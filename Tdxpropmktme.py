import os
import re
import sys
import json
import time
import math
import hashlib
import argparse
import unicodedata
import warnings
from typing import List, Dict, Tuple, Optional
warnings.filterwarnings("ignore")


CHUNK_MIN_TOKENS     = 600
CHUNK_MAX_TOKENS     = 1200
CHUNK_OVERLAP_PCT    = 0.20
MIN_MEANINGFUL_WORDS = 30

VECTORSTORE_DIR      = "./vectorstore"
METADATA_FILE        = os.path.join(VECTORSTORE_DIR, "index_metadata.json")
CHROMA_COLLECTION    = "intel_tdx"
CHUNKING_VERSION     = "para"

RERANKER_TOP_N  = 15

EMBED_MODEL  = "text-embedding-3-large"
EMBED_DIMS   = 3072
EMBED_BATCH  = 64

OPENAI_MODEL  = "gpt-5.5"
MAX_TOKENS    = 16000
CONTEXT_CHARS = 25000

PRICING = {
    "embedding_per_1m_tokens": 0.13,
    "llm_input_per_1m_tokens": 2.50,
    "llm_output_per_1m_tokens": 10.00,
}

USER_ASSERTIONS = """Confidentiality Properties
ID\tProperty Description
cP1\tGPA to HPA mappings in EPT must remain confidential (no aliasing)
cP2\tHKID encryption keys in KET must not be leaked
cP3\tHKID assignment state in KOT must remain confidential
cP4\tTDR lifecycle state must remain confidential
cP5\tPage states in secure EPT must remain confidential
cP6\tKey configuration state of HKID must be confidential
cP7\tFinalization status of TDCS must remain confidential
cP8\tShared bit status in secure EPT entries must be confidential
cP9\tPackage configuration bitmap in TDR must remain confidential
cP10\tVCPU to HKID association must remain confidential
cP11\tIncorrect HKID must result in cache miss
cP12\tCorrect HKID must result in cache hit
cP13\tUnauthorized HKID should not access populated cache line
cP14\tCache access should be exclusive to the latest HKID
cP15\tCache data must remain unchanged unless explicitly modified
Integrity Properties
ID\tProperty Description
iP1\tGPA-to-HPA mappings must never be in 'blocked' state
iP2\tFinalized TDR cannot revert to INIT or FATAL state
iP3\tHKID state transitions must follow valid lifecycle (Assigned -> Configured -> Blocked -> Teardown)
iP4\tValid cache entries must include correct tag and data
iP5\tAll valid entries in the same cache set must have unique tags
iP6\tValid cache entries must map HKID to correct set and way
iP7\tValid cache entries must include correct TD owner bit
iP8\tDifferent cache ways in the same set must have different tags
iP9\tCache entries with the same tag must have the same TD owner bit"""

RETRIEVAL_QUERIES = [
    "security vulnerabilities in this module",
    "missing verification properties",
    "attack scenarios and threats",
    "correctness and consistency checks",
    "edge cases and race conditions",
]

DOMAINS = {
    "keyid_isolation":           ["KeyID", "HKID", "key isolation", "per-TD", "cross-TD", "KeyID assignment"],
    "key_lifecycle":             ["key lifecycle", "revocation", "reuse", "creation", "key derivation", "KET", "KOT"],
    "memory_encryption_engine":  ["MEE", "encryption engine", "TME", "MKTME", "encrypted memory", "cipher"],
    "memory_remapping_aliasing": ["remapping", "aliasing", "GPA", "HPA", "alias", "cross-TD access", "mapping attack"],
    "dma_io_isolation":          ["DMA", "IOMMU", "device", "I/O", "external access", "bus master"],
    "replay_rollback":           ["replay", "rollback", "counter", "integrity tree", "MAC", "page MAC", "monotonic"],
    "metadata_integrity":        ["integrity tree", "metadata", "MAC tag", "page integrity", "cryptographic", "verification"],
    "side_channel":              ["side channel", "access pattern", "covert channel", "leakage", "timing", "correlation"],
    "bios_firmware_config":      ["BIOS", "firmware", "misconfiguration", "TME activation", "key programming", "MSR"],
    "fault_injection":           ["fault injection", "partial write", "corruption", "encrypted page", "glitch", "atomic"],
}

TECH_MARKERS = {
    "keyid_isolation":           ["TDH.MNG.KEY.CONFIG", "PCONFIG", "MKTME_KEYID_PARTITIONING",
                                    "TDX private KeyID range", "KeyID bit field", "shared KeyID range"],
    "key_lifecycle":             ["TDH.MNG.KEY.CREATE", "TDH.MNG.KEY.RECLAIMID", "TDH.MNG.KEY.FREEID",
                                    "KOT entry state", "KET key table entry", "WBINVD"],
    "memory_encryption_engine":  ["MK-TME", "AES-XTS-256", "MEE cache line", "IA32_TME_ACTIVATE",
                                    "TME-MK mode", "physical address space ID"],
    "memory_remapping_aliasing": ["GPA aliasing", "shared HPA mapping", "PAMT owner mismatch",
                                    "TDH.MEM.SEPT.ADD", "cross-TD physical alias"],
    "dma_io_isolation":          ["IOMMU", "VT-d remapping", "DMA remapping engine", "device TLB",
                                    "bus-master DMA", "PCIe TLP"],
    "replay_rollback":           ["integrity counter", "MAC tree root", "monotonic counter",
                                    "replay-protected memory", "counter rollback"],
    "metadata_integrity":        ["page MAC", "integrity tree node", "SHA-256 MAC", "Merkle-style tree",
                                    "metadata corruption"],
    "side_channel":              ["cache timing channel", "prefetch access pattern", "memory access trace",
                                    "power side channel", "microarchitectural leakage"],
    "bios_firmware_config":      ["IA32_TME_ACTIVATE MSR", "BIOS TME enable bit", "SEAMLDR",
                                    "ACM measurement", "platform key programming"],
    "fault_injection":           ["voltage glitch", "row hammer", "bit flip injection",
                                    "partial write corruption", "ECC error injection"],
}


def compute_technical_specificity(text: str) -> Tuple[Dict, int]:
    text_lower = text.lower()
    hits: Dict[str, List[str]] = {}
    total = 0
    for domain, markers in TECH_MARKERS.items():
        found = [m for m in markers if m.lower() in text_lower]
        hits[domain] = found
        total += len(found)
    return hits, total


def _check_imports():
    missing = []
    for pkg, pip_name in [
        ("fitz",                "pymupdf"),
        ("chromadb",            "chromadb"),
        ("langchain_chroma",    "langchain-chroma"),
        ("langchain_openai",    "langchain-openai"),
        ("langchain_core",      "langchain"),
        ("openai",              "openai"),
        ("numpy",               "numpy"),
    ]:
        try:
            __import__(pkg)
        except ImportError:
            missing.append(pip_name)
    if missing:
        print(f"  Missing packages: {', '.join(missing)}")
        print(f"  Run: pip install {' '.join(missing)}")
        sys.exit(1)


try:
    import tiktoken
    _TOKENIZER   = tiktoken.get_encoding("cl100k_base")
    _TIKTOKEN_OK = True

    def _count_tokens(text: str) -> int:
        return len(_TOKENIZER.encode(text, disallowed_special=()))

    def _encode(text: str) -> list:
        return _TOKENIZER.encode(text, disallowed_special=())

    def _decode(tokens: list) -> str:
        return _TOKENIZER.decode(tokens)

except ImportError:
    _TIKTOKEN_OK = False

    def _count_tokens(text: str) -> int:
        return int(len(text.split()) * 1.3)

    def _encode(text: str) -> list:
        return text.split()

    def _decode(tokens: list) -> str:
        return " ".join(str(t) for t in tokens)


def clean_text(raw: str) -> str:
    raw = unicodedata.normalize("NFKC", raw)
    lines = raw.splitlines()
    filtered = []
    for line in lines:
        line = line.strip()
        if re.match(r"^Page\s+\d+(\s+of\s+\d+)?$", line):
            continue
        if re.match(r"^Intel.*Specification", line):
            continue
        if re.match(r"^[\-\.=]{5,}$", line):
            continue
        filtered.append(line)
    raw = "\n".join(filtered)
    raw = re.sub(r"\d{6}-\d{3}[A-Z]{2}", "", raw)
    raw = re.sub(r"\n{3,}", "\n\n", raw)
    raw = re.sub(r"[ \t]{2,}", " ", raw)
    raw = raw.replace("\x0c", "\n")
    return raw.strip()


def extract_pdf_text(pdf_path: str) -> str:
    import fitz
    doc = fitz.open(pdf_path)
    pages_text = []
    for page_num, page in enumerate(doc):
        try:
            blocks = page.get_text("blocks")
            blocks = sorted(blocks, key=lambda b: (b[1], b[0]))
            text = "\n".join(block[4].strip() for block in blocks if block[4].strip())
            if len(text.strip()) > 50:
                pages_text.append(f"\n===== PAGE {page_num+1} | {os.path.basename(pdf_path)} =====\n{text}")
        except Exception as e:
            print(f"    Error on page {page_num+1}: {e}")
    doc.close()
    return clean_text("\n\n".join(pages_text))


def load_pdfs(pdf_paths: List[str]) -> List[Dict]:
    documents = []
    for pdf_path in pdf_paths:
        fname = os.path.basename(pdf_path)
        print(f"  Extracting: {fname} ...", end="", flush=True)
        try:
            text = extract_pdf_text(pdf_path)
            if len(text.strip()) < 100:
                print("  Too little text — skipped.")
                continue
            documents.append({"source": fname, "text": text})
            print(f"  ({len(text):,} chars)")
        except Exception as e:
            print(f"  Error: {e}")
    return documents


PARAGRAPH_MIN_TOKENS = CHUNK_MIN_TOKENS
PARAGRAPH_MAX_TOKENS = CHUNK_MAX_TOKENS
PARAGRAPH_OVERLAP = 1


def split_paragraphs(text: str) -> List[str]:
    return [p.strip() for p in re.split(r"\n{2,}", text) if len(p.strip()) > 50]


def paragraph_based_chunking(text: str, source: str) -> List[Dict]:
    paragraphs = split_paragraphs(text)

    chunks = []
    buffer: List[str] = []
    buffer_tokens = 0
    counter = 0

    for para in paragraphs:
        para_tokens = _count_tokens(para)

        if para_tokens > PARAGRAPH_MAX_TOKENS:
            if buffer:
                chunks.append({
                    "text": "\n\n".join(buffer),
                    "source": source,
                    "chunk_id": f"{source}_{counter}",
                    "section": "paragraph",
                    "page": "",
                    "tokens": buffer_tokens,
                })
                counter += 1
                buffer, buffer_tokens = [], 0

            chunks.append({
                "text": para,
                "source": source,
                "chunk_id": f"{source}_{counter}",
                "section": "large_paragraph",
                "page": "",
                "tokens": para_tokens,
            })
            counter += 1
            continue

        if buffer_tokens + para_tokens <= PARAGRAPH_MAX_TOKENS:
            buffer.append(para)
            buffer_tokens += para_tokens
        else:
            if buffer_tokens >= PARAGRAPH_MIN_TOKENS:
                chunks.append({
                    "text": "\n\n".join(buffer),
                    "source": source,
                    "chunk_id": f"{source}_{counter}",
                    "section": "paragraph",
                    "page": "",
                    "tokens": buffer_tokens,
                })
                counter += 1

                if PARAGRAPH_OVERLAP:
                    buffer = buffer[-PARAGRAPH_OVERLAP:]
                    buffer_tokens = sum(_count_tokens(x) for x in buffer)
                else:
                    buffer, buffer_tokens = [], 0

            buffer.append(para)
            buffer_tokens += para_tokens

    if buffer:
        chunks.append({
            "text": "\n\n".join(buffer),
            "source": source,
            "chunk_id": f"{source}_{counter}",
            "section": "paragraph",
            "page": "",
            "tokens": buffer_tokens,
        })

    return chunks


def chunk_all_documents(documents: List[Dict]) -> List[Dict]:
    print(f"  Tokenizer     : {'tiktoken cl100k_base' if _TIKTOKEN_OK else 'word-count fallback'}")
    all_chunks = []
    for doc in documents:
        chunks = paragraph_based_chunking(doc["text"], source=doc["source"])
        all_chunks.extend(chunks)
        print(f"  {doc['source']}: {len(chunks)} paragraph chunks")
    print(f"  Total chunks  : {len(all_chunks)}")
    return all_chunks


def _compute_pdf_hash(pdf_paths: List[str]) -> str:
    h = hashlib.md5()
    for path in sorted(pdf_paths):
        h.update(path.encode())
        with open(path, "rb") as fh:
            for chunk in iter(lambda: fh.read(65536), b""):
                h.update(chunk)
    return h.hexdigest()


def _build_cache_key(pdf_paths: List[str]) -> Dict:
    return {"pdf_hash": _compute_pdf_hash(pdf_paths), "embedding_model": EMBED_MODEL, "chunking_version": CHUNKING_VERSION}


def _load_cached_metadata() -> Optional[Dict]:
    if not os.path.isfile(METADATA_FILE):
        return None
    try:
        with open(METADATA_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return None


def _save_metadata(meta: Dict):
    os.makedirs(VECTORSTORE_DIR, exist_ok=True)
    with open(METADATA_FILE, "w", encoding="utf-8") as f:
        json.dump(meta, f, indent=2)


def check_cache_valid(pdf_paths: List[str]) -> bool:
    expected = _build_cache_key(pdf_paths)
    cached = _load_cached_metadata()
    if cached and cached == expected:
        if os.path.isdir(VECTORSTORE_DIR) and any(f for f in os.listdir(VECTORSTORE_DIR) if f != "index_metadata.json"):
            print("  [cache] metadata matched — loading existing vectorstore")
            return True
    print("  [cache] rebuilding vectorstore" if cached else "  [cache] no cache found — building for the first time")
    return False


def _chunks_to_langchain_docs(chunks: List[Dict]):
    from langchain_core.documents import Document
    return [Document(
        page_content=c["text"],
        metadata={k: c.get(k, "") for k in ("chunk_id", "source", "section", "section_id", "section_title", "page", "tokens")},
    ) for c in chunks]


def build_vectorstore(chunks: List[Dict], openai_api_key: str):
    from langchain_chroma import Chroma
    from langchain_openai import OpenAIEmbeddings
    embedding_fn = OpenAIEmbeddings(model=EMBED_MODEL, openai_api_key=openai_api_key, dimensions=EMBED_DIMS)
    docs = _chunks_to_langchain_docs(chunks)
    total = len(docs)
    print(f"  Embedding {total} chunks via {EMBED_MODEL} ...")
    vectorstore = None
    for i in range(0, total, EMBED_BATCH):
        batch = docs[i:i + EMBED_BATCH]
        if vectorstore is None:
            vectorstore = Chroma.from_documents(documents=batch, embedding=embedding_fn,
                                                 collection_name=CHROMA_COLLECTION, persist_directory=VECTORSTORE_DIR)
        else:
            vectorstore.add_documents(batch)
    print(f"  Chroma vectorstore built — {total} vectors persisted to {VECTORSTORE_DIR}")
    return vectorstore


def load_vectorstore(openai_api_key: str):
    from langchain_chroma import Chroma
    from langchain_openai import OpenAIEmbeddings
    embedding_fn = OpenAIEmbeddings(model=EMBED_MODEL, openai_api_key=openai_api_key, dimensions=EMBED_DIMS)
    vectorstore = Chroma(collection_name=CHROMA_COLLECTION, embedding_function=embedding_fn, persist_directory=VECTORSTORE_DIR)
    print(f"  Loaded existing Chroma vectorstore — {vectorstore._collection.count()} vectors")
    return vectorstore


def _doc_to_chunk_dict(doc) -> Dict:
    md = doc.metadata
    return {
        "text": doc.page_content,
        "chunk_id": md.get("chunk_id", doc.page_content[:64]),
        "source": md.get("source", ""),
        "section": md.get("section", ""),
        "section_id": md.get("section_id", ""),
        "section_title": md.get("section_title", ""),
        "page": md.get("page", ""),
        "tokens": md.get("tokens", 0),
    }


def retrieve_chunks(vectorstore, top_n: int = RERANKER_TOP_N) -> List[Dict]:
    retriever = vectorstore.as_retriever(search_type="similarity", search_kwargs={"k": top_n})
    seen, pooled = set(), []
    for q in RETRIEVAL_QUERIES:
        for d in retriever.invoke(q):
            cd = _doc_to_chunk_dict(d)
            if cd["chunk_id"] not in seen:
                seen.add(cd["chunk_id"])
                pooled.append(cd)
    return pooled[:top_n]


def _jaccard_similarity(a: str, b: str) -> float:
    sa, sb = set(a.lower().split()), set(b.lower().split())
    if not sa or not sb:
        return 0.0
    return len(sa & sb) / len(sa | sb)


def compute_redundancy_rate(chunks: List[Dict], threshold: float = 0.5) -> float:
    n = len(chunks)
    if n < 2:
        return 0.0
    dup_pairs, total_pairs = 0, 0
    for i in range(n):
        for j in range(i + 1, n):
            total_pairs += 1
            if _jaccard_similarity(chunks[i]["text"], chunks[j]["text"]) >= threshold:
                dup_pairs += 1
    return dup_pairs / total_pairs if total_pairs else 0.0


def compute_retrieved_domain_diversity(chunks: List[Dict]) -> Tuple[Dict, float]:
    combined_text = " ".join(c["text"] for c in chunks).lower()
    coverage = {}
    for domain, keywords in DOMAINS.items():
        coverage[domain] = 1 if any(re.search(r"\b" + re.escape(kw.lower()) + r"\b", combined_text) for kw in keywords) else 0
    score = sum(coverage.values()) / len(coverage)
    return coverage, score


def compute_coverage(text: str) -> Tuple[Dict, Dict, float]:
    text_lower = text.lower()
    coverage_map, evidence_map = {}, {}
    for domain, keywords in DOMAINS.items():
        hits = [kw for kw in keywords if re.search(r"\b" + re.escape(kw.lower()) + r"\b", text_lower)]
        coverage_map[domain] = 1 if hits else 0
        evidence_map[domain] = hits
    score = sum(coverage_map.values()) / len(coverage_map)
    return coverage_map, evidence_map, score


def print_coverage(text: str):
    coverage_map, evidence_map, score = compute_coverage(text)
    print("\n" + "=" * 70)
    print("  TDX SEPT + PAMT COVERAGE REPORT")
    print("=" * 70)
    for domain, covered in coverage_map.items():
        status = "COVERED" if covered else "MISSING"
        print(f"  {domain:25s} : {status}")
    total_covered = sum(coverage_map.values())
    print(f"\n  OVERALL COVERAGE SCORE: {score:.2f}  ({total_covered}/{len(coverage_map)} domains)")


def estimate_cost(embed_calls: int, embed_tokens: int, llm_input_tokens: int, llm_output_tokens: int) -> Dict:
    embed_cost = (embed_tokens / 1_000_000) * PRICING["embedding_per_1m_tokens"]
    llm_in_cost = (llm_input_tokens / 1_000_000) * PRICING["llm_input_per_1m_tokens"]
    llm_out_cost = (llm_output_tokens / 1_000_000) * PRICING["llm_output_per_1m_tokens"]
    return {
        "embedding_calls": embed_calls,
        "embedding_tokens_est": embed_tokens,
        "embedding_cost_usd_est": round(embed_cost, 6),
        "llm_input_tokens": llm_input_tokens,
        "llm_output_tokens": llm_output_tokens,
        "llm_cost_usd_est": round(llm_in_cost + llm_out_cost, 6),
        "total_cost_usd_est": round(embed_cost + llm_in_cost + llm_out_cost, 6),
        "pricing_used": PRICING,
        "note": "Rough estimate only — verify against your actual billing dashboard.",
    }


_PROPERTY_SPLIT_RE = re.compile(r"(?=^\**Property Name\**\s*:)", re.MULTILINE | re.IGNORECASE)
_HEADING_SPLIT_RE = re.compile(r"(?=^#{1,3}\s+(?:Property\s+\d+|\d+\.))", re.MULTILINE | re.IGNORECASE)
_STOPWORDS = {
    "the", "a", "an", "of", "to", "and", "or", "in", "on", "is", "are", "be",
    "must", "should", "this", "that", "for", "with", "as", "by", "it", "its",
    "not", "no", "if", "when", "which", "can", "will", "may", "any", "at",
}


def parse_properties(text: str) -> List[str]:
    blocks = [b.strip() for b in _PROPERTY_SPLIT_RE.split(text) if b.strip()]
    if len(blocks) <= 1:
        blocks = [b.strip() for b in _HEADING_SPLIT_RE.split(text) if b.strip()]
    if len(blocks) <= 1:
        blocks = [b.strip() for b in re.split(r"(?=^##\s+)", text, flags=re.MULTILINE) if b.strip()]
    return blocks if blocks else ([text.strip()] if text.strip() else [])


def _content_words(text: str) -> set:
    words = re.findall(r"[a-zA-Z][a-zA-Z\-]{2,}", text.lower())
    return {w for w in words if w not in _STOPWORDS}


def _parse_existing_assertions(assertions_block: str) -> List[str]:
    descriptions = []
    for line in assertions_block.splitlines():
        if "\t" in line:
            parts = line.split("\t")
            if len(parts) == 2 and not parts[0].strip().lower().startswith("id"):
                descriptions.append(parts[1].strip())
    return descriptions


def compute_novelty_score(properties: List[str], assertions_block: str) -> Dict:
    existing = _parse_existing_assertions(assertions_block)
    existing_word_sets = [_content_words(e) for e in existing]

    per_property_max_sim = []
    flagged_duplicates = []
    for prop in properties:
        prop_words = _content_words(prop)
        if not prop_words or not existing_word_sets:
            per_property_max_sim.append(0.0)
            continue
        sims = []
        for ex_words in existing_word_sets:
            if not ex_words:
                continue
            inter = len(prop_words & ex_words)
            union = len(prop_words | ex_words)
            sims.append(inter / union if union else 0.0)
        max_sim = max(sims) if sims else 0.0
        per_property_max_sim.append(max_sim)
        if max_sim >= 0.35:
            name_match = re.search(r"Property Name\s*:\s*(.+)", prop, re.IGNORECASE)
            flagged_duplicates.append({
                "property": (name_match.group(1).strip() if name_match else prop[:60]),
                "max_similarity_to_existing": round(max_sim, 3),
            })

    avg_sim = sum(per_property_max_sim) / len(per_property_max_sim) if per_property_max_sim else 0.0
    return {
        "num_properties": len(properties),
        "avg_max_similarity_to_existing": round(avg_sim, 4),
        "flagged_possible_duplicates": flagged_duplicates,
    }


def compute_faithfulness_score(properties: List[str], retrieved_chunks: List[Dict]) -> Dict:
    context_words = set()
    for c in retrieved_chunks:
        context_words |= _content_words(c["text"])

    per_property_scores = []
    for prop in properties:
        prop_words = _content_words(prop)
        if not prop_words:
            per_property_scores.append(0.0)
            continue
        grounded = len(prop_words & context_words)
        per_property_scores.append(grounded / len(prop_words))

    avg_score = sum(per_property_scores) / len(per_property_scores) if per_property_scores else 0.0
    return {
        "num_properties": len(properties),
        "avg_faithfulness_proxy": round(avg_score, 4),
        "per_property_scores": [round(s, 3) for s in per_property_scores],
    }


def compute_factual_correctness_ragas(response: str, reference: str) -> Dict:
    try:
        import asyncio
        from openai import AsyncOpenAI
        from ragas.llms import llm_factory
        from ragas.metrics.collections import FactualCorrectness
    except ImportError:
        return {
            "available": False,
            "error": "ragas not installed — run: pip install ragas",
        }

    reference_capped = reference[:CONTEXT_CHARS]

    async def _score() -> float:
        client = AsyncOpenAI(api_key=os.environ.get("OPENAI_API_KEY", ""))
        llm = llm_factory("gpt-4o-mini", client=client)
        scorer = FactualCorrectness(llm=llm)
        result = await scorer.ascore(response=response, reference=reference_capped)
        return float(result.value)

    try:
        score = asyncio.run(_score())
    except Exception as e:
        return {"available": False, "error": str(e)}

    return {
        "available": True,
        "score": round(score, 4),
        "judge_model": "gpt-4o-mini",
        "reference_source": "retrieved_context (chunks actually fed to the LLM)",
    }


def compute_domain_coverage_strict(properties: List[str]) -> Tuple[Dict, float]:
    coverage = {d: 0 for d in DOMAINS}
    for prop in properties:
        prop_lower = prop.lower()
        for domain in DOMAINS:
            if coverage[domain]:
                continue
            kw_hits = sum(1 for kw in DOMAINS[domain] if kw.lower() in prop_lower)
            tech_hits = sum(1 for tm in TECH_MARKERS.get(domain, []) if tm.lower() in prop_lower)
            if kw_hits >= 2 and tech_hits >= 1:
                coverage[domain] = 1
    score = sum(coverage.values()) / len(coverage)
    return coverage, score


def build_context_block(chunks: List[Dict], max_chars: int = CONTEXT_CHARS) -> str:
    context, total = [], 0
    for i, chunk in enumerate(chunks):
        piece = f"[SOURCE {i+1}] {chunk['source']} | {chunk.get('section', 'NA')} | page {chunk.get('page', 'NA')}\n{chunk['text']}"
        if total + len(piece) <= max_chars:
            context.append(piece)
            total += len(piece)
        else:
            break
    return "\n\n".join(context)


def build_prompt(assertions: str, context: str) -> str:
    return f"""You are a hardware security verification expert with deep expertise in Intel TDX (Trusted Domain Extensions), MKTME (Multi-Key Total Memory Encryption), and assertion-based verification (SystemVerilog Assertions).

Your task is to generate high-value missing MKTME verification properties that are NOT already covered by the existing assertions below.

Focus exclusively on:
- KeyID isolation across TDs
- Key lifecycle (creation, revocation, reuse attacks)
- Memory remapping and aliasing attacks
- DMA and I/O interaction with encrypted memory
- Replay / rollback protection on encrypted pages
- Metadata integrity (integrity trees, page MAC tags)
- Side-channel leakage via access patterns
- BIOS/firmware misconfiguration risks
- Fault injection and partial write on encrypted memory

For each missing property, provide:

Property Name:
Definition:
- Explain clearly in English (simple but technically deep)
Purpose:
- Why this verification is needed in TDX + MKTME
Security Impact:
- What attack or failure can happen if missing
Reference:
- Intel TDX Module Specification / Intel SDM / Intel MKTME documentation
- Mention topic (exact section number not required)

Output Style:
- English only
- Structured with headings and bullet points
- Do NOT repeat anything already covered in existing assertions
- Think like a CPU security auditor reviewing RTL
- Do NOT give generic textbook answers
- Focus on real hardware-level vulnerabilities — practical and testable

EXISTING ASSERTIONS (already verified — do NOT repeat these):
{assertions}

TDX + MKTME SPEC CONTEXT (retrieved from Intel documentation):
{context}

OUTPUT:
Generate high-value missing TDX + MKTME verification properties:
"""


def _uses_max_completion_tokens(model_name: str) -> bool:
    return model_name.lower().startswith(("o1", "o3", "gpt-5", "chatgpt-4o-latest"))


def _no_custom_temperature(model_name: str) -> bool:
    return model_name.lower().startswith(("o1", "o3", "gpt-5"))


def _is_reasoning_model(model_name: str) -> bool:
    return model_name.lower().startswith(("o1", "o3", "gpt-5"))


def call_openai(prompt: str, client) -> Tuple[str, Dict]:
    use_new_param = _uses_max_completion_tokens(OPENAI_MODEL)
    skip_temp = _no_custom_temperature(OPENAI_MODEL)
    is_reasoning = _is_reasoning_model(OPENAI_MODEL)

    if is_reasoning:
        messages = [{"role": "user", "content": "You are a strict formal verification and Intel TDX security expert.\n\n" + prompt}]
    else:
        messages = [
            {"role": "system", "content": "You are a strict formal verification and Intel TDX security expert."},
            {"role": "user", "content": prompt},
        ]

    kwargs: Dict = dict(model=OPENAI_MODEL, messages=messages)
    if use_new_param:
        kwargs["max_completion_tokens"] = MAX_TOKENS
    else:
        kwargs["max_tokens"] = MAX_TOKENS
    if not skip_temp:
        kwargs["temperature"] = 0.2

    try:
        response = client.chat.completions.create(**kwargs)
    except Exception as e:
        err_str = str(e)
        if "temperature" in err_str:
            kwargs.pop("temperature", None)
            response = client.chat.completions.create(**kwargs)
        elif use_new_param and "max_completion_tokens" in err_str:
            kwargs.pop("max_completion_tokens")
            kwargs["max_tokens"] = MAX_TOKENS
            response = client.chat.completions.create(**kwargs)
        elif not use_new_param and "max_tokens" in err_str:
            kwargs.pop("max_tokens")
            kwargs["max_completion_tokens"] = MAX_TOKENS
            response = client.chat.completions.create(**kwargs)
        else:
            raise

    choice = response.choices[0]
    finish = getattr(choice, "finish_reason", "unknown")
    raw_content = choice.message.content

    usage = getattr(response, "usage", None)
    usage_dict = {"input_tokens": 0, "output_tokens": 0, "finish_reason": finish}
    if usage:
        usage_dict["input_tokens"] = getattr(usage, "prompt_tokens", 0)
        usage_dict["output_tokens"] = getattr(usage, "completion_tokens", 0)

    if not raw_content:
        raise RuntimeError(f"Empty response from {OPENAI_MODEL} (finish_reason={finish}).")
    return raw_content, usage_dict


def run_pipeline(vectorstore, client, output_dir: str = ".") -> Dict:
    print(f"\n{'='*70}\n  EXPERIMENT 2: rag_mqa\n{'='*70}")

    metrics: Dict = {"experiment": 2, "name": "rag_mqa"}

    t0 = time.perf_counter()
    chunks = retrieve_chunks(vectorstore, top_n=RERANKER_TOP_N)
    t1 = time.perf_counter()
    metrics["retrieval_latency_sec"] = round(t1 - t0, 3)
    metrics["num_retrieval_queries"] = len(RETRIEVAL_QUERIES)
    metrics["final_context_chunk_count"] = len(chunks)

    metrics["redundancy_rate"] = round(compute_redundancy_rate(chunks), 4)
    domain_cov, domain_score = compute_retrieved_domain_diversity(chunks)
    metrics["retrieved_domain_coverage"] = domain_cov
    metrics["retrieved_domain_diversity_score"] = round(domain_score, 4)
    metrics["avg_chunk_tokens"] = round(sum(c.get("tokens", 0) for c in chunks) / max(1, len(chunks)), 1)

    retrieval_log = [{
        "chunk_id": c["chunk_id"], "source": c["source"], "section": c.get("section", ""),
        "page": c.get("page", ""), "rerank_score": c.get("rerank_score"),
        "text_preview": c["text"][:200],
    } for c in chunks]
    with open(os.path.join(output_dir, "retrieved_chunks_exp2.json"), "w", encoding="utf-8") as f:
        json.dump(retrieval_log, f, indent=2)

    context_text = build_context_block(chunks)
    prompt = build_prompt(USER_ASSERTIONS, context_text)
    metrics["prompt_chars"] = len(prompt)

    t2 = time.perf_counter()
    result, usage = call_openai(prompt, client)
    t3 = time.perf_counter()
    metrics["llm_latency_sec"] = round(t3 - t2, 3)
    metrics["end_to_end_latency_sec"] = round(t3 - t0, 3)
    metrics["llm_usage"] = usage

    out_coverage, out_evidence, out_score = compute_coverage(result)
    metrics["output_domain_coverage"] = out_coverage
    metrics["output_coverage_score"] = round(out_score, 4)

    properties = parse_properties(result)
    metrics["property_count"] = len(properties)
    metrics["avg_property_word_count"] = round(
        sum(len(p.split()) for p in properties) / max(1, len(properties)), 1
    )

    tech_hits, tech_total = compute_technical_specificity(result)
    metrics["technical_specificity_hits"] = tech_hits
    metrics["technical_specificity_total"] = tech_total

    strict_coverage, strict_score = compute_domain_coverage_strict(properties)
    metrics["output_domain_coverage_strict"] = strict_coverage
    metrics["output_coverage_score_strict"] = round(strict_score, 4)

    novelty = compute_novelty_score(properties, USER_ASSERTIONS)
    metrics["novelty"] = novelty

    faithfulness = compute_faithfulness_score(properties, chunks)
    metrics["faithfulness"] = faithfulness

    factual_correctness = compute_factual_correctness_ragas(
        response=result, reference=context_text
    )
    metrics["factual_correctness"] = factual_correctness

    embed_tokens_est = sum(c.get("tokens", 0) for c in chunks)
    embed_calls_est = metrics["num_retrieval_queries"]
    metrics["cost_estimate"] = estimate_cost(
        embed_calls=embed_calls_est,
        embed_tokens=int(embed_tokens_est),
        llm_input_tokens=usage.get("input_tokens", 0),
        llm_output_tokens=usage.get("output_tokens", 0),
    )

    out_path = os.path.join(output_dir, "missing_sept_pamt_properties1_exp2.txt")
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(result)
    metrics["output_file"] = out_path

    metrics_path = os.path.join(output_dir, "ablation1_metrics_exp2.json")
    with open(metrics_path, "w", encoding="utf-8") as f:
        json.dump(metrics, f, indent=2)

    print_coverage(result)
    print("\n  --- NEW non-saturated quality metrics ---")
    print(f"  Property count             : {metrics['property_count']}")
    print(f"  Avg property length (words): {metrics['avg_property_word_count']}")
    print(f"  Technical specificity hits : {metrics['technical_specificity_total']}  (higher = more genuine spec detail)")
    print(f"  STRICT coverage score      : {metrics['output_coverage_score_strict']}  (replaces the saturated 1.00 metric)")
    print(f"  Novelty (lower=better)     : {novelty['avg_max_similarity_to_existing']}  ({len(novelty['flagged_possible_duplicates'])} possible duplicates of existing assertions)")
    print(f"  Faithfulness (higher=better): {faithfulness['avg_faithfulness_proxy']}")
    if factual_correctness.get("available"):
        print(f"  Factual correctness (RAGAS, higher=better): {factual_correctness['score']}")
    else:
        print(f"  Factual correctness (RAGAS): unavailable ({factual_correctness.get('error')})")
    print(f"\n  Retrieval latency : {metrics['retrieval_latency_sec']}s")
    print(f"  LLM latency       : {metrics['llm_latency_sec']}s")
    print(f"  Redundancy rate   : {metrics['redundancy_rate']}")
    print(f"  Retrieved-domain diversity : {metrics['retrieved_domain_diversity_score']}")
    print(f"  Est. cost (USD)   : {metrics['cost_estimate']['total_cost_usd_est']}")
    print(f"  Saved: {out_path}")
    print(f"  Saved: {metrics_path}")

    return metrics


def parse_args():
    parser = argparse.ArgumentParser(description="Intel TDX RAG — Experiment 2 (MQA)")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--pdf", nargs="+", metavar="FILE")
    group.add_argument("--pdf_dir", metavar="DIR")
    parser.add_argument("--model", default=OPENAI_MODEL)
    parser.add_argument("--dims", type=int, default=EMBED_DIMS)
    parser.add_argument("--output_dir", default=".")
    parser.add_argument("--force_rebuild", action="store_true")
    return parser.parse_args()


def collect_pdf_paths(args) -> List[str]:
    if args.pdf:
        paths = args.pdf
    else:
        d = args.pdf_dir
        if not os.path.isdir(d):
            print(f"  Not a directory: {d}")
            sys.exit(1)
        paths = [os.path.join(d, f) for f in os.listdir(d) if f.lower().endswith(".pdf")]
        if not paths:
            print(f"  No PDFs found in: {d}")
            sys.exit(1)
    for p in paths:
        if not os.path.isfile(p):
            print(f"  File not found: {p}")
            sys.exit(1)
    return paths


def get_or_build_vectorstore(pdf_paths: List[str], api_key: str, force_rebuild: bool = False):
    cache_valid = (not force_rebuild) and check_cache_valid(pdf_paths)
    if cache_valid:
        return load_vectorstore(api_key)
    documents = load_pdfs(pdf_paths)
    if not documents:
        print("  No usable text extracted. Exiting.")
        sys.exit(1)
    all_chunks = chunk_all_documents(documents)
    if os.path.isdir(VECTORSTORE_DIR):
        import shutil
        shutil.rmtree(VECTORSTORE_DIR)
    vectorstore = build_vectorstore(all_chunks, api_key)
    _save_metadata(_build_cache_key(pdf_paths))
    return vectorstore


def main():
    _check_imports()
    args = parse_args()

    global OPENAI_MODEL, EMBED_DIMS
    OPENAI_MODEL = args.model
    EMBED_DIMS = args.dims

    api_key = os.environ.get("OPENAI_API_KEY", "")
    if not api_key:
        print("  OPENAI_API_KEY not set.")
        sys.exit(1)

    from openai import OpenAI
    client = OpenAI(api_key=api_key)

    pdf_paths = collect_pdf_paths(args)
    vectorstore = get_or_build_vectorstore(pdf_paths, api_key, args.force_rebuild)

    os.makedirs(args.output_dir, exist_ok=True)
    run_pipeline(vectorstore, client, output_dir=args.output_dir)


if __name__ == "__main__":
    main()