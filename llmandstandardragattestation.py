"""
Intel TDX RAG Pipeline — SEPT + PAMT Security Audit — EXPERIMENT 1 ONLY (Standard RAG)
======================================================================================
This script isolates and runs strictly Experiment 1 (Standard RAG).
All other ablation configurations (MQA, MMR, Reranking) have been removed.

Features:
  - Single query retrieval (similarity-based)
  - Configurable top-N context size (defaults to 15)
  - Code-native metrics calculation (Latency, Redundancy, Technical Specificity, Strict Coverage, Novelty, Faithfulness, Cost)
  - Saves LLM generated properties, retrieved chunk details, and JSON metrics

Usage:
    python tdx_rag_exp1.py --pdf_dir ./specs
"""

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

# =============================================================================
# CONFIG
# =============================================================================

CHUNK_MIN_TOKENS     = 600
CHUNK_MAX_TOKENS     = 1200
CHUNK_OVERLAP_PCT    = 0.20
MIN_MEANINGFUL_WORDS = 30

VECTORSTORE_DIR      = "./vectorstore"
METADATA_FILE        = os.path.join(VECTORSTORE_DIR, "index_metadata.json")
CHROMA_COLLECTION    = "intel_tdx"
CHUNKING_VERSION     = "v2para"

RERANKER_TOP_N  = 15             # FIXED final context size

EMBED_MODEL  = "text-embedding-3-large"
EMBED_DIMS   = 3072
EMBED_BATCH  = 64

OPENAI_MODEL  = "gpt-5.5"
MAX_TOKENS    = 16000
CONTEXT_CHARS = 25000

# --- Factual correctness / semantic alignment controls -----------------
FAITHFULNESS_MIN_THRESHOLD   = 0.30   # below this per-property faithfulness -> flagged LOW-CONFIDENCE
REQUIRE_SOURCE_CITATIONS     = True   # prompt requires [SOURCE N] citations per property

# Rough public list-price estimates for cost reporting only (USD / 1M tokens).
PRICING = {
    "embedding_per_1m_tokens": 0.13,   # text-embedding-3-large list price ballpark
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
"""
# Single top-level user query (Experiment 1 baseline: no query expansion)
USER_QUERY = "Extract missing security verification properties related to SEPT and PAMT in Intel TDX"
DOMAINS = {
    "sept_state_machine":       ["SEPT", "PENDING", "BLOCKED", "PRESENT", "state machine", "entry state"],
    "gpa_hpa_translation":      ["GPA", "HPA", "translation", "aliasing", "mapping", "page walk"],
    "sept_permissions":         ["permission", "read", "write", "execute", "access control", "enforcement"],
    "pamt_ownership":           ["PAMT", "page type", "ownership", "TD owner", "metadata", "assignment"],
    "sept_pamt_consistency":    ["consistency", "cross-check", "mismatch", "PAMT", "SEPT", "synchronization"],
    "sept_transition_attacks":  ["blocked", "pending", "accept", "TDACCEPTPAGE", "transition attack", "VMM manipulation"],
    "sept_misconfiguration":    ["misconfiguration", "rogue mapping", "malicious VMM", "aliased", "injection"],
    "toctou_race":              ["TOCTOU", "race condition", "concurrent", "multi-vCPU", "atomic", "simultaneous"],
    "large_page_handling":      ["large page", "split", "promotion", "demotion", "2M", "1G", "4K", "page size"],
    "shared_private_routing":   ["shared bit", "shared EPT", "private EPT", "routing", "bypass", "shared GPA"],
}

TECH_MARKERS = {
    "sept_state_machine":       ["TDH.MEM.SEPT.ADD", "SEPT_PRESENT", "SEPT_PENDING", "SEPT_BLOCKED",
                                  "SEPT_FREE", "SEPT_NL", "leaf entry", "non-leaf entry"],
    "gpa_hpa_translation":      ["GPAW", "guest physical address width", "EPT violation", "TDH.MEM.SEPT.ADD",
                                  "address translation table", "4-level", "5-level"],
    "sept_permissions":         ["R/W/X", "XS bit", "XU bit", "supervisor shadow stack", "SEPT.RWX",
                                  "user executable", "supervisor executable"],
    "pamt_ownership":           ["PAMT_4K", "PAMT_2M", "PAMT_1G", "PAMT entry owner", "TDH.MEM.PAGE.ADD",
                                  "TDH.MEM.PAGE.AUG"],
    "sept_pamt_consistency":    ["TDH.MEM.SEPT.ADD", "PAMT.OWNER", "PAMT.PT", "cross-reference check",
                                  "SEPT-PAMT mismatch"],
    "sept_transition_attacks":  ["TDH.MEM.RANGE.BLOCK", "TDH.MEM.RANGE.UNBLOCK", "TDH.MEM.TRACK",
                                  "TDH.MEM.PAGE.ACCEPT", "TDG.MEM.PAGE.ACCEPT", "TLB tracking epoch"],
    "sept_misconfiguration":    ["SEAMCALL", "VMM-controlled EPT pointer", "shared EPTP",
                                  "host-side page table", "TDH.MEM.SEPT.REMOVE"],
    "toctou_race":              ["TDH.MEM.TRACK", "epoch counter", "TLB shootdown", "IPI broadcast",
                                  "atomic compare-and-swap", "SEPT entry lock"],
    "large_page_handling":      ["TDH.MEM.PAGE.PROMOTE", "TDH.MEM.PAGE.DEMOTE", "PAMT_2M", "PAMT_1G",
                                  "huge page split", "leaf-to-non-leaf conversion"],
    "shared_private_routing":   ["shared bit (GPA bit 51)", "S-EPT", "shared EPTP", "private GPA space",
                                  "shared GPA space", "async #VE"],
}"""
# Single top-level user query (Experiment 1 baseline: no query expansion)
USER_QUERY = "Extract missing security verification properties related to Attestation in Intel TDX"

DOMAINS = {
    "measurement_integrity":       ["MRTD", "RTMR", "extend", "measurement", "immutable", "finalize"],
    "reportmac_key_isolation":     ["REPORTMAC", "MAC", "key derivation", "HKID", "key isolation", "bound key"],
    "reportdata_freshness":        ["REPORTDATA", "nonce", "challenge", "freshness", "replay", "binding"],
    "tdreport_correctness":        ["TDREPORT", "TDCALL", "attributes", "state", "consistency", "mismatch"],
    "quoting_enclave_handoff":     ["Quoting Enclave", "QE", "quote", "handoff", "SGX", "verification"],
    "td_lifecycle_attestation":    ["lifecycle", "INIT", "RUNNING", "TEARDOWN", "SEAM", "TD state"],
    "mktme_key_binding":           ["MKTME", "KeyID", "key lifecycle", "per-TD", "key derivation", "TME"],
    "rollback_replay_protection":  ["rollback", "replay", "counter", "monotonic", "recreate", "reuse"],
    "fault_injection_resilience":  ["fault injection", "partial write", "corruption", "atomic", "integrity violation"],
    "side_channel_leakage":        ["side channel", "timing", "speculation", "leakage", "covert", "cache"],
}

TECH_MARKERS = {
    "measurement_integrity":      ["TDH.MR.EXTEND", "MRTD", "RTMR index", "measurement register finalize"],
    "reportmac_key_isolation":    ["TDH.MNG.KEY.CONFIG", "REPORTMACSTRUCT", "attestation key derivation",
                                    "HMAC key isolation"],
    "reportdata_freshness":       ["REPORTDATA field", "nonce binding", "freshness challenge",
                                    "replay window"],
    "tdreport_correctness":       ["TDG.MR.REPORT", "TDREPORT structure", "TD attributes field",
                                    "state consistency check"],
    "quoting_enclave_handoff":    ["Quoting Enclave", "ECDSA quote", "SGX attestation key",
                                    "QE identity verification"],
    "td_lifecycle_attestation":   ["TDH.MNG.INIT", "SEAM VMX root", "TD state transition",
                                    "TEARDOWN state"],
    "mktme_key_binding":          ["TDH.MNG.KEY.CONFIG", "KeyID binding", "per-TD key derivation"],
    "rollback_replay_protection": ["monotonic counter", "TCB recovery", "anti-rollback"],
    "fault_injection_resilience": ["partial write detection", "glitch injection",
                                    "integrity violation trap"],
    "side_channel_leakage":       ["cache timing", "speculative execution leak", "covert channel"],
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

# =============================================================================
# DEPENDENCY CHECK
# =============================================================================

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

# =============================================================================
# TOKENIZER
# =============================================================================

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

# =============================================================================
# STEP 1 — PDF EXTRACTION
# =============================================================================

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
"""
# =============================================================================
# STEP 2 — CHUNKING v2
# =============================================================================

_SECTION_HEADING_RE = re.compile(r"^(\d+(?:\.\d+){0,4})\s+([A-Z][^\n]{5,80})$(?=\n\n|\n*$)", re.MULTILINE)
_SENTENCE_SPLIT_RE = re.compile(r"(?<=[.!?])\s+")
_TABLE_LINE_RE = re.compile(r"[|│┼┤├]")
_TABLE_BLOCK_PATTERN = re.compile(r"((?:[ \t]*(?:[^\n]*[|│┼][^\n]*)[ \t]*\n){2,})")


def _is_table_context(text: str, match_start: int, window: int = 200) -> bool:
    snippet = text[max(0, match_start - window): match_start + window]
    return len(_TABLE_LINE_RE.findall(snippet)) >= 4


def _extract_table_blocks(text: str) -> Tuple[str, Dict[str, str]]:
    table_map: Dict[str, str] = {}
    counter = [0]

    def _replace(m: re.Match) -> str:
        key = f"__TABLE_BLOCK_{counter[0]}__"
        table_map[key] = m.group(0).strip()
        counter[0] += 1
        return f"\n\n{key}\n\n"

    modified = _TABLE_BLOCK_PATTERN.sub(_replace, text)
    return modified, table_map


def _sentence_boundary_overlap(text: str, budget_tokens: int) -> str:
    sentences = [s.strip() for s in _SENTENCE_SPLIT_RE.split(text) if s.strip()]
    collected, total = [], 0
    for sent in reversed(sentences):
        t = _count_tokens(sent)
        if total + t > budget_tokens and collected:
            break
        collected.insert(0, sent)
        total += t
        if total >= budget_tokens:
            break
    return " ".join(collected)


def _is_meaningful(text: str) -> bool:
    return len(text.split()) >= MIN_MEANINGFUL_WORDS


def _split_into_sections(text: str) -> List[Dict]:
    matches = [m for m in _SECTION_HEADING_RE.finditer(text) if not _is_table_context(text, m.start())]
    sections, current_page = [], "1"
    for i, m in enumerate(matches):
        sec_id, sec_title = m.group(1), m.group(2).strip()
        start = m.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        body = text[start:end].strip()
        page_hits = re.findall(r"===== PAGE (\d+)", text[:start])
        if page_hits:
            current_page = page_hits[-1]
        sections.append({"section_id": sec_id, "section_title": sec_title, "page": current_page, "text": body})
    preamble = text[:matches[0].start()].strip() if matches else text.strip()
    if len(preamble.split()) > 30:
        sections.insert(0, {"section_id": "0", "section_title": "Preamble", "page": "1", "text": preamble})
    return sections


def _emit_chunk(token_list, source, sec, out_chunks, seen_hashes, counter, label_prefix=""):
    text_out = _decode(token_list).strip()
    if not text_out or not _is_meaningful(text_out):
        return False
    h = hashlib.md5(text_out.encode()).hexdigest()
    if h in seen_hashes:
        return False
    seen_hashes.add(h)
    section_label = f"{sec['section_id']} {sec['section_title']}"
    out_chunks.append({
        "text": (label_prefix + text_out) if label_prefix else text_out,
        "source": source,
        "chunk_id": f"{source}_{counter[0]}",
        "section": section_label,
        "section_id": sec["section_id"],
        "section_title": sec["section_title"],
        "page": sec["page"],
        "tokens": len(token_list),
    })
    counter[0] += 1
    return True


def _chunk_one_section(sec, max_tok, min_tok, overlap_tok, source, out_chunks, seen_hashes, counter):
    section_text, table_map = _extract_table_blocks(sec["text"])
    paragraphs = [p.strip() for p in re.split(r"\n{2,}", section_text) if len(p.strip()) > 10]
    expanded_paragraphs = [(table_map[p], True) if p in table_map else (p, False) for p in paragraphs]

    buffer, carry_text, emitted_chunks_texts = [], "", []

    def _flush(force=False):
        nonlocal buffer, carry_text
        if not buffer:
            return False
        if not force and len(buffer) < min_tok:
            return False
        decoded = _decode(buffer)
        ok = _emit_chunk(buffer, source, sec, out_chunks, seen_hashes, counter)
        if ok:
            emitted_chunks_texts.append(decoded)
            overlap_str = _sentence_boundary_overlap(decoded, overlap_tok)
            carry_text = overlap_str
            buffer = _encode(overlap_str) if overlap_str else []
        else:
            buffer, carry_text = [], ""
        return ok

    buffer = _encode(carry_text) if carry_text else []

    for para_text, is_table in expanded_paragraphs:
        para_toks = _encode(para_text)
        if is_table:
            _flush(force=True)
            buffer, carry_text = [], ""
            _emit_chunk(para_toks, source, sec, out_chunks, seen_hashes, counter, label_prefix="TABLE: ")
            emitted_chunks_texts.append(para_text)
            carry_text, buffer = "", []
        elif len(para_toks) > max_tok:
            _flush(force=True)
            buffer = _encode(carry_text) if carry_text else []
            carry_text = ""
            sentences = [s for s in _SENTENCE_SPLIT_RE.split(para_text) if s.strip()]
            for sent in sentences:
                sent_toks = _encode(sent)
                if len(buffer) + len(sent_toks) <= max_tok:
                    buffer.extend(sent_toks)
                else:
                    _flush(force=True)
                    buffer = _encode(carry_text) if carry_text else []
                    buffer.extend(sent_toks)
        elif len(buffer) + len(para_toks) <= max_tok:
            buffer.extend(para_toks)
        else:
            flushed = _flush(force=False)
            if flushed:
                buffer = _encode(carry_text) if carry_text else []
                buffer.extend(para_toks)
            else:
                buffer.extend(para_toks)
                if len(buffer) > max_tok:
                    _flush(force=True)
                    buffer = _encode(carry_text) if carry_text else []

    if buffer:
        if len(buffer) < min_tok and emitted_chunks_texts and out_chunks:
            tail_text = _decode(buffer).strip()
            prev = out_chunks[-1]
            merged = prev["text"] + "\n\n" + tail_text
            merged_tok = _encode(merged)
            if len(merged_tok) <= max_tok * 1.25:
                prev["text"] = merged
                prev["tokens"] = len(merged_tok)
                seen_hashes.add(hashlib.md5(merged.encode()).hexdigest())
            else:
                _emit_chunk(buffer, source, sec, out_chunks, seen_hashes, counter)
        else:
            _flush(force=True)


def document_aware_recursive_chunk(text: str, source: str) -> List[Dict]:
    max_tok, min_tok = CHUNK_MAX_TOKENS, CHUNK_MIN_TOKENS
    overlap_tok = int(max_tok * CHUNK_OVERLAP_PCT)
    sections = _split_into_sections(text)
    out_chunks, seen_hashes, counter = [], set(), [0]
    for sec in sections:
        _chunk_one_section(sec, max_tok, min_tok, overlap_tok, source, out_chunks, seen_hashes, counter)
    return out_chunks


def chunk_all_documents(documents: List[Dict]) -> List[Dict]:
    print(f"  Tokenizer     : {'tiktoken cl100k_base' if _TIKTOKEN_OK else 'word-count fallback'}")
    all_chunks = []
    for doc in documents:
        chunks = document_aware_recursive_chunk(doc["text"], source=doc["source"])
        all_chunks.extend(chunks)
        print(f"  {doc['source']}: {len(chunks)} chunks")
    print(f"  Total chunks  : {len(all_chunks)}")
    return all_chunks
"""

 
# =============================================================================
# CHUNKING STRATEGY — PARAGRAPH-BASED (converted from the document-aware /
# section-header-based v7 chunker)
# =============================================================================
# Pure paragraph segmentation: no section-heading detection, no table-block
# extraction, no sentence-boundary carry-forward. Paragraphs (blank-line
# separated blocks) are accumulated up to CHUNK_MAX_TOKENS, with the last
# PARAGRAPH_OVERLAP paragraph(s) of a chunk carried forward into the next
# chunk as simple overlap. This is the deliberately structure-blind
# counterpart to the section-aware chunker it replaces here -- useful as
# the "Experiment A" baseline against the document-aware "Experiment B" in
# a chunking-strategy ablation.
# =============================================================================
 
PARAGRAPH_MIN_TOKENS = CHUNK_MIN_TOKENS
PARAGRAPH_MAX_TOKENS = CHUNK_MAX_TOKENS
PARAGRAPH_OVERLAP = 1     # number of previous paragraphs carried forward
 
 
def split_paragraphs(text: str) -> List[str]:
    """Pure paragraph segmentation. No section awareness."""
    return [p.strip() for p in re.split(r"\n{2,}", text) if len(p.strip()) > 50]
 
 
def paragraph_based_chunking(text: str, source: str) -> List[Dict]:
    """
    Paragraph-only chunking strategy: paragraphs are accumulated until the
    token budget reaches PARAGRAPH_MAX_TOKENS, then flushed as one chunk,
    carrying the last PARAGRAPH_OVERLAP paragraph(s) forward for context
    continuity. A paragraph that alone exceeds PARAGRAPH_MAX_TOKENS is kept
    as its own oversized chunk rather than being truncated or mid-sentence
    split (the section-aware chunker did sentence-level splitting here;
    this simpler strategy intentionally does not).
    """
    paragraphs = split_paragraphs(text)
 
    chunks = []
    buffer: List[str] = []
    buffer_tokens = 0
    counter = 0
 
    for para in paragraphs:
        para_tokens = _count_tokens(para)
 
        # Paragraph itself larger than the max chunk budget: flush whatever
        # is buffered, then emit this paragraph as its own standalone chunk.
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
 
        # Paragraph fits in the current buffer -- accumulate.
        if buffer_tokens + para_tokens <= PARAGRAPH_MAX_TOKENS:
            buffer.append(para)
            buffer_tokens += para_tokens
        else:
            # Buffer is full: flush it (if it already meets the minimum
            # size) before starting a new buffer with this paragraph.
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
 
# =============================================================================
# STEP 3 — CACHE VALIDATION
# =============================================================================

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

# =============================================================================
# STEP 4 — CHROMA VECTOR STORE
# =============================================================================

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

# =============================================================================
# STEP 5 — RETRIEVAL (EXPERIMENT 1: STANDARD RAG ONLY)
# =============================================================================

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


def retrieve_experiment_1(vectorstore, top_n: int = RERANKER_TOP_N) -> List[Dict]:
    """Standard RAG: ONE single query derived from USER_QUERY, plain similarity search."""
    retriever = vectorstore.as_retriever(search_type="similarity", search_kwargs={"k": top_n})
    docs = retriever.invoke(USER_QUERY)
    return [_doc_to_chunk_dict(d) for d in docs]

# =============================================================================
# STEP 6 — METRICS
# =============================================================================

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

# =============================================================================
# PROPERTY-LEVEL QUALITY METRICS
# =============================================================================

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
        "avg_max_similarity_to_existing": round(avg_sim, 4),   # LOWER is better
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
        "avg_faithfulness_proxy": round(avg_score, 4),   # HIGHER is better
        "per_property_scores": [round(s, 3) for s in per_property_scores],
    }


_SOURCE_CITATION_RE = re.compile(r"\[SOURCE\s+(\d+)\]", re.IGNORECASE)


def validate_property_citations(properties: List[str], num_available_sources: int) -> Dict:
    """
    FACTUAL-CORRECTNESS CHECK: verify that every [SOURCE N] tag a property cites
    actually corresponds to a chunk that was retrieved and shown to the LLM.
    A citation to a SOURCE number outside the retrieved range is a strong signal
    of hallucination (the model invented a reference) and is flagged as invalid.
    """
    results = []
    for i, prop in enumerate(properties):
        cited = sorted({int(n) for n in _SOURCE_CITATION_RE.findall(prop)})
        valid = [n for n in cited if 1 <= n <= num_available_sources]
        invalid = [n for n in cited if n not in valid]
        results.append({
            "property_index": i,
            "cited_sources": cited,
            "invalid_citations": invalid,
            "has_citation": len(cited) > 0,
        })

    with_citation = sum(1 for r in results if r["has_citation"])
    with_invalid = sum(1 for r in results if r["invalid_citations"])
    total = len(properties)
    return {
        "total_properties": total,
        "properties_with_citation": with_citation,
        "citation_rate": round(with_citation / total, 4) if total else 0.0,
        "properties_with_invalid_citation": with_invalid,
        "invalid_citation_rate": round(with_invalid / total, 4) if total else 0.0,
        "details": results,
    }


def compute_technical_grounding(properties: List[str], retrieved_chunks: List[Dict]) -> Dict:
    """
    SEMANTIC-ALIGNMENT CHECK: unlike compute_faithfulness_score (generic word
    overlap), this targets the DOMAIN-SPECIFIC technical vocabulary (register
    names, SEAMCALL leaves, state names from TECH_MARKERS). For every technical
    marker a property mentions, we check whether that exact marker also appears
    verbatim in the retrieved context. This is a stricter, more meaningful proxy
    for factual correctness than plain word overlap, since it targets the precise
    hardware terms that must be right for a property to be usable.
    """
    context_text = " ".join(c["text"] for c in retrieved_chunks).lower()
    all_markers = [m for markers in TECH_MARKERS.values() for m in markers]

    per_property = []
    for prop in properties:
        prop_lower = prop.lower()
        mentioned = [m for m in all_markers if m.lower() in prop_lower]
        grounded = [m for m in mentioned if m.lower() in context_text]
        score = (len(grounded) / len(mentioned)) if mentioned else None
        per_property.append({
            "mentioned_markers": mentioned,
            "grounded_markers": grounded,
            "technical_grounding_score": round(score, 3) if score is not None else None,
        })

    scored = [p["technical_grounding_score"] for p in per_property if p["technical_grounding_score"] is not None]
    avg = round(sum(scored) / len(scored), 4) if scored else None
    return {
        "avg_technical_grounding_score": avg,   # HIGHER is better; None = no properties made specific technical claims
        "properties_with_technical_claims": len(scored),
        "properties_without_technical_claims": len(properties) - len(scored),
        "per_property": per_property,
    }


def annotate_properties_with_confidence(
    properties: List[str],
    per_property_faithfulness: List[float],
    citation_check: Dict,
    tech_grounding: Dict,
    threshold: float,
) -> str:
    """
    Produces a human-reviewable annotated version of the generated properties,
    prefixing each one with a factual-correctness / semantic-alignment confidence
    tag derived from faithfulness score + citation validity + technical grounding.
    This does NOT silently drop anything — it surfaces confidence so a reviewer
    (or a downstream automated gate) can prioritize verification effort.
    """
    blocks = []
    for i, prop in enumerate(properties):
        faith = per_property_faithfulness[i] if i < len(per_property_faithfulness) else 0.0
        cite_detail = citation_check["details"][i] if i < len(citation_check["details"]) else {}
        cited = cite_detail.get("cited_sources", [])
        invalid = cite_detail.get("invalid_citations", [])
        tech_detail = tech_grounding["per_property"][i] if i < len(tech_grounding["per_property"]) else {}
        tech_score = tech_detail.get("technical_grounding_score")

        if invalid:
            tag = f"[FLAGGED - cites non-existent SOURCE{invalid} -> verify manually, likely hallucinated reference]"
        elif tech_score is not None and tech_score < 1.0:
            tag = f"[FLAGGED - technical_grounding={tech_score:.2f} -> some cited technical term(s) not found verbatim in retrieved context]"
        elif faith < threshold:
            tag = f"[LOW-CONFIDENCE - faithfulness={faith:.2f} (< {threshold}) -> weak grounding in retrieved context]"
        elif not cited:
            tag = f"[UNCITED - faithfulness={faith:.2f} -> no explicit SOURCE tag found, review before use]"
        else:
            tag = f"[GROUNDED - faithfulness={faith:.2f}, cites SOURCE{cited}]"

        blocks.append(f"{tag}\n{prop}")

    header = (
        "=" * 70 + "\n"
        "ANNOTATED OUTPUT — Factual Correctness & Semantic Alignment Review\n"
        "Tags: GROUNDED (good) | UNCITED (review) | LOW-CONFIDENCE (review) | FLAGGED (likely hallucination)\n"
        + "=" * 70 + "\n\n"
    )
    separator = "\n\n" + ("-" * 70) + "\n\n"
    return header + separator.join(blocks)


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

# =============================================================================
# STEP 7 — PROMPT BUILDER
# =============================================================================

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
    return f"""You are a senior hardware security verification expert with deep expertise in Intel TDX (Trusted Domain Extensions), remote attestation, and assertion-based verification (SystemVerilog Assertions / formal verification).
 
Your task is to identify missing RTL/formal verification properties specifically related to TDX Attestation that are NOT already covered by the existing assertions below.
 
FOCUS AREAS — identify gaps in:
- Measurement integrity and immutability (MRTD, RTMR registers)
- REPORTDATA binding and freshness (nonce/challenge correctness)
- REPORTMAC key isolation across TDs (per-TD key binding)
- Replay and rollback protection
- TD lifecycle attacks (destroy/recreate, state machine violations)
- TD state and attributes correctness reflected in TDREPORT
- Partial write and fault injection scenarios on MRTD/RTMR
- Secure handoff to Quoting Enclave (QE)
- Ordering and atomicity of RTMR extensions
- Mismatch between internal hardware state and reported attestation state
- MKTME KeyID binding to attestation identity
- Side-channel leakage of measurement registers
 
RULES:
- Do NOT repeat or restate any existing property listed below
- Generate ONLY NEW missing properties not covered by existing assertions
- Output MUST be in English
- Think like a CPU security auditor reviewing RTL — focus on realistic hardware-level attack surfaces
- Do NOT give textbook explanations — be concise and technically precise
- For each property provide:
    Property Name:
    Definition: (what hardware behavior must hold)
    Purpose: (why this matters for attestation correctness)
    Security Impact: (what attack or failure is possible if missing)
    Reference: (relevant Intel TDX Module Spec / SDM / MKTME doc topic)
 
EXISTING PROPERTIES (already verified — do NOT repeat these):
{assertions}
 
TDX SPEC CONTEXT (retrieved from Intel TDX documentation):
{context}
 
OUTPUT:
Generate  high-value missing TDX Attestation properties in English:
"""

# =============================================================================
# STEP 8 — LLM CALL
# =============================================================================

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

# =============================================================================
# EXPERIMENT RUNNER (EXPERIMENT 1 ONLY)
# =============================================================================

def run_experiment_1(vectorstore, client, output_dir: str = ".") -> Dict:
    name = "standard_rag"
    print(f"\n{'='*70}\n  EXPERIMENT 1: {name}\n{'='*70}")

    metrics: Dict = {"experiment": 1, "name": name}

    # --- Retrieval stage (timed) ---
    t0 = time.perf_counter()
    chunks = retrieve_experiment_1(vectorstore, top_n=RERANKER_TOP_N)
    t1 = time.perf_counter()
    metrics["retrieval_latency_sec"] = round(t1 - t0, 3)
    metrics["num_retrieval_queries"] = 1
    metrics["final_context_chunk_count"] = len(chunks)

    # --- Retrieval-side metrics ---
    metrics["redundancy_rate"] = round(compute_redundancy_rate(chunks), 4)
    domain_cov, domain_score = compute_retrieved_domain_diversity(chunks)
    metrics["retrieved_domain_coverage"] = domain_cov
    metrics["retrieved_domain_diversity_score"] = round(domain_score, 4)
    metrics["avg_chunk_tokens"] = round(sum(c.get("tokens", 0) for c in chunks) / max(1, len(chunks)), 1)

    # --- Save retrieval log ---
    retrieval_log = [{
        "chunk_id": c["chunk_id"], "source": c["source"], "section": c.get("section", ""),
        "page": c.get("page", ""), "text_preview": c["text"][:200],
    } for c in chunks]
    with open(os.path.join(output_dir, "retrieved_chunks_exp1.json"), "w", encoding="utf-8") as f:
        json.dump(retrieval_log, f, indent=2)

    # --- Build prompt ---
    context_text = build_context_block(chunks)
    prompt = build_prompt(USER_ASSERTIONS, context_text)
    metrics["prompt_chars"] = len(prompt)

    # --- LLM call (timed) ---
    t2 = time.perf_counter()
    result, usage = call_openai(prompt, client)
    t3 = time.perf_counter()
    metrics["llm_latency_sec"] = round(t3 - t2, 3)
    metrics["end_to_end_latency_sec"] = round(t3 - t0, 3)
    metrics["llm_usage"] = usage

    # --- Generation-side metrics ---
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

    # --- Factual correctness / semantic alignment checks -----------------
    citation_check = validate_property_citations(properties, num_available_sources=len(chunks))
    metrics["citation_validation"] = citation_check

    tech_grounding = compute_technical_grounding(properties, chunks)
    metrics["technical_grounding"] = tech_grounding

    low_conf_count = sum(1 for s in faithfulness["per_property_scores"] if s < FAITHFULNESS_MIN_THRESHOLD)
    metrics["low_confidence_property_count"] = low_conf_count
    metrics["low_confidence_rate"] = round(low_conf_count / max(1, len(properties)), 4)
    metrics["factual_correctness_summary"] = {
        "faithfulness_min_threshold": FAITHFULNESS_MIN_THRESHOLD,
        "low_confidence_property_count": low_conf_count,
        "low_confidence_rate": metrics["low_confidence_rate"],
        "citation_rate": citation_check["citation_rate"],
        "invalid_citation_rate": citation_check["invalid_citation_rate"],
        "avg_technical_grounding_score": tech_grounding["avg_technical_grounding_score"],
    }

    # --- Cost estimate ---
    embed_tokens_est = metrics["avg_chunk_tokens"]
    metrics["cost_estimate"] = estimate_cost(
        embed_calls=1,
        embed_tokens=int(embed_tokens_est),
        llm_input_tokens=usage.get("input_tokens", 0),
        llm_output_tokens=usage.get("output_tokens", 0),
    )

    # --- Save outputs ---
    out_path = os.path.join(output_dir, "missing_sept_pamt_properties1_exp1(document).txt")
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(result)
    metrics["output_file"] = out_path

    annotated_text = annotate_properties_with_confidence(
        properties,
        faithfulness["per_property_scores"],
        citation_check,
        tech_grounding,
        FAITHFULNESS_MIN_THRESHOLD,
    )
    annotated_path = os.path.join(output_dir, "missing_sept_pamt_properties1_exp1_ANNOTATED(document).txt")
    with open(annotated_path, "w", encoding="utf-8") as f:
        f.write(annotated_text)
    metrics["annotated_output_file"] = annotated_path

    metrics_path = os.path.join(output_dir, "ablation1_metrics_exp1(document).json")
    with open(metrics_path, "w", encoding="utf-8") as f:
        json.dump(metrics, f, indent=2)

    print_coverage(result)
    print("\n  --- QUALITY METRICS ---")
    print(f"  Property count             : {metrics['property_count']}")
    print(f"  Avg property length (words): {metrics['avg_property_word_count']}")
    print(f"  Technical specificity hits : {metrics['technical_specificity_total']}")
    print(f"  STRICT coverage score      : {metrics['output_coverage_score_strict']}")
    print(f"  Novelty (lower=better)     : {novelty['avg_max_similarity_to_existing']} ({len(novelty['flagged_possible_duplicates'])} possible duplicates)")
    print(f"  Faithfulness (higher=better): {faithfulness['avg_faithfulness_proxy']}")
    print("\n  --- FACTUAL CORRECTNESS / SEMANTIC ALIGNMENT ---")
    print(f"  Citation rate (has [SOURCE N]) : {citation_check['citation_rate']}")
    print(f"  Invalid citation rate          : {citation_check['invalid_citation_rate']} (hallucinated SOURCE refs)")
    print(f"  Avg technical grounding score  : {tech_grounding['avg_technical_grounding_score']}")
    print(f"  Low-confidence properties      : {low_conf_count}/{metrics['property_count']} (faithfulness < {FAITHFULNESS_MIN_THRESHOLD})")
    print(f"\n  Retrieval latency          : {metrics['retrieval_latency_sec']}s")
    print(f"  LLM latency                : {metrics['llm_latency_sec']}s")
    print(f"  Redundancy rate            : {metrics['redundancy_rate']}")
    print(f"  Retrieved-domain diversity : {metrics['retrieved_domain_diversity_score']}")
    print(f"  Est. cost (USD)            : {metrics['cost_estimate']['total_cost_usd_est']}")
    print(f"  Saved: {out_path}")
    print(f"  Saved: {annotated_path}")
    print(f"  Saved: {metrics_path}")

    return metrics
"""
def run_no_rag_query(query: str, client, output_dir: str = ".") -> Dict:
    
    print(f"\n{'='*70}\n  DIRECT QUERY MODE (No document / No RAG)\n{'='*70}")

    metrics: Dict = {"mode": "no_rag_direct_query", "model": OPENAI_MODEL, "query": query}

    prompt = (
        "You are a strict formal verification and Intel TDX security expert.\n\n"
        "Answer the following question using your own knowledge only. "
        "No document context has been retrieved for this query, so do not "
        "invent or reference [SOURCE N] citations, and clearly say so if you "
        "are uncertain about a specific spec detail.\n\n"
        f"Question:\n{query}"
    )
    metrics["prompt_chars"] = len(prompt)

    t0 = time.perf_counter()
    result, usage = call_openai(prompt, client)
    t1 = time.perf_counter()
    metrics["llm_latency_sec"] = round(t1 - t0, 3)
    metrics["llm_usage"] = usage

    metrics["cost_estimate"] = estimate_cost(
        embed_calls=0,
        embed_tokens=0,
        llm_input_tokens=usage.get("input_tokens", 0),
        llm_output_tokens=usage.get("output_tokens", 0),
    )

    out_path = os.path.join(output_dir, "no_rag_response.txt")
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(result)
    metrics["output_file"] = out_path

    metrics_path = os.path.join(output_dir, "no_rag_metrics.json")
    with open(metrics_path, "w", encoding="utf-8") as f:
        json.dump(metrics, f, indent=2)

    print(f"\n{result}\n")
    print(f"  LLM latency    : {metrics['llm_latency_sec']}s")
    print(f"  Est. cost (USD): {metrics['cost_estimate']['total_cost_usd_est']}")
    print(f"  Saved: {out_path}")
    print(f"  Saved: {metrics_path}")

    return metrics
"""

def run_no_rag_query(query: str, client, output_dir: str = ".") -> Dict:
    """
    Direct-query mode: bypasses PDF ingestion, chunking, the vector store, and
    retrieval entirely. Sends the raw question straight to the model using
    only its own parametric knowledge — no document context is provided, so
    the model is explicitly told not to fabricate [SOURCE N] citations.

    Still computes the same domain-coverage report used in Experiment 1, so
    you can compare how much of the SEPT/PAMT domain space the no-RAG answer
    touches versus the retrieval-grounded one.
    """
    print(f"\n{'='*70}\n  DIRECT QUERY MODE (No document / No RAG)\n{'='*70}")

    metrics: Dict = {"mode": "no_rag_direct_query", "model": OPENAI_MODEL, "query": query}

    prompt = (
        "You are a strict formal verification and Intel TDX security expert.\n\n"
        "Answer the following question using your own knowledge only. "
        "No document context has been retrieved for this query, so do not "
        "invent or reference [SOURCE N] citations, and clearly say so if you "
        "are uncertain about a specific spec detail.\n\n"
        f"Question:\n{query}"
    )
    metrics["prompt_chars"] = len(prompt)

    t0 = time.perf_counter()
    result, usage = call_openai(prompt, client)
    t1 = time.perf_counter()
    metrics["llm_latency_sec"] = round(t1 - t0, 3)
    metrics["llm_usage"] = usage

    # --- Coverage report (same DOMAINS keyword logic as Experiment 1) -----
    out_coverage, out_evidence, out_score = compute_coverage(result)
    metrics["output_domain_coverage"] = out_coverage
    metrics["output_domain_evidence"] = out_evidence
    metrics["output_coverage_score"] = round(out_score, 4)

    # --- Property-level parsing + technical specificity (for comparability) --
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

    metrics["cost_estimate"] = estimate_cost(
        embed_calls=0,
        embed_tokens=0,
        llm_input_tokens=usage.get("input_tokens", 0),
        llm_output_tokens=usage.get("output_tokens", 0),
    )

    out_path = os.path.join(output_dir, "no_rag_response.txt")
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(result)
    metrics["output_file"] = out_path

    # --- Save a standalone coverage report (mirrors print_coverage output) ---
    coverage_report_lines = [
        "=" * 70,
        "  TDX SEPT + PAMT COVERAGE REPORT (NO-RAG / DIRECT QUERY)",
        "=" * 70,
    ]
    for domain, covered in out_coverage.items():
        status = "COVERED" if covered else "MISSING"
        evidence = ", ".join(out_evidence.get(domain, [])) or "-"
        coverage_report_lines.append(f"  {domain:25s} : {status:8s} (matched: {evidence})")
    total_covered = sum(out_coverage.values())
    coverage_report_lines.append("")
    coverage_report_lines.append(
        f"  OVERALL COVERAGE SCORE: {out_score:.2f}  ({total_covered}/{len(out_coverage)} domains)"
    )
    coverage_report_lines.append(
        f"  STRICT property-level coverage: {strict_score:.2f} "
        f"({sum(strict_coverage.values())}/{len(strict_coverage)} domains)"
    )
    coverage_report_text = "\n".join(coverage_report_lines)

    coverage_report_path = os.path.join(output_dir, "no_rag_coverage_report.txt")
    with open(coverage_report_path, "w", encoding="utf-8") as f:
        f.write(coverage_report_text)
    metrics["coverage_report_file"] = coverage_report_path

    metrics_path = os.path.join(output_dir, "no_rag_metrics.json")
    with open(metrics_path, "w", encoding="utf-8") as f:
        json.dump(metrics, f, indent=2)

    print(f"\n{result}\n")
    print(coverage_report_text)
    print(f"\n  --- QUALITY METRICS (NO-RAG) ---")
    print(f"  Property count             : {metrics['property_count']}")
    print(f"  Technical specificity hits : {metrics['technical_specificity_total']}")
    print(f"  Novelty (lower=better)     : {novelty['avg_max_similarity_to_existing']} ({len(novelty['flagged_possible_duplicates'])} possible duplicates)")
    print(f"\n  LLM latency    : {metrics['llm_latency_sec']}s")
    print(f"  Est. cost (USD): {metrics['cost_estimate']['total_cost_usd_est']}")
    print(f"  Saved: {out_path}")
    print(f"  Saved: {coverage_report_path}")
    print(f"  Saved: {metrics_path}")

    return metrics
# =============================================================================
# CLI / MAIN
# =============================================================================

def parse_args():
    parser = argparse.ArgumentParser(description="Intel TDX RAG — Experiment 1 (Standard RAG) Only")
    group = parser.add_mutually_exclusive_group(required=False)
    group.add_argument("--pdf", nargs="+", metavar="FILE")
    group.add_argument("--pdf_dir", metavar="DIR")
    parser.add_argument("--model", default=OPENAI_MODEL)
    parser.add_argument("--dims", type=int, default=EMBED_DIMS)
    parser.add_argument("--output_dir", default=".")
    parser.add_argument("--force_rebuild", action="store_true")
    parser.add_argument("--no_rag", action="store_true",
                         help="Skip PDF ingestion and retrieval; query the model directly with no document context")
    parser.add_argument("--query", metavar="TEXT",
                         help="Question to ask in --no_rag mode (defaults to the standard SEPT/PAMT query if omitted)")
    args = parser.parse_args()
    if not args.no_rag and not (args.pdf or args.pdf_dir):
        parser.error("one of --pdf, --pdf_dir is required (or pass --no_rag to skip documents entirely)")
    return args


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

    os.makedirs(args.output_dir, exist_ok=True)

    if args.no_rag:
        query = args.query or USER_QUERY
        run_no_rag_query(query, client, output_dir=args.output_dir)
        return

    pdf_paths = collect_pdf_paths(args)
    vectorstore = get_or_build_vectorstore(pdf_paths, api_key, args.force_rebuild)
    run_experiment_1(vectorstore, client, output_dir=args.output_dir)


if __name__ == "__main__":
    main()
