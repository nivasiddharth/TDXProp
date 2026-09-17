# TDXProp: Hardware-Aware Retrieval for Security Property Generation and Coverage Analysis in Intel TDX

**TDXProp** uses retrieval-augmented generation to produce TDX security
properties directly from specification text, without a hand-built formal
model or RTL. It answers a user query about a TDX security objective in two
phases:

- **Offline phase** — builds a *TDX Security Knowledge Base* (KB) once, by
  extracting, chunking, and embedding the specification corpus into a
  searchable index.
- **Online phase** — for each query, expands it into multiple
  reformulations, retrieves supporting evidence from the KB, and generates a
  candidate property from that evidence.

A final **Coverage Analysis** step aggregates properties across queries,
measuring taxonomy coverage at both the retrieval and generation stages.

This repository contains the experimental pipeline and results for an
ablation study comparing three configurations for extracting missing
security verification properties from Intel TDX specification documents:

- **LLM Only** — direct generation, no retrieval.
- **Standard RAG** — single-query, paragraph-level retrieval.
- **TDXProp** — paragraph-level retrieval augmented with five generic query
  reformulations (multi-query expansion).

Each configuration is evaluated independently across four Intel TDX security
domains — **SEPT/PAMT**, **Attestation**, **MKTME**, and **TD Partitioning** —
with the embedding model, vector database, LLM, prompt template, chunking
strategy, context budget, and hardware environment held constant across runs,
so that observed differences primarily reflect the retrieval strategy. Each
configuration × domain pair is run twice (24 total runs); reported metrics are
the arithmetic mean of the two runs unless stated otherwise.

## Repository layout

```
.
├── README.md
├── requirements.txt
│
├── Tdxpropseptandpamt.py              # TDXProp (multi-query RAG) — SEPT/PAMT
├── Tdxpropattestation.py              # TDXProp (multi-query RAG) — Attestation
├── Tdxpropmktme.py                    # TDXProp (multi-query RAG) — MKTME
├── Tdxproptdpartition.py              # TDXProp (multi-query RAG) — TD Partitioning
│
├── llmandstandardragseptandpamt.py    # LLM Only + Standard RAG — SEPT/PAMT
├── llmandstandardragattestation.py    # LLM Only + Standard RAG — Attestation
├── llmandstandardragmktme.py          # LLM Only + Standard RAG — MKTME
├── llmandstandardragpartition.py      # LLM Only + Standard RAG — TD Partitioning
├── retrieval_latency.png            # Retrieval latency: LLM vs RAG vs TDXProp
├── total_latency.png                # End-to-end latency: LLM vs RAG vs TDXProp
├── token_usage.png                  # Input/output token usage per configuration
├── specificity_faithfulness.png     # Technical specificity & faithfulness scores
├── verification/
│   ├── TDXPropintegrity.rkt           # Rosette: integrity property verification
│   └── TDXPropconfidentiality.rkt     # Rosette: confidentiality property verification
│
└── Results.tar.xz
   ```

> The `llmandstandardrag*.py` scripts bundle **two** experiments each: pass
> `--no_rag` for the LLM-Only baseline, or omit it (with `--pdf_dir`/`--pdf`)
> to run Standard RAG. The `Tdxprop*.py` scripts implement the TDXProp
> (multi-query expansion) configuration for their respective domain.

## Pipeline overview

Each script implements the offline/online pipeline described above for its
domain:

**Offline phase — build the TDX Security Knowledge Base (KB)**

1. **Document ingestion** — parses Intel TDX specification PDFs with PyMuPDF
   (`fitz`) and splits them into paragraph-level chunks (600–1200 tokens,
   20% overlap), tokenized with `tiktoken`.
2. **Indexing** — embeds chunks with `text-embedding-3-large` (3072 dims) via
   `langchain-openai` and stores them in a local Chroma vector store
   (`langchain-chroma` / `chromadb`), forming the searchable KB. The index is
   cached under `./vectorstore*` with an `index_metadata.json` fingerprint so
   re-runs skip re-embedding unless `--force_rebuild` is passed.

**Online phase — per-query retrieval and generation**

3. **Query expansion & retrieval** — depending on configuration:
   - *LLM Only*: no retrieval; the model answers from the query alone.
   - *Standard RAG*: a single similarity search against the KB.
   - *TDXProp*: the query is expanded into five generic reformulations, each
     retrieved against the KB, with results merged into a fixed-size context
     window (`RERANKER_TOP_N` / `TOP_N_CHUNKS` chunks).
4. **Generation** — an OpenAI chat model (`gpt-5.5` by default) generates a
   candidate security verification property for the domain, grounded in the
   retrieved evidence (where applicable) and a fixed prompt template.

**Coverage Analysis — aggregation across queries**

5. **Evaluation** — code-native metrics (latency, token usage/cost,
   redundancy, technical specificity, strict coverage, novelty) plus
   LLM-judged **Faithfulness** / **Factual Correctness** via
   [`ragas`](https://github.com/explodinggradients/ragas). Properties
   generated across queries are aggregated to measure taxonomy coverage at
   both the retrieval and generation stages.
6. **Output** — each run writes the generated properties (`.txt`), the
   retrieval log (`.json`), and a metrics report (`.json`) to `--output_dir`.

## Formal Verification (Rosette)

Candidate properties generated by the RAG pipeline are treated as
**hypotheses**, not ground truth. `verification/` contains Rosette
(symbolic-execution-based) formal verification harnesses that check whether
each generated property actually holds against a symbolic model of the
relevant TDX hardware behavior — split by property class:

| File                             | Property class     | Verified properties |
|-----------------------------------|--------------------|:--------------------:|
| `verification/TDXPropintegrity.rkt`       | Integrity properties ( incl. a few split sub-checks) | 90 |
| `verification/TDXPropconfidentiality.rkt` | Confidentiality properties (base cache-confidentiality check ) | 41 |

Each property is encoded as a Rosette `assert` over symbolic TDX state
(SEPT entries, TDR/TDCS records, cache lines, HKID/key bindings, attestation
report fields, etc.), and checked with `(verify ...)`. A property is reported
as **VERIFIED** when the solver returns `unsat` (no counterexample to the
assertion exists) and **VIOLATED** when a counterexample is found. Both
scripts print a per-property pass/fail line as they run, followed by a
summary table over `all-results` at the end.

### Requirements

- [Racket](https://racket-lang.org/) with the
  [Rosette](https://github.com/emina/rosette) solver-aided language installed
  (`raco pkg install rosette`).
- Both scripts `require` three companion modules that define the symbolic
  TDX hardware model and are **not included in this repository**:
  `tables.rkt`, `tdx_lib.rkt`, and `cache_instance_hkid.rkt`. These must be
  present in the same directory (`verification/`) before running either
  script — they define the symbolic constructors (`make-secure_EPT_entry`,
  `make-TDR`, `query-cache`, etc.) that the property assertions are built on.

### Running

```bash
cd verification
raco make TDXPropintegrity.rkt          # optional: precompile
racket TDXPropintegrity.rkt
racket TDXPropconfidentiality.rkt
```

Each script prints one `VERIFIED` / `VIOLATED` line per property as it runs
(with a short description of what was checked), then a final summary table
over `all-results` at the end, e.g.:

```
iP1 VERIFIED: No GPA->HPA mapping in BLOCKED state
iP2 VERIFIED: Finalized TDR cannot revert to INIT/FATAL
...
iP1: VERIFIED ✓
iP2: VERIFIED ✓
iP19 [DocP2-RegScrub]: VERIFIED ✓
...
```

## Requirements

- Python 3.10+
- An OpenAI API key with access to the embedding and chat models configured
  in each script (`text-embedding-3-large`, `gpt-5.5` by default — adjust the
  `EMBED_MODEL` / `OPENAI_MODEL` constants at the top of a script if you use
  different model names).

Install dependencies:

```bash
pip install -r requirements.txt
```

Set your API key:

```bash
export OPENAI_API_KEY="sk-..."
```

## Usage

### Standard RAG (single-query retrieval)

```bash
python llmandstandardragseptandpamt.py --pdf_dir ./specs
```

### LLM Only (no retrieval)

```bash
python llmandstandardragseptandpamt.py --no_rag
python llmandstandardragseptandpamt.py --no_rag --query "custom question"
```

### TDXProp (multi-query expansion RAG)

```bash
python Tdxpropseptandpamt.py --pdf_dir ./specs
```

The same pattern applies to the Attestation, MKTME, and TD Partitioning
variants — swap in the corresponding script for the domain you want to run.

### Common flags

| Flag              | Description                                                        |
|-------------------|----------------------------------------------------------------------|
| `--pdf FILE...`   | One or more specification PDFs to ingest.                          |
| `--pdf_dir DIR`   | Directory of specification PDFs to ingest (mutually exclusive with `--pdf`). |
| `--model NAME`    | Override the OpenAI chat model (default: `gpt-5.5`).                |
| `--dims N`        | Override embedding dimensions (default: `3072`).                    |
| `--output_dir DIR`| Directory to write generated properties / logs / metrics (default: `.`). |
| `--force_rebuild` | Rebuild the vector store even if a cached index is found.           |
| `--no_rag`        | *(LLM-only + Standard RAG scripts only)* Skip retrieval entirely.    |
| `--query TEXT`    | *(LLM-only + Standard RAG scripts only)* Override the default domain query. |

Each run produces, in `--output_dir`:

- `missing_<domain>_properties*.txt` — the generated security properties.
- `retrieved_chunks*.json` — the retrieval log (chunks, scores, sources).
- `ablation*_metrics*.json` — latency, token/cost, and quality metrics for the run.

## Results

### Property generation counts

Number of candidate security verification properties generated per
configuration, per domain (raw counts, not deduplicated against the
reference assertion list):

| Configuration  | SEPT/PAMT | Attestation | MKTME | TD Partitioning | Total |
|----------------|:---------:|:-----------:|:-----:|:----------------:|:-----:|
| LLM Only       | 22        | 34          | 33    | 24               | 113   |
| Standard RAG   | 17        | 27          | 15    | 33               | 92    |
| TDXProp        | 28        | 32          | 31    | 24               | 115   |
we have also contains the aggregated figures referenced in the
paper, comparing **LLM Only**, **Standard RAG**, and **TDXProp** across all
four domains:

- **`retrieval_latency.png`** — TDXProp's multi-query expansion increases
  retrieval latency relative to Standard RAG, as expected from issuing five
  reformulated queries instead of one.
- **`total_latency.png`** — TDXProp has the highest end-to-end latency of the
  three configurations, driven primarily by the additional retrieval calls
  and larger resulting context.
- **`token_usage.png`** — TDXProp consumes the most input and output tokens,
  reflecting its larger retrieved context and longer generations.
- **`specificity_faithfulness.png`** — TDXProp achieves the highest technical
  specificity of the three configurations, with faithfulness comparable to
  Standard RAG and substantially above the LLM-only baseline.

### Raw run outputs

`Results.tar.xz` contains the unprocessed per-run artifacts for all 24
experimental runs (3 configurations × 4 domains × 2 runs) that the aggregated
figures and table above were computed from.

## Notes

- The `vectorstore*/` directories are build artifacts (populated on first
  run) and are not checked into this repository; add them to `.gitignore`
  if you generate them locally.
- `USER_ASSERTIONS` (the reference list of confidentiality/integrity
  properties used for coverage/novelty scoring) is currently shared across
  the SEPT/PAMT, Attestation, MKTME, and TD Partitioning scripts. Swap this
  block out per-domain if/when a domain-specific verified-assertions list is
  available.
- `ragas`-based Factual Correctness / Faithfulness scoring requires network
  access to the OpenAI API at evaluation time, in addition to generation.