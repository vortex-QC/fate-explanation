# fate-explanation

Replication package. Paper DOI: [10.5281/zenodo.23201747](https://doi.org/10.5281/zenodo.23201747) (backfilled after publish).

**File ↔ section map**

| Artifact | Paper section |
|---|---|
| FateExplanation.lean | §7 formal core T_F1–T_F8 (Theorems, zero sorryAx) |
| mm_test_cri_eaeb_v0.1.py | §4.3 E-A/E-B model-domain implementation (pre-registered) |
| data JSON | §4.3 divergence tables (weight SHA256 895b80d9696c2319) |

**Replication guide**

1. Lean core: `lake env lean DensityMath/FateExplanation.lean` (Lean 4.33.1 + Mathlib); axiom check via `#print axioms`.
2. E-A/E-B: run `mm_test_cri_eaeb_v0.1.py` with a local Qwen3-8B (bf16, GPU ≥ 20 GB free); outputs the data JSON.

**Source data policy**: all experimental data generated locally on the author's machine; no third-party datasets used.

## License

Code (`lean/`): MIT. Docs: CC-BY-4.0.
