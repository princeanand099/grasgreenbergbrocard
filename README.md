# GrasGreenbergBrocard

[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0-blue)](https://lean-lang.org/)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24278751.svg)](https://doi.org/10.5281/zenodo.24278751)

Lean 4 (`v4.35.0`) formalization of **Prince Anand**, *Arithmetic Structure and Counting Bounds for the Brocard–Ramanujan Equation* ([DOI: 10.5281/zenodo.24278751](https://doi.org/10.5281/zenodo.24278751)).

## Highlights

- **Complete Coverage (Sections 1–8)**: Formalizes Theorems 1.1, 1.2, 1.3(i)–(ii), 4.2, 5.2, 5.3, 6.4, 8.1, 8.2, Propositions 2.2, 2.4, 3.2, 4.1, 5.1, 6.1, 6.2, and Lemmas 2.1, 3.3, 6.3, 7.1–7.4.
- **Zero Kernel Bypasses**: `0` `sorry`s, `0` `admit`s, `0` `native_decide` (`Lean.ofReduceBool`/`Lean.trustCompiler`).
- **Audited External Axioms**: **28** strictly external, peer-reviewed axioms isolated in **6** `ExternalAxioms*.lean` files (`0` unused, `0` circular), verified across **59** `#print axioms` declarations in `GrasGreenbergBrocard/AuditAxioms.lean`.

## Build & Verify

```bash
lake exe cache get
lake build
lake build GrasGreenbergBrocard.AuditAxioms
```

## Documentation

- [`THEOREM_CORRESPONDENCE.md`](THEOREM_CORRESPONDENCE.md) — Exact theorem-by-theorem mapping between the manuscript and Lean 4 declarations.
- [`EXTERNAL_AXIOMS.md`](EXTERNAL_AXIOMS.md) — Complete inventory of all 28 external axioms across 6 files with published references.
- [`AUDIT.md`](AUDIT.md) — Machine-checked verification report and 4-tier adversarial audit repair log.
- [`PROGRESS.md`](PROGRESS.md) — Module-by-module completion status.
- [`MATHEMATICAL_CORRECTIONS.md`](MATHEMATICAL_CORRECTIONS.md) — Record of mathematical clarifications and edge-case refinements discovered during formalization.

## Citation

If you use this formalization or the accompanying manuscript, please cite:

- Prince Anand, *Arithmetic Structure and Counting Bounds for the Brocard–Ramanujan Equation*, Zenodo, DOI: [10.5281/zenodo.24278751](https://doi.org/10.5281/zenodo.24278751). See [`CITATION.cff`](CITATION.cff) for BibTeX/CFF metadata.
