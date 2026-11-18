# Formalization Progress Record

- **Current Stage**: Sections 2, 3, and 4 **CI verified** on `main` (`13e54c4e`, 9,074 jobs, exit 0). Section 5 formalization **In progress** on branch `sec5`.
- **Remaining `sorry` / `admit` in `main`**: 0.
- **Manuscript-owned axioms**: 0.

## Section Status

| Section | Modules | Status | CI Commit / Notes |
|---|---|---|---|
| **Section 2** | `Basic`, `ExternalAxiomsAnalytic`, `ValuationParity*`, `ExpSumBounds*`, `VaalerMod` | **CI verified** | Passed on `main` (`9074/9074` jobs) |
| **Section 3** | `ExternalAxiomsSec3`, `ChebyshevLucas`, `PellFundamental`, `Thm1_1Collapse`, `Picard2Torsion`, `Thm1_2Iwasawa` | **CI verified** | Passed on `main` (`9074/9074` jobs) |
| **Section 4** | `ExternalAxiomsSec4`, `Prop4_1SmoothBiquad`, `Thm4_2QuarticCores` | **CI verified** | PR #3 merged at `13e54c4e`; CI log `3422515f` (`exit 0`, 9,074 jobs) |
| **Section 5** | `ExternalAxiomsSec5`, `Prop5_1MidpointBias`, `Thm5_2EffectiveCores`, `Thm5_3RedeiCohomology` | **In progress** | Branch `sec5` created from `main` |

## Next Concrete Tasks
1. Formalize `GrasGreenbergBrocard/ExternalAxiomsSec5.lean` (Perron §25 midpoint symmetry, Davenport Ch. 19 real character sum upper bound, and Gauss/Rédei–Reichardt narrow class group package).
2. Formalize `GrasGreenbergBrocard/Prop5_1MidpointBias.lean` (Proposition 5.1(i)–(ii)).
3. Formalize `GrasGreenbergBrocard/Thm5_2EffectiveCores.lean` (Theorem 5.2(i)–(ii)) and `GrasGreenbergBrocard/Thm5_3RedeiCohomology.lean` (Theorem 5.3(i)–(ii)).
4. Update `GrasGreenbergBrocard.lean` and documentation for Section 5, verify `sec5` CI, merge PR to `main`, and verify `main` CI.
