# Formalization Progress Record

- **Current Stage**: **COMPLETE MANUSCRIPT FORMALIZATION & ADVERSARIAL AUDIT VERIFIED ON `main`** (Sections 1–8, all 42 main theorems, propositions, and lemmas; PR #8 merged at [`0def862b`](https://github.com/princeanand099/grasgreenbergbrocard/commit/0def862b555263df11fb85cd36847c472d1ac421), [CI Run #44567866016](https://github.com/princeanand099/grasgreenbergbrocard/actions/runs/44567866016/job/135714460223), [CI Log `56e1d6d4`](https://github.com/princeanand099/grasgreenbergbrocard/commit/56e1d6d4bca09efcde64400ed0b5fb3fe1c5e309), `9,091 / 9,091` Lake build targets passing with `exit 0`).
- **Remaining `sorry` / `admit` / `sorryAx` across the entire repository**: `0`.
- **Compiler/kernel bypasses (`native_decide` / `Lean.trustCompiler`)**: `0`.
- **Manuscript-owned axioms**: `0`.

## Section-by-Section Verification Ledger

| Section | Lean Modules (`GrasGreenbergBrocard/`) | Status | Verification Reference |
| :--- | :--- | :--- | :--- |
| **Core Foundations** | `Basic`, `PellFundamental`, `ChebyshevLucas` | **CI verified** | Passing on `main` (`0def862b`, `exit 0`) |
| **Section 2** | `ExternalAxiomsAnalytic`, `ValuationParityLayer`, `ValuationParityDigits`, `ValuationParityVaaler`, `ExpSumBounds`, `ValuationParityThmHelpers`, `ValuationParityThmPart1`, `ValuationParityThmCollar`, `ValuationParityThmInterCollar`, `ValuationParityThm`, `ExpSumBoundsMod`, `VaalerMod`, `ValuationParityModWeight`, `ValuationParityModCollar`, `ValuationParityModInterCollar`, `ValuationParityMod` | **CI verified** | Tightened `vaughan_van_der_corput_prime_sum` (`IsPrimeSubinterval` + `AntitoneOn w`) propagated in [PR #8](https://github.com/princeanand099/grasgreenbergbrocard/pull/8) (`0def862b`, `exit 0`) |
| **Section 3** | `ExternalAxiomsSec3`, `Thm1_1Collapse`, `Picard2Torsion`, `Thm1_2Iwasawa` | **CI verified** | Iwasawa axioms scoped to `canonicalRealQuadIwasawa` in [PR #7](https://github.com/princeanand099/grasgreenbergbrocard/pull/7) (`d22839cc`, `exit 0`) |
| **Section 4** | `ExternalAxiomsSec4`, `Prop4_1SmoothBiquad`, `Thm4_2QuarticCores` | **CI verified** | PR #3 merged (`13e54c4e`); re-verified on `main` (`0def862b`, `exit 0`, 0 new axioms) |
| **Section 5** | `ExternalAxiomsSec5`, `Prop5_1MidpointBias`, `Thm5_2EffectiveCores`, `Thm5_3RedeiCohomology` | **CI verified** | PR #4 merged (`83126170`); re-verified on `main` (`0def862b`, `exit 0`) |
| **Section 6** | `Prop6_1FourGCD`, `Prop6_2ConsecutiveSquareShift`, `Lem6_3ParityFlipOsc`, `Lem6_3ParityFlip`, `Thm6_4CapacityDiamond`, `Thm6_4PolarizationConcentration` | **CI verified** | Honest collar-excised multi-digit Vaaler proof (`lem_6_3_osc_bound_honest`) merged in [PR #8](https://github.com/princeanand099/grasgreenbergbrocard/pull/8) (`0def862b`, `exit 0`, 0 new axioms) |
| **Section 7** | `ExternalAxiomsSec7`, `Sec7PadeWronskian`, `Thm1_3Part2Counting` | **CI verified** | Padé/Wronskian axioms hardened with `IsPolyFactSol`, `HasDepressedDegreeGap`, and `hO` in [PR #7](https://github.com/princeanand099/grasgreenbergbrocard/pull/7) (`d22839cc`, `exit 0`) |
| **Section 8** | `ExternalAxiomsSec8`, `Thm8_1FreyCurves`, `Thm8_2TatuzawaClassGroup` | **CI verified** | `tatuzawa_effective_siegel` scoped to `canonicalRealQuadClassGroup` in [PR #7](https://github.com/princeanand099/grasgreenbergbrocard/pull/7) (`d22839cc`, `exit 0`); constants synchronized with manuscript |
| **Axiom Audit** | `AuditAxioms` | **CI verified** | Added in [PR #7](https://github.com/princeanand099/grasgreenbergbrocard/pull/7); all 42 main declarations re-verified in [PR #8](https://github.com/princeanand099/grasgreenbergbrocard/pull/8) ([CI Log `56e1d6d4`](https://github.com/princeanand099/grasgreenbergbrocard/commit/56e1d6d4bca09efcde64400ed0b5fb3fe1c5e309), `9,091/9,091` jobs, `exit 0`) |

## Completed Milestones

1. **PR #3 (`13e54c4e`)**: Section 4 formalization (`Prop4_1SmoothBiquad`, `Thm4_2QuarticCores`).
2. **PR #4 (`83126170`)**: Section 5 formalization (`Prop5_1MidpointBias`, `Thm5_2EffectiveCores`, `Thm5_3RedeiCohomology`).
3. **PR #5 (`727f61b5`)**: Initial Section 6 formalization (`Prop6_1FourGCD` through `Thm6_4PolarizationConcentration`).
4. **PR #6 (`fc583b1e` / merge)**: Complete Sections 7–8 formalization (`Sec7PadeWronskian`, `Thm1_3Part2Counting`, `Thm8_1FreyCurves`, `Thm8_2TatuzawaClassGroup`).
5. **PR #7 (`d22839cc`)**: Adversarial audit soundness hardening for Sections 3, 7, and 8 external axioms + automated `#print axioms` verification in `AuditAxioms.lean`.
6. **PR #8 (`0def862b`)**: Tightening of `vaughan_van_der_corput_prime_sum` (`IsPrimeSubinterval` + `AntitoneOn w`), propagation across all Section 2 modules, and complete replacement of Section 6.3 oscillatory proof by `lem_6_3_osc_bound_honest`.
