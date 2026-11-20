# Formalization Progress

All sections (Sections 1–8) of *Arithmetic Structure and Counting Bounds for the Brocard–Ramanujan Equation* ([DOI: 10.5281/zenodo.24278751](https://doi.org/10.5281/zenodo.24278751)) are formalized in Lean 4 (`v4.35.0`) with **0 `sorry`s**, **0 `admit`s**, **0 `native_decide`**, **0 unused axioms**, and **0 circular axioms**.

| Section | Modules | Status | Audited Declarations |
| :--- | :--- | :--- | :--- |
| Section 2 | `ValuationParityLayer`, `ValuationParityVaaler`, `ExpSumBounds`, `ExpSumBoundsMod`, `ValuationParityThm`, `ValuationParityMod` | Complete | 6 |
| Section 3 (Thms. 1.1–1.2) | `PellFundamental`, `Thm1_1Collapse`, `Picard2Torsion`, `Thm1_2Iwasawa` | Complete | 14 |
| Section 4 | `Prop4_1SmoothBiquad`, `Thm4_2QuarticCores` | Complete | 6 |
| Section 5 | `Prop5_1MidpointBias`, `Thm5_2EffectiveCores`, `Thm5_3RedeiCohomology` | Complete | 9 |
| Section 6 (Thm. 1.3(i)) | `Prop6_1FourGCD`, `Prop6_2ConsecutiveSquareShift`, `Lem6_3ParityFlip`, `Thm6_4CapacityDiamond`, `Thm6_4PolarizationConcentration` | Complete | 8 |
| Section 7 (Thm. 1.3(ii)) | `Sec7PadeWronskian`, `Sec7ClusterReduction`, `Thm1_3Part2Counting` | Complete | 12 |
| Section 8 | `Thm8_1FreyCurves`, `Thm8_2TatuzawaClassGroup` | Complete | 4 |
| **Total** | **28 Lean modules (incl. 6 external axiom files + `AuditAxioms.lean`)** | **Complete (CI green)** | **59** |
