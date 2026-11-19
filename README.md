# Formal Verification of Brocard–Ramanujan Arithmetic Structure and Counting Bounds (Lean 4)

[![Repository](https://img.shields.io/badge/GitHub-princeanand099%2Fgrasgreenbergbrocard-blue)](https://github.com/princeanand099/grasgreenbergbrocard)
[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0-informational)](https://lean-lang.org/)
[![CI Status](https://img.shields.io/badge/Lake%20Build-9091%2F9091%20Passing-brightgreen)](https://github.com/princeanand099/grasgreenbergbrocard/actions/runs/44567866016/job/135714460223)

## 1. Overview

This repository contains the complete, machine-checked Lean 4 (`v4.35.0`) formalization of the manuscript *Arithmetic Structure, Iwasawa Theory, and Counting Bounds for the Brocard–Ramanujan Equation* (`brocard_arithmetic_structure_and_counting_bounds.tex`). The formalization spans 43 Lean modules covering Sections 1 through 8 of the manuscript, together with an automated kernel-level axiom audit module (`GrasGreenbergBrocard/AuditAxioms.lean`).

All 9,091 Lake build targets compile cleanly with `exit 0`, zero errors, zero `sorry` placeholders, and zero compiler-bypass or kernel-extension mechanisms. Every main theorem, proposition, and lemma depends strictly on Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) together with explicitly isolated, peer-reviewed literature axioms declared exclusively inside the `ExternalAxioms*.lean` files.

| Verification Metric | Verified State | Reference |
| :--- | :--- | :--- |
| Lean 4 Toolchain | `leanprover/lean4:v4.35.0` | `lean-toolchain` |
| Total Lake Build Targets | `9,091 / 9,091` passing (`exit 0`) | [CI Run #44567866016](https://github.com/princeanand099/grasgreenbergbrocard/actions/runs/44567866016/job/135714460223) |
| Audited Main Declarations | `42` theorems, propositions, and lemmas | `GrasGreenbergBrocard/AuditAxioms.lean` |
| `sorry` / `admit` / `sorryAx` | `0` | [CI Log `56e1d6d4`](https://github.com/princeanand099/grasgreenbergbrocard/commit/56e1d6d4bca09efcde64400ed0b5fb3fe1c5e309) |
| `native_decide` / `Lean.trustCompiler` | `0` | [CI Log `56e1d6d4`](https://github.com/princeanand099/grasgreenbergbrocard/commit/56e1d6d4bca09efcde64400ed0b5fb3fe1c5e309) |
| Adversarial Audit Hardening | Merged (`d22839cc`) | [PR #7](https://github.com/princeanand099/grasgreenbergbrocard/pull/7) |
| Analytic Axiom Tightening & Honest Sec. 6.3 | Merged (`0def862b`) | [PR #8](https://github.com/princeanand099/grasgreenbergbrocard/pull/8) |

## 2. Repository Architecture and Module Map

The root entry point `GrasGreenbergBrocard.lean` imports all thematic sections in dependency order and concludes with `GrasGreenbergBrocard.AuditAxioms`, ensuring that every CI build verifies both proof compilation and kernel-level `#print axioms` closure.

| Manuscript Section | Lean Modules (`GrasGreenbergBrocard/`) | Mathematical Scope |
| :--- | :--- | :--- |
| Core Foundations | `Basic`, `PellFundamental`, `ChebyshevLucas` | Square-free core $q_n$ of $n!$, fundamental Pell solutions, Chebyshev/Lucas recurrence identities |
| Section 2 (Analytic Parity) | `ExternalAxiomsAnalytic`, `ValuationParityLayer`, `ValuationParityDigits`, `ValuationParityVaaler`, `ExpSumBounds`, `ValuationParityThmHelpers`, `ValuationParityThmPart1`, `ValuationParityThmCollar`, `ValuationParityThmInterCollar`, `ValuationParityThm` | Asymptotics of $\log q_n$, Vaaler extremal approximation, dyadic prime exponential sums, second-order valuation parity $\Delta(n)$ and $S_{\mathrm{odd}}(n)$ |
| Section 2 (Modular Parity) | `ExpSumBoundsMod`, `VaalerMod`, `ValuationParityModWeight`, `ValuationParityModCollar`, `ValuationParityModInterCollar`, `ValuationParityMod` | Multi-modulus power-band equidistribution for factorial prime valuations |
| Section 3 & Thms 1.1–1.2 | `ExternalAxiomsSec3`, `Thm1_1Collapse`, `Thm1_2Iwasawa` | Pell index collapse ($k \in \{1,2\}$ for large $n$), fundamental regulator quantization, distinctness of $q_n$, $J_n$ principality, Leopoldt–Coates valuation law, Ozaki–Taya split-prime Iwasawa invariants, conditional finiteness |
| Section 4 | `ExternalAxiomsSec4`, `Picard2Torsion`, `Prop4_1SmoothBiquad`, `Thm4_2QuarticCores` | Picard $2$-torsion, smooth biquadratic models, Euclidean lock, dual quartic structure, midpoint core bounds |
| Section 5 | `ExternalAxiomsSec5`, `Prop5_1MidpointBias`, `Thm5_2EffectiveCores`, `Thm5_3RedeiCohomology` | Continued-fraction midpoint symmetry and bias, cross-symmetry, effective core bounds via Davenport character sums, Rédei–Reichardt cohomology and $4$-rank |
| Section 6 & Thm 1.3(i) | `Prop6_1FourGCD`, `Prop6_2ConsecutiveSquareShift`, `Lem6_3ParityFlipOsc`, `Lem6_3ParityFlip`, `Thm6_4CapacityDiamond`, `Thm6_4PolarizationConcentration` | $\mathrm{SL}_2$ / four-GCD structure, consecutive square-shift $k=2$ exclusions, honest collar-excised multi-digit Vaaler parity-flip bound, capacity diamond, $k=2$ gap and counting bounds, polarization concentration |
| Section 7 & Thm 1.3(ii) | `ExternalAxiomsSec7`, `Sec7PadeWronskian`, `Thm1_3Part2Counting` | Pigeonhole Siegel lemma, initial Padé polynomials, Puiseux monomial-product independence, support-reduced Wronskian, denominator clearing, global and Brocard $6/7$ counting bounds, depressed degree-gap bounds |
| Section 8 | `ExternalAxiomsSec8`, `Thm8_1FreyCurves`, `Thm8_2TatuzawaClassGroup` | Frey elliptic curve modularity and Galois representations, level-$2$ CM reduction, $abc$-quality and Hall-type bounds, Tatuzawa effective Siegel theorem, narrow $2^J$-rank lower bounds |
| Automated Audit | `AuditAxioms` | Machine-checked `#print axioms` verification across all 42 main results |

## 3. Formal Verification Standards and Audit History

To ensure that the formalization matches the mathematical statements of the manuscript without circularity, vacuous quantification, or Lean kernel exploits, the repository underwent a two-stage adversarial audit prior to finalization.

### 3.1 Anti-Cheating Verification Invariants
Every module in `GrasGreenbergBrocard/` satisfies the following invariants, re-verified on every CI build:

1. **No incomplete proofs**: Zero occurrences of `sorry`, `admit`, or `sorryAx` anywhere in the dependency graph.
2. **No compiler or kernel bypass**: Zero occurrences of `native_decide`, `Lean.ofReduceBool`, or `Lean.trustCompiler`.
3. **No unsound metaprogramming or opaque escape hatches**: Zero occurrences of `unsafe`, `implemented_by`, `extern`, `partial`, or `opaque` in proof modules.
4. **Strict axiom isolation**: Every `axiom` declaration resides exclusively inside the five populated `ExternalAxioms*.lean` files (`ExternalAxiomsAnalytic`, `ExternalAxiomsSec3`, `ExternalAxiomsSec5`, `ExternalAxiomsSec7`, `ExternalAxiomsSec8`). `ExternalAxiomsSec4.lean` declares zero axioms, and Section 6 introduces zero new axioms.
5. **Automated kernel axiom reporting**: `GrasGreenbergBrocard/AuditAxioms.lean` executes `#print axioms` on all 42 main theorems during `lake build`.

### 3.2 Soundness Hardening in PR #7 (`d22839cc`)
During the first adversarial audit ([PR #7](https://github.com/princeanand099/grasgreenbergbrocard/pull/7)), four external axiom declarations were hardened to eliminate over-broad quantification:

- **`bpz_dyadic_cluster_elimination` (`ExternalAxiomsSec7.lean`)**: Bound explicitly to `IsPolyFactSol` and `HasDepressedDegreeGap`, accompanied by a fully formalized proof of `brocard_poly_depressed_gap`.
- **`siegel_bpz_support_wronskian` (`ExternalAxiomsSec7.lean`)**: Strengthened with the explicit Padé vanishing-order hypothesis `hO`.
- **Iwasawa axioms (`ExternalAxiomsSec3.lean`)**: Scoped to the canonical real quadratic Iwasawa structure `canonicalRealQuadIwasawa q p` rather than quantifying over arbitrary abstract invariant tuples.
- **`tatuzawa_effective_siegel` (`ExternalAxiomsSec8.lean`)**: Scoped to `canonicalRealQuadClassGroup` to prevent instantiation with arbitrary fabricated class-group records.

### 3.3 Analytic Axiom Tightening and Honest Section 6.3 Proof in PR #8 (`0def862b`)
The final residual audit gap concerned `vaughan_van_der_corput_prime_sum` in `ExternalAxiomsAnalytic.lean`, which previously lacked explicit prime-subinterval and weight-monotonicity hypotheses. In [PR #8](https://github.com/princeanand099/grasgreenbergbrocard/pull/8) (head [`9fb877a9`](https://github.com/princeanand099/grasgreenbergbrocard/commit/9fb877a99dc5a7535709daa7b35ce5ea4a0f9f5d), merged at [`0def862b`](https://github.com/princeanand099/grasgreenbergbrocard/commit/0def862b555263df11fb85cd36847c472d1ac421)):

- **Axiom tightening**: `vaughan_van_der_corput_prime_sum` now explicitly requires `IsPrimeSubinterval P I` (every element of $I$ is prime and lies in a contiguous subinterval of $[P, 2P]$) and `AntitoneOn w (Set.Icc P (2 * P))` (monotone decreasing weight).
- **Section 2 propagation**: `ExpSumBounds.lean`, `ExpSumBoundsMod.lean`, and all six `ValuationParity*` modules were updated to supply verified `IsPrimeSubinterval` and monotonicity proofs at every call site.
- **Honest Section 6.3 oscillatory proof**: The prior oscillatory-weight argument in `Lem6_3ParityFlipOsc.lean` was replaced by `lem_6_3_osc_bound_honest`, a collar-excised multi-digit Vaaler exponential-sum proof using exclusively the monotone weight $w(t) = 1/t$, genuine prime subintervals, and the non-resonance gap hypothesis propagated through `Lem6_3ParityFlip.lean` and `Thm6_4CapacityDiamond.lean`.
- **Unchanged public theorem statements**: `thm_6_4_capacity_diamond`, `thm_1_3_part1_k2_gap_and_counting`, `prop_6_2_part3_consecutive_squares_k2_exclusion`, and `thm_6_4_polarization_concentration` retain their exact public statements.

## 4. Documentation and Audit Records

- [`EXTERNAL_AXIOMS.md`](EXTERNAL_AXIOMS.md): Complete register of all external peer-reviewed literature axioms, their structural hypotheses, and dependent modules (zero manuscript-owned results).
- [`THEOREM_CORRESPONDENCE.md`](THEOREM_CORRESPONDENCE.md): Exhaustive manuscript-to-Lean correspondence and kernel `#print axioms` classification for all 42 audited declarations.
- [`MATHEMATICAL_CORRECTIONS.md`](MATHEMATICAL_CORRECTIONS.md): Formal mathematical audit log documenting the synchronized manuscript refinements and PR #7 / PR #8 soundness hardenings.
- [`PROGRESS.md`](PROGRESS.md): Complete formalization milestone and CI verification ledger.

## 5. Local Reproduction and Verification

To reproduce the complete build and verify the `#print axioms` audit locally (requires `elan` and Lean `v4.35.0`):

```bash
git clone https://github.com/princeanand099/grasgreenbergbrocard.git
cd grasgreenbergbrocard
lake exe cache get
lake build
lake build GrasGreenbergBrocard.AuditAxioms
```

A clean build exits with status `0` and prints the exact Lean kernel axiom closure for all 42 audited declarations.
