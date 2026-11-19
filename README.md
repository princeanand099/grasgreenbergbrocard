# Arithmetic Structure and Counting Bounds for the Brocard–Ramanujan Equation (Lean 4 Formalization)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24278751.svg)](https://doi.org/10.5281/zenodo.24278751)
[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0-blue)](https://lean-lang.org/)
[![Lake Build](https://img.shields.io/badge/Lake%20Build-9091%2F9091%20Passing-brightgreen)](https://github.com/princeanand099/grasgreenbergbrocard/actions/runs/44567866016/job/135714460223)
[![Sorry Count](https://img.shields.io/badge/sorry-0-brightgreen)](https://github.com/princeanand099/grasgreenbergbrocard/commit/56e1d6d4bca09efcde64400ed0b5fb3fe1c5e309)
[![License](https://img.shields.io/badge/License-Apache--2.0-lightgrey)](LICENSE)

## 1. Overview and Accompanying Manuscript

This repository provides a complete, machine-checked **Lean 4** (`v4.35.0`) formalization of the manuscript:

> **Prince Anand**, *Arithmetic Structure and Counting Bounds for the Brocard–Ramanujan Equation* (November 2026).
> - **Permanent DOI**: [`10.5281/zenodo.24278751`](https://doi.org/10.5281/zenodo.24278751)
> - **Self-Contained Manuscript (PDF)**: [`Brocard Arithmetic Structure And Counting Bounds.pdf`](Brocard%20Arithmetic%20Structure%20And%20Counting%20Bounds.pdf)
> - **LaTeX Source**: [`brocard_arithmetic_structure_and_counting_bounds.tex`](brocard_arithmetic_structure_and_counting_bounds.tex)

The formalization comprises **43 Lean modules** covering Sections 1–8 of the paper, together with an automated kernel-level axiom audit module (`GrasGreenbergBrocard/AuditAxioms.lean`). All `9,091` Lake build targets compile with `exit 0`, **zero `sorry`**, **zero `admit`**, and **zero `native_decide` / `Lean.trustCompiler`**.

| Verification Metric | Verified State | Evidence |
| :--- | :--- | :--- |
| Permanent Archival DOI | `10.5281/zenodo.24278751` | [Zenodo Record](https://doi.org/10.5281/zenodo.24278751) |
| Lean 4 Toolchain | `leanprover/lean4:v4.35.0` | [`lean-toolchain`](lean-toolchain) |
| Lake Build Targets | `9,091 / 9,091` passing (`exit 0`) | [CI Run #44567866016](https://github.com/princeanand099/grasgreenbergbrocard/actions/runs/44567866016/job/135714460223) |
| Audited Main Declarations | `42` theorems, propositions, and lemmas | [`AuditAxioms.lean`](GrasGreenbergBrocard/AuditAxioms.lean) |
| Standard-Axioms-Only Declarations | `8` core results (`0` external axioms) | [CI Log `56e1d6d4`](https://github.com/princeanand099/grasgreenbergbrocard/commit/56e1d6d4bca09efcde64400ed0b5fb3fe1c5e309) |
| `sorry` / `admit` / `sorryAx` | `0` | [CI Log `56e1d6d4`](https://github.com/princeanand099/grasgreenbergbrocard/commit/56e1d6d4bca09efcde64400ed0b5fb3fe1c5e309) |
| `native_decide` / `Lean.trustCompiler` | `0` | [CI Log `56e1d6d4`](https://github.com/princeanand099/grasgreenbergbrocard/commit/56e1d6d4bca09efcde64400ed0b5fb3fe1c5e309) |
| Adversarial Audit Hardening | Merged (`d22839cc`, `0def862b`) | [PR #7](https://github.com/princeanand099/grasgreenbergbrocard/pull/7), [PR #8](https://github.com/princeanand099/grasgreenbergbrocard/pull/8) |

## 2. Headline Formalized Results

| Manuscript Result | Lean Declaration (`GrasGreenbergBrocard.*`) | Module |
| :--- | :--- | :--- |
| **Theorem 1.1(i)–(iii)** (Pell index collapse $k \in \{1,2\}$, regulator quantization, core distinctness) | `pell_index_collapse_large`, `fundamental_regulator_quantization`, `q_n_ne_of_solutions` | `Thm1_1Collapse.lean` |
| **Theorem 1.2(i)–(iii)** (Leopoldt–Coates valuation law, split-prime Iwasawa invariants, conditional finiteness) | `thm_1_2_part1_valuation_law`, `thm_1_2_part2_split_primes`, `thm_1_2_part3_conditional_finiteness` | `Thm1_2Iwasawa.lean` |
| **Theorem 1.3(i)** ($k = 2$ gap $n_2 - n_1 > n_1^{1-\varepsilon}$ & $O_\varepsilon(N^\varepsilon)$ counting bound) | `thm_1_3_part1_k2_gap_and_counting` | `Thm6_4CapacityDiamond.lean` |
| **Theorem 1.3(ii)** (Global & Brocard $O_\varepsilon(N^{6/7+\varepsilon})$ and depressed degree-gap bounds) | `thm_1_3_part2_global_6_7`, `thm_1_3_part2_brocard_6_7`, `thm_1_3_part2_degree_gap_bounds` | `Thm1_3Part2Counting.lean` |
| **Theorem 2.5** (Second-order valuation parity $\Delta(n)$ & $S_{\mathrm{odd}}(n)$) | `Delta_parity_second_order`, `S_odd_asymptotic` | `ValuationParityThm.lean` |
| **Theorem 4.2(i)–(iii)** (Euclidean lock, dual quartic structure, midpoint core bounds) | `thm_4_2_part1_euclidean_lock`, `thm_4_2_part2_dual_quartic`, `thm_4_2_part3_midpoint_core_bounds` | `Thm4_2QuarticCores.lean` |
| **Theorem 5.2(i)–(ii)** (Cross-symmetry identity & Davenport effective core bounds) | `thm_5_2_part1_cross_symmetry` *(0 external axioms)*, `thm_5_2_part2_effective_cores` | `Thm5_2EffectiveCores.lean` |
| **Theorem 5.3(i)–(ii)** (Rédei–Reichardt cohomology $4$-rank & dual quartic pairing) | `thm_5_3_part1_cohomology_4rank`, `thm_5_3_part2_dual_quartic` | `Thm5_3RedeiCohomology.lean` |
| **Theorem 6.4(a)–(b)** (Universal Capacity Diamond & Rankin polarization concentration) | `thm_6_4_capacity_diamond`, `thm_6_4_polarization_concentration` | `Thm6_4CapacityDiamond.lean`, `Thm6_4PolarizationConcentration.lean` |
| **Theorem 8.1(i)–(ii)** (Frey elliptic curves $\mathcal{E}_n, F_n^{(2)}$, CM reduction, $abc$ & Hall bounds) | `thm_8_1_part1_frey_E`, `thm_8_1_part2_level2_cm_reduction`, `thm_8_1_part2_abc_and_hall_bounds` | `Thm8_1FreyCurves.lean` |
| **Theorem 8.2** (Effective Tatuzawa class number explosion & narrow $2^J$-rank dichotomy) | `thm_8_2_tatuzawa_and_narrow_2J_rank` | `Thm8_2TatuzawaClassGroup.lean` |

## 3. Repository Architecture

The root file [`GrasGreenbergBrocard.lean`](GrasGreenbergBrocard.lean) imports all sections in dependency order and concludes with `GrasGreenbergBrocard.AuditAxioms`:

| Section | Modules (`GrasGreenbergBrocard/`) | Scope |
| :--- | :--- | :--- |
| Core Foundations | `Basic`, `PellFundamental`, `ChebyshevLucas` | Square-free core $q_n$, fundamental Pell solutions, Chebyshev–Lucas recurrences |
| Section 2 (Analytic) | `ExternalAxiomsAnalytic`, `ValuationParityLayer`, `ValuationParityDigits`, `ValuationParityVaaler`, `ExpSumBounds`, `ValuationParityThmHelpers`, `ValuationParityThmPart1`, `ValuationParityThmCollar`, `ValuationParityThmInterCollar`, `ValuationParityThm` | $\log q_n$ asymptotics, Vaaler extremal polynomials, dyadic prime exponential sums, $\Delta(n)$, $S_{\mathrm{odd}}(n)$ |
| Section 2 (Modular) | `ExpSumBoundsMod`, `VaalerMod`, `ValuationParityModWeight`, `ValuationParityModCollar`, `ValuationParityModInterCollar`, `ValuationParityMod` | Multi-modulus power-band equidistribution |
| Section 3 & Thms 1.1–1.2 | `ExternalAxiomsSec3`, `Thm1_1Collapse`, `Thm1_2Iwasawa` | Pell collapse, regulator quantization, core distinctness, Iwasawa invariants |
| Section 4 | `ExternalAxiomsSec4`, `Picard2Torsion`, `Prop4_1SmoothBiquad`, `Thm4_2QuarticCores` | Picard $2$-torsion, smooth biquadratics, Euclidean lock, quartic cores |
| Section 5 | `ExternalAxiomsSec5`, `Prop5_1MidpointBias`, `Thm5_2EffectiveCores`, `Thm5_3RedeiCohomology` | Continued-fraction midpoint symmetry/bias, Davenport bounds, Rédei cohomology |
| Section 6 & Thm 1.3(i) | `Prop6_1FourGCD`, `Prop6_2ConsecutiveSquareShift`, `Lem6_3ParityFlipOsc`, `Lem6_3ParityFlip`, `Thm6_4CapacityDiamond`, `Thm6_4PolarizationConcentration` | Four-GCD $\mathrm{SL}_2$ structure, square-shift exclusions, honest collar-excised Vaaler parity-flip, capacity diamond, polarization concentration |
| Section 7 & Thm 1.3(ii) | `ExternalAxiomsSec7`, `Sec7PadeWronskian`, `Thm1_3Part2Counting` | Pigeonhole Siegel lemma, Padé polynomials, Puiseux independence, support-reduced Wronskian, Tables 1–2, $6/7$ counting bounds |
| Section 8 | `ExternalAxiomsSec8`, `Thm8_1FreyCurves`, `Thm8_2TatuzawaClassGroup` | Frey curves, CM reduction, $abc$/Hall bounds, Tatuzawa narrow $2^J$-rank |
| Automated Audit | `AuditAxioms` | Machine-checked `#print axioms` closure for all 42 main declarations |

## 4. Trust Base and Verification Protocol

Every external assumption in this repository is a standard, peer-reviewed result from number theory or arithmetic geometry, isolated exclusively inside five `ExternalAxioms*.lean` files (`ExternalAxiomsAnalytic`, `ExternalAxiomsSec3`, `ExternalAxiomsSec5`, `ExternalAxiomsSec7`, `ExternalAxiomsSec8`). **Zero manuscript-owned results are axiomatized.**

Following two adversarial audits ([PR #7](https://github.com/princeanand099/grasgreenbergbrocard/pull/7) and [PR #8](https://github.com/princeanand099/grasgreenbergbrocard/pull/8)):
- `vaughan_van_der_corput_prime_sum` explicitly requires `IsPrimeSubinterval P I` and `AntitoneOn w (Set.Icc P (2 * P))`, and `Lem6_3ParityFlipOsc.lean` proves `lem_6_3_osc_bound_honest` using exclusively the monotone weight $w(t) = 1/t$.
- `bpz_dyadic_cluster_elimination` is bound to `IsPolyFactSol` and `HasDepressedDegreeGap` (with `brocard_poly_depressed_gap` proved internally).
- Iwasawa and Tatuzawa axioms are scoped strictly to `canonicalRealQuadIwasawa` and `canonicalRealQuadClassGroup`.

### Local Reproduction

```bash
git clone https://github.com/princeanand099/grasgreenbergbrocard.git
cd grasgreenbergbrocard
lake exe cache get
lake build
lake build GrasGreenbergBrocard.AuditAxioms
```

For full third-party audit commands (including `leanchecker` and source-level checks), see [`AUDIT.md`](AUDIT.md).

## 5. Documentation and Audit Records

- [`AUDIT.md`](AUDIT.md): Step-by-step independent verification and kernel audit protocol.
- [`EXTERNAL_AXIOMS.md`](EXTERNAL_AXIOMS.md): Complete literature-cited register of all external axioms.
- [`THEOREM_CORRESPONDENCE.md`](THEOREM_CORRESPONDENCE.md): Exhaustive manuscript-to-Lean correspondence and `#print axioms` classification.
- [`MATHEMATICAL_CORRECTIONS.md`](MATHEMATICAL_CORRECTIONS.md): Formal audit record and synchronized manuscript refinements.
- [`PROGRESS.md`](PROGRESS.md): Milestone and CI verification ledger.
- [`formalization.yaml`](formalization.yaml): Machine-readable provenance and theorem manifest.

## 6. How to Cite

Citation metadata is provided in [`CITATION.cff`](CITATION.cff) (supported natively by GitHub's *Cite this repository* menu) and archived on Zenodo at [`10.5281/zenodo.24278751`](https://doi.org/10.5281/zenodo.24278751):

```bibtex
@article{Anand2026Brocard,
  author  = {Prince Anand},
  title   = {Arithmetic Structure and Counting Bounds for the {Brocard--Ramanujan} Equation},
  year    = {2026},
  month   = nov,
  doi     = {10.5281/zenodo.24278751},
  url     = {https://doi.org/10.5281/zenodo.24278751}
}

@software{Anand2026BrocardLean4,
  author  = {Prince Anand},
  title   = {Formal Verification of Arithmetic Structure and Counting Bounds for the {Brocard--Ramanujan} Equation ({Lean} 4)},
  year    = {2026},
  month   = nov,
  doi     = {10.5281/zenodo.24278751},
  url     = {https://github.com/princeanand099/grasgreenbergbrocard},
  license = {Apache-2.0}
}
```
