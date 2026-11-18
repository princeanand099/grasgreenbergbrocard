# Gras–Greenberg–Brocard Lean 4 Formalization

Lean 4 formalization of the manuscript *Arithmetic Structure, Iwasawa Invariants, and Unconditional Counting Bounds for Brocard's Problem* (`brocard_arithmetic_structure_and_counting_bounds.tex`).

## Toolchain & Build

- **Lean / Mathlib**: Lean 4 (`lean-toolchain`), Mathlib v4.35.0 (`lake-manifest.json`, `lakefile.toml`).
- **Build command**:
  ```bash
  lake build
  ```
- **CI**: GitHub Actions (`.github/workflows/`) builds the full project and logs output to the `ci-logs` branch.

## Module Organization

### Foundational & Section 2 (Valuation-Parity Equidistribution of Factorials)
- `GrasGreenbergBrocard/Basic.lean`: Core definitions (`Podd`, `Peven`, `q_n`, `s_n`, `Sodd`, `Seven`, `Dparity`, `pell_index`).
- `GrasGreenbergBrocard/ExternalAxiomsAnalytic.lean`: External analytic axioms for Section 2 (van der Corput $k$-th derivative exponential sum bounds, Mertens's asymptotic, Vaaler's trigonometric polynomial approximation).
- `GrasGreenbergBrocard/ValuationParityLayer.lean`, `ValuationParityDigits.lean`, `ValuationParityVaaler.lean`, `ExpSumBounds.lean`: Base-$p$ digit expansion, Vaaler Fourier expansion, and exponential sum bounds.
- `GrasGreenbergBrocard/ValuationParityThmHelpers.lean`, `ValuationParityThmPart1.lean`, `ValuationParityThmCollar.lean`, `ValuationParityThmInterCollar.lean`, `ValuationParityThm.lean`: Proof of Theorem 2.5(i)–(ii) (`Delta_parity_isLittleO_mul_log`, `S_odd_asymptotic`, `S_even_asymptotic`).
- `GrasGreenbergBrocard/ExpSumBoundsMod.lean`, `VaalerMod.lean`, `ValuationParityModWeight.lean`, `ValuationParityModCollar.lean`, `ValuationParityModInterCollar.lean`, `ValuationParityMod.lean`: Proof of Theorem 2.5(iii) (`multi_modulus_power_band_equidistribution`).

### Section 3 (Chebyshev–Lucas Valuation Absorption & Theorems 1.1–1.2)
- `GrasGreenbergBrocard/ExternalAxiomsSec3.lean`: External axioms for Section 3 (Breusch 1932, Rosser–Schoenfeld 1962, Stirling remainder, Erdős–Selfridge 1975, Nagura 1952, Leopoldt/Coates/Taya/Iwasawa package `RealQuadIwasawaInvariants`).
- `GrasGreenbergBrocard/ChebyshevLucas.lean`: Lemma 3.2 (`lucasY_eq_mul_chebyshevU`, `gcd_pell_chebyshevU_dvd`, `padicValInt_chebyshevU`, `padicValNat_pell_absorption`).
- `GrasGreenbergBrocard/PellFundamental.lean`: Lemma 3.1 (`q_n_has_prime_mod4`, `neg_pell_no_int_sol`, `log_q_n_gt_point4`, `pell_index_upper_bound`, `log_s_n_asymptotic`).
- `GrasGreenbergBrocard/Thm1_1Collapse.lean`: Theorem 1.1 (`known_k4`, `known_k5`, `known_k7`, `pell_index_collapse_large`, `fundamental_regulator_quantization`, `q_n_ne_of_solutions`).
- `GrasGreenbergBrocard/Picard2Torsion.lean`: Picard 2-torsion and $k=1,2$ midpoint structure (`J_n_sq_eq`, `J_n_principal_iff_k_eq_2`, `k_eq_1_picard_identity`, `second_stage_nonprincipal_k_eq_2`).
- `GrasGreenbergBrocard/Thm1_2Iwasawa.lean`: Theorem 1.2(i)–(iii) (`thm_1_2_part1_valuation_law`, `thm_1_2_part2_split_primes`, `thm_1_2_part3_conditional_finiteness`).

### Section 4 (Arithmetic Structure of the Critical Regime $k = 2$)
- `GrasGreenbergBrocard/ExternalAxiomsSec4.lean`: External axioms for Section 4 (Chebyshev $\vartheta(x) \sim x$ and Mertens's first theorem on odd primes).
- `GrasGreenbergBrocard/Prop4_1SmoothBiquad.lean`: Proposition 4.1(i)–(ii) (`prop_4_1_part1`, `prop_4_1_part2`, smooth biquadratic / Diophantine structure for $k=2$).
- `GrasGreenbergBrocard/Thm4_2QuarticCores.lean`: Theorem 4.2(i)–(iii) (`thm_4_2_part1_quartic_law`, `thm_4_2_part1_euclidean_lock`, `thm_4_2_part2_dual_quartic`, `thm_4_2_part2_euclidean_locks`, `thm_4_2_part3_midpoint_core_bounds`, `thm_4_2_part3_mertens_bound`).

### Section 5 (The Fundamental Regime $k = 1$ and Rédei–Reichardt Cohomology)
- `GrasGreenbergBrocard/ExternalAxiomsSec5.lean`: External axioms for Section 5 (Perron §25 / Hardy–Wright Theorem 10.7.5 midpoint symmetry, Davenport Ch. 19 real character sum upper bound `davenport_real_char_half_band_upper`, and Gauss/Rédei–Reichardt narrow class group exact sequence `RedeiNarrowClassData`, `redei_reichardt_exact_sequence`).
- `GrasGreenbergBrocard/Prop5_1MidpointBias.lean`: Proposition 5.1(i)–(ii) (`eq_5_1_midpoint_decomp`, `psi_eval_upper_half`, `prop_5_1_part1_midpoint_bias`, `prop_5_1_part2_cross_symmetry`).
- `GrasGreenbergBrocard/Thm5_2EffectiveCores.lean`: Theorem 5.2(i)–(ii) (`A_star5`, `B_star5`, `Delta_parity_odd`, `B_part`, `Z_star`, `thm_5_2_part1_bipartition`, `thm_5_2_part1_cross_symmetry`, `thm_5_2_part1_radical_bounds`, `delta2Mid_ne_two`, `thm_5_2_part2_effective_cores`, `thm_5_2_part2_pell_pm2_insoluble`).
- `GrasGreenbergBrocard/Thm5_3RedeiCohomology.lean`: Theorem 5.3(i)–(ii) (`thm_5_3_part1_cohomology_4rank`, `PevenPlus`, `PevenMinus`, `W_split`, `B_tilde`, `A_plus_star`, `thm_5_3_part2_inert_absorption`, `thm_5_3_part2_dual_quartic`).

## Documentation & Audit Records

- [`EXTERNAL_AXIOMS.md`](EXTERNAL_AXIOMS.md): Register of all external peer-reviewed axioms (zero manuscript-owned results).
- [`THEOREM_CORRESPONDENCE.md`](THEOREM_CORRESPONDENCE.md): Manuscript-to-Lean correspondence and fidelity audit.
- [`MATHEMATICAL_CORRECTIONS.md`](MATHEMATICAL_CORRECTIONS.md): Mathematical correction and audit log.
- [`PROGRESS.md`](PROGRESS.md): Continuous formalization and CI status record.
- Manuscript & PDF: `brocard_arithmetic_structure_and_counting_bounds.tex`, `Brocard Arithmetic Structure And Counting Bounds.pdf`.
