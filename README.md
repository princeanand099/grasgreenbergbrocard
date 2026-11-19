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

### Section 6 (Pairwise $\mathrm{SL}_2(\mathbb{Z})$ Duality, Capacity Diamond, and Theorem 1.3(i))
- `GrasGreenbergBrocard/Prop6_1FourGCD.lean`: Proposition 6.1 (`X_gcd`, `Y_gcd`, `Z_gcd`, `W_gcd`, `P_ratio`, `prop_6_1_coprime_and_factorization`, `prop_6_1_sl2_duality`, `prop_6_1_bilinear_relations`).
- `GrasGreenbergBrocard/Prop6_2ConsecutiveSquareShift.lean`: Proposition 6.2(i)–(iii) (`prop_6_2_part1_square_ratio_gap`, `prop_6_2_part2_no_two_unit_solutions`, `prop_6_2_part3_no_small_square_ratio`).
- `GrasGreenbergBrocard/Lem6_3ParityFlipOsc.lean`, `GrasGreenbergBrocard/Lem6_3ParityFlip.lean`: Lemma 6.3(i)–(ii) (`lem_6_3_part1_parity_flip_factorization`, `lem_6_3_part2_oscillation_bounds`, `lem_6_3_part2_window_exclusion`).
- `GrasGreenbergBrocard/Thm6_4CapacityDiamond.lean`: Theorem 6.4(a) (`theta_weight`, `theta_eps_weight`, `log_ZW_and_XY_bounds`, `thm_6_4_capacity_diamond`), Theorem 1.3(i) (`thm_1_3_part1_k2_gap_and_counting`), and Proposition 6.2(iii) consecutive-square $k=2$ exclusion (`prop_6_2_part3_consecutive_squares_k2_exclusion`).
- `GrasGreenbergBrocard/Thm6_4PolarizationConcentration.lean`: Theorem 6.4(b) (`thm_6_4_polarization_concentration`, Rankin spherical cap Cauchy–Schwarz interval bound and $C_\varepsilon \eta^{-2} N^\varepsilon$ counting bound).

### Section 7 (Support-Reduced Padé–Wronskian Method & Theorem 1.3(ii))
- `GrasGreenbergBrocard/ExternalAxiomsSec7.lean`: External axioms for Section 7 (Bui–Pratt–Zaharescu 2023 Lemma 4.2 Taylor family, Siegel 1949 / BPZ 2023 support-reduced Wronskian non-vanishing, and BPZ 2023 Prop. 3.4 & §5 dyadic cluster elimination).
- `GrasGreenbergBrocard/Sec7PadeWronskian.lean`: Siegel's Lemma (`siegel_lemma_pigeonhole`), Lemma 7.1 (`lem_7_1_initial_pade_polynomials`), Lemma 7.2 (`lem_7_2_monomial_product_puiseux_indep`), Lemma 7.3 (`lem_7_3_support_reduced_wronskian`), and Lemma 7.4 (`gauss_leading_coeff_dvd_of_linear_factors`, `lem_7_4_leading_coeff_divisibility`).
- `GrasGreenbergBrocard/Thm1_3Part2Counting.lean`: Table 1 (`table1_m2_exact`–`table1_m5_exact`), Table 2 (`table2_nu3`–`table2_nu_large`), and Theorem 1.3(ii) (`thm_1_3_part2_global_6_7`, `thm_1_3_part2_brocard_6_7`, `thm_1_3_part2_degree_gap_bounds`).

### Section 8 (Elliptic Curve Realizations and Effective Class Group Bounds)
- `GrasGreenbergBrocard/ExternalAxiomsSec8.lean`: External axioms for Section 8 (Wiles 1995 / BCDT 2001 / Mazur 1978 / Kenku 1982 / Serre 1972 modularity & Galois surjectivity `frey_curve_modularity_and_galois`, Dirichlet CNF + Gauss genus theory `dirichlet_cnf_and_gauss_genus`, and Tatuzawa 1951 effective Siegel theorem `tatuzawa_effective_siegel`).
- `GrasGreenbergBrocard/Thm8_1FreyCurves.lean`: Theorem 8.1(i)–(ii) (`thm_8_1_part1_frey_E`, `thm_8_1_part2_level2_cm_reduction`, `thm_8_1_part2_abc_and_hall_bounds`).
- `GrasGreenbergBrocard/Thm8_2TatuzawaClassGroup.lean`: Theorem 8.2 (`hNonGen`, `thm_8_2_tatuzawa_and_narrow_2J_rank`).

## Documentation & Audit Records

- [`EXTERNAL_AXIOMS.md`](EXTERNAL_AXIOMS.md): Register of all external peer-reviewed axioms (zero manuscript-owned results).
- [`THEOREM_CORRESPONDENCE.md`](THEOREM_CORRESPONDENCE.md): Manuscript-to-Lean correspondence and fidelity audit.
- [`MATHEMATICAL_CORRECTIONS.md`](MATHEMATICAL_CORRECTIONS.md): Mathematical correction and audit log.
- [`PROGRESS.md`](PROGRESS.md): Continuous formalization and CI status record.
- Manuscript & PDF: `brocard_arithmetic_structure_and_counting_bounds.tex`, `Brocard Arithmetic Structure And Counting Bounds.pdf`.
