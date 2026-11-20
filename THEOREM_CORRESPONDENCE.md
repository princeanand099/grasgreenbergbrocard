# Theorem Correspondence and Kernel Axiom Audit

Mapping between **Prince Anand**, *Arithmetic Structure and Counting Bounds for the Brocard–Ramanujan Equation* ([DOI: 10.5281/zenodo.24278751](https://doi.org/10.5281/zenodo.24278751)) and the Lean 4 (`v4.35.0`) formalization in `GrasGreenbergBrocard`.

Every declaration listed below is checked by `GrasGreenbergBrocard/AuditAxioms.lean` (**78** `#print axioms` declarations, **0** `sorryAx`, **0** `Lean.ofReduceBool`/`Lean.trustCompiler`). Every external-axiom entry matches the exact Lean 4 kernel `#print axioms` closure (in addition to Lean's standard logical axioms `propext`, `Classical.choice`, `Quot.sound`).

## Section 2 — Valuation Parity & Prime Exponential Sums

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Eq. (2.1) / Layer decomposition ($\log q_n$, $\log s_n$) | `log_q_n_asymptotic`, `log_s_n_asymptotic` | `ValuationParityLayer.lean`, `PellFundamental.lean` | `de_la_vallee_poussin_theta` (`log_s_n_asymptotic`: plus `stirling_log_factorial_remainder`) |
| Lemma 2.3 (Vaaler approximation) | `vaaler_parity_approx` | `ValuationParityVaaler.lean` | `vaaler_extremal_polynomials` |
| Lemma 2.4 (Prime exponential sum bounds) | `prime_exp_sum_bounds` | `ExpSumBounds.lean` | `vaughan_van_der_corput_prime_sum` |
| Theorem 2.5(i) (Second-order parity asymptotic $\Delta(n)$) | `Delta_parity_second_order` | `ValuationParityThm.lean` | `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Theorem 2.5(ii) ($S_{\mathrm{odd}}(n)$ asymptotic) | `S_odd_asymptotic` | `ValuationParityThm.lean` | `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Theorem 2.5(iii) (Multi-modulus equidistribution) | `multi_modulus_power_band_equidistribution` | `ValuationParityMod.lean` | `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |

## Section 3 — Theorems 1.1 & 1.2 (Pell Index Collapse & Iwasawa Theory)

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Known solutions $k(4)=1, k(5)=1, k(7)=2$ | `known_k4`, `known_k5`, `known_k7` | `Thm1_1Collapse.lean` | **Standard Lean axioms only** (`0` external) |
| Lemma 3.1(i) (Negative Pell insolubility $x^2 - q_n y^2 = -1$) | `neg_pell_no_rat_sol` | `PellFundamental.lean` | `breusch_bertrand_mod4` |
| Lemma 3.1(i) ($\log q_n > 0.4n$, $\log \varepsilon_n > 0.2n$, $k < 2.5 \log n$ for $n \ge 8$) | `log_q_n_gt_point4_ge8`, `log_fund_pell_gt_point2_ge8`, `pell_index_upper_bound_ge8` | `PellFundamental.lean` | `rosser_schoenfeld_theta_diff` |
| Theorem 1.1(i) (Pell index collapse $k \in \{1, 2\}$) | `pell_index_collapse_large` | `Thm1_1Collapse.lean` | `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `rosser_schoenfeld_theta_diff`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Theorem 1.1(ii) (Fundamental regulator quantization) | `fundamental_regulator_quantization` | `Thm1_1Collapse.lean` | `stirling_log_factorial_remainder` |
| Theorem 1.1(iii) (Distinct squarefree cores) | `q_n_ne_of_solutions` | `Thm1_1Collapse.lean` | `erdos_selfridge_consecutive_product_not_square` |
| Proposition 3.3 (Ideal/ring identities for $k = 1, 2$ in $\mathbb{Z}[\sqrt{-q_n}]$) | `J_n_principal_iff_k_eq_2`, `k_eq_1_picard_identity`, `second_stage_nonprincipal_k_eq_2` | `Picard2Torsion.lean` | `breusch_bertrand_mod4` (note: formalizes the concrete ideal/element identities in `Zsqrtd (-q_n)` without constructing abstract $\mathrm{Pic}(\mathcal{O}_n^-)$) |
| Sec. 3.3 (Nagura band prime, unnumbered) | `nagura_prime_in_band` | `Thm1_2Iwasawa.lean` | `nagura_prime_in_interval` |
| Eq. (3.6) ($p$-adic regulator valuation from $n!+1=m^2$) | `thm_1_2_eq_3_6_regulator_valuation` | `Thm1_2Iwasawa.lean` | `canonicalRealQuadIwasawa`, `erdos_selfridge_consecutive_product_not_square`, `padic_log_regulator_pell_power` |
| Sec. 3.3 (Wieferich congruence $u^{p^2-1} \equiv 1 \pmod{p^2 \mathbb{Z}[\sqrt{q_n}]}$) | `thm_1_2_wieferich_congruence` | `Thm1_2Iwasawa.lean` | **Standard Lean axioms only** (`0` external) |
| Finite verification ($1 \le n < 116$, $n \notin \{4,5,7\}$) | `brocard_small_solutions_lt_116` | `Thm1_2Iwasawa.lean` | **Standard Lean axioms only** (`propext`, `Quot.sound`; pure kernel `decide`) |
| Theorem 1.2(i) (Valuation law & $\lambda_p^* \ge 1$) | `thm_1_2_part1_valuation_law` | `Thm1_2Iwasawa.lean` | `canonicalRealQuadIwasawa`, `erdos_selfridge_consecutive_product_not_square`, `iwasawa_main_conjecture_free_rank`, `leopoldt_coates_valuation_law`, `padic_log_regulator_pell_power` |
| Theorem 1.2(ii) (Split-prime unramified Iwasawa module) | `thm_1_2_part2_split_primes` | `Thm1_2Iwasawa.lean` | `canonicalRealQuadIwasawa`, `erdos_selfridge_consecutive_product_not_square`, `ozaki_taya_split_prime_iwasawa`, `padic_log_regulator_pell_power` |
| Theorem 1.2(iii) (Conditional finiteness, $n \ge 116$ & complete $n \ge 1$ branches (a)–(c)) | `thm_1_2_part3_conditional_finiteness`, `thm_1_2_part3_complete_finiteness` | `Thm1_2Iwasawa.lean` | `canonicalRealQuadIwasawa`, `erdos_selfridge_consecutive_product_not_square`, `iwasawa_main_conjecture_free_rank`, `leopoldt_coates_valuation_law`, `ozaki_taya_split_prime_iwasawa`, `padic_log_regulator_pell_power`, `rosser_schoenfeld_theta_diff` |

## Section 4 — Smooth Biquadratic Geometry & Quartic Cores

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Prop. 4.1(i) (Smoothness & raw/asymptotic eq. 4.4) | `prop_4_1_part1`, `prop_4_1_part1_asymptotic` | `Prop4_1SmoothBiquad.lean` | `breusch_bertrand_mod4` (`asymptotic`: plus `de_la_vallee_poussin_theta`) |
| Prop. 4.1(ii) (Biquadratic splitting & Fermat-quotient lock) | `prop_4_1_part2` | `Prop4_1SmoothBiquad.lean` | `breusch_bertrand_mod4` |
| Theorem 4.2(i) (Quartic law & Euclidean lock) | `thm_4_2_part1_quartic_law`, `thm_4_2_part1_euclidean_lock` | `Thm4_2QuarticCores.lean` | `breusch_bertrand_mod4` (`euclidean_lock`: plus Section 2 analytic axioms) |
| Theorem 4.2(ii) (Dual quartic & second-stage Euclidean locks) | `thm_4_2_part2_dual_quartic`, `thm_4_2_part2_euclidean_locks` | `Thm4_2QuarticCores.lean` | `breusch_bertrand_mod4` (`euclidean_locks`: plus Section 2 analytic axioms) |
| Theorem 4.2(iii) (Midpoint core bounds & Mertens $\log p_{t+1}$ bound) | `thm_4_2_part3_midpoint_core_bounds`, `thm_4_2_part3_mertens_bound` | `Thm4_2QuarticCores.lean` | `breusch_bertrand_mod4` + Section 2 analytic axioms (`mertens_bound`: plus `mertens_first_theorem_odd_primes`) |

## Section 5 — Midpoint Bias, Effective Cores & Rédei Cohomology

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Prop. 5.1(i)–(ii) (CF midpoint symmetry & valuation bias) | `prop_5_1_part1`, `prop_5_1_part2_bias` | `Prop5_1MidpointBias.lean` | `breusch_bertrand_mod4`, `perron_cf_midpoint_symmetry` (`bias`: plus `de_la_vallee_poussin_theta`) |
| Theorem 5.2(i) (Cross-symmetry identity & radical bounds) | `thm_5_2_part1_cross_symmetry`, `thm_5_2_part1_radical_bounds` | `Thm5_2EffectiveCores.lean` | `cross_symmetry`: **0 external**; `radical_bounds`: Section 2 analytic axioms |
| Theorem 5.2(ii) (Effective core bounds & Pell $\pm 2$ insolubility) | `thm_5_2_part2_effective_cores`, `thm_5_2_part2_pell_pm2_insoluble` | `Thm5_2EffectiveCores.lean` | `davenport_real_char_half_band_upper`, `rosser_schoenfeld_theta_diff` (`pell_pm2`: plus `breusch_bertrand_mod4`) |
| Theorem 5.3(i) (Midpoint norm cocycle non-vanishing & kernel membership) | `yMidVec_ne_zero`, `yMidVec_mem_redeiKernel` | `Thm5_3RedeiCohomology.lean` | **Standard Lean axioms only** (`0` external) |
| Theorem 5.3(i) (Rédei cohomology 4-rank over repaired `ramPrimes n` & 2-adic Hilbert row) | `thm_5_3_part1_cohomology_4rank` | `Thm5_3RedeiCohomology.lean` | `canonicalRealQuadRedei`, `redei_reichardt_exact_sequence` |
| Theorem 5.3(ii) (Inert absorption & dual quartic) | `thm_5_3_part2_inert_absorption`, `thm_5_3_part2_dual_quartic` | `Thm5_3RedeiCohomology.lean` | `breusch_bertrand_mod4` |

## Section 6 — Theorem 1.3(i) ($k = 2$ Gap & Counting Bounds)

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Prop. 6.1 (SL$_2$, $\mathbb{Z}[\sqrt{P}]$, characters & Quadrant IV) | `prop_6_1_part1_sl2_and_four_squares`, `prop_6_1_part2_zsqrtd_identities`, `prop_6_1_part3_characters_and_quadrant_iv` | `Prop6_1FourGCD.lean` | **Standard Lean axioms only** (`0` external) |
| Prop. 6.2(i)–(iii) ($n=4$ boundary, equipartition, square-shift & consecutive-squares exclusions) | `prop_6_2_part1_n4_boundary`, `prop_6_2_part2_consecutive_equipartition`, `prop_6_2_part3_square_shift_exclusions`, `prop_6_2_part3_consecutive_squares_k2_exclusion` | `Prop6_2ConsecutiveSquareShift.lean`, `Thm6_4CapacityDiamond.lean` | `part1`, `part3_square_shift`: **0 external**; `part2`, `consecutive_squares_k2`: Section 2 analytic axioms |
| Lemma 6.3 (Uniform parity flip) | `lem_6_3_parity_flip_uniform` | `Lem6_3ParityFlip.lean` | `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Theorem 6.4(a)–(b) & Theorem 1.3(i) | `thm_6_4_capacity_diamond`, `thm_1_3_part1_k2_gap_and_counting`, `thm_6_4_polarization_concentration` | `Thm6_4CapacityDiamond.lean`, `Thm6_4PolarizationConcentration.lean` | `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |

## Section 7 — Support-Reduced Padé–Wronskian & Theorem 1.3(ii)

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Siegel's Lemma, Lemma 7.1, Eq. (7.1) Depression, Eq. (7.17) Cluster Reduction, Exponent Equivalence | `siegel_lemma_pigeonhole`, `lem_7_1_initial_pade_polynomials`, `poly_has_depressed_gap_two`, `pigeonhole_cluster_reduction`, `pade_chi_lt_ratio_iff_theta_lt` | `Sec7PadeWronskian.lean`, `Sec7ClusterReduction.lean`, `Thm1_3Part2Counting.lean` | **Standard Lean axioms only** (`0` external) |
| Algebraic/abstract cores of Lemmas 7.2, 7.3, 7.4 | `lem_7_2_monomial_product_puiseux_indep`, `lem_7_3_support_reduced_wronskian`, `lem_7_4_denominator_clearing`, `depressed_poly_asymptotic_core` | `Sec7PadeWronskian.lean` | **Standard Lean axioms only** (`0` external; note: abstract/algebraic wrappers — analytic Puiseux/ODE/Cauchy-Leibniz steps are packaged in the 3 Section 7 axioms below) |
| Sec. 7.4 Dyadic cluster elimination, Global $N^{6/7+\varepsilon}$ (all $s \in \mathbb{Z}\setminus\{0\}$), Table 1 ($m=2,3,4,5$), Table 2 ($\nu = 3,4,5,\ge 6,\ge 25$) | `dyadic_cluster_elimination_proved`, `thm_1_3_part2_global_6_7`, `thm_1_3_part2_global_6_7_general`, `thm_1_3_part2_brocard_6_7`, `thm_1_3_part2_table1_bounds`, `thm_1_3_part2_degree_gap_bounds` | `Thm1_3Part2Counting.lean` | `bpz_cauchy_leibniz_pade_eval`, `canonicalMonomialTaylorFamily`, `canonicalSupportWronskian` |

## Section 8 — Frey Curves & Tatuzawa Class Group Bounds

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Theorem 8.1(i) (Frey curve $\mathcal{E}_n$, bound to `freyCurveE m : WeierstrassCurve ℤ`) | `thm_8_1_part1_frey_E` | `Thm8_1FreyCurves.lean` | `frey_E_modularity` |
| Theorem 8.1(ii) (Frey curve $F_n^{(2)}$, bound to `freyCurveF2 X₁ : WeierstrassCurve ℤ`) | `thm_8_1_part2_level2_cm_reduction` | `Thm8_1FreyCurves.lean` | `breusch_bertrand_mod4`, `frey_F2_modularity_and_galois` |
| Theorem 8.1(ii) ($abc$-quality & Hall bounds) | `thm_8_1_part2_abc_and_hall_bounds` | `Thm8_1FreyCurves.lean` | `breusch_bertrand_mod4`, `de_la_vallee_poussin_theta` |
| Theorem 8.2 (Tatuzawa effective Siegel & narrow $2^J$-rank) | `thm_8_2_tatuzawa_and_narrow_2J_rank` | `Thm8_2TatuzawaClassGroup.lean` | `canonicalRealQuadClassGroup`, `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `erdos_selfridge_consecutive_product_not_square`, `pnt_pi_asymptotic`, `tatuzawa_effective_siegel` |
