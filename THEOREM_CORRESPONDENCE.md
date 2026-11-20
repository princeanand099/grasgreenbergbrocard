# Theorem Correspondence

Mapping between **Prince Anand**, *Arithmetic Structure and Counting Bounds for the Brocard–Ramanujan Equation* ([DOI: 10.5281/zenodo.24278751](https://doi.org/10.5281/zenodo.24278751)) and the Lean 4 (`v4.35.0`) formalization in `GrasGreenbergBrocard`.

Every declaration listed below is checked by `GrasGreenbergBrocard/AuditAxioms.lean` (59 `#print axioms` declarations, zero `sorryAx`, zero `native_decide`).

## Section 2 — Valuation Parity & Prime Exponential Sums

| Manuscript Result | Lean 4 Declaration | File | External Axioms Used |
| :--- | :--- | :--- | :--- |
| Eq. (2.1) / Layer decomposition | `log_q_n_asymptotic` | `ValuationParityLayer.lean` | `de_la_vallee_poussin_theta`, `chebyshev_pi_upper`, `pnt_pi_asymptotic`, `mertens_first_theorem` |
| Lemma 2.1 (Vaaler approximation) | `vaaler_parity_approx` | `ValuationParityVaaler.lean` | `vaaler_extremal_polynomials` |
| Prop. 2.2 (Prime exponential sum bounds) | `prime_exp_sum_bounds` | `ExpSumBounds.lean` | `vaughan_van_der_corput_prime_sum` |
| Thm. 2.3 (Second-order parity asymptotic) | `Delta_parity_second_order`, `S_odd_asymptotic` | `ValuationParityThm.lean` | Sec. 2 analytic axioms |
| Prop. 2.4 (Multi-modulus equidistribution) | `multi_modulus_power_band_equidistribution` | `ValuationParityMod.lean` | Sec. 2 analytic axioms |

## Section 3 — Theorems 1.1 & 1.2 (Pell Index Collapse & Iwasawa Theory)

| Manuscript Result | Lean 4 Declaration | File | External Axioms Used |
| :--- | :--- | :--- | :--- |
| Known solutions $k(4)=1, k(5)=1, k(7)=2$ | `known_k4`, `known_k5`, `known_k7` | `Thm1_1Collapse.lean` | Standard Lean axioms only |
| Theorem 1.1(i) (Pell index collapse $k \in \{1, 2\}$) | `pell_index_collapse_large` | `Thm1_1Collapse.lean` | Sec. 2 analytic + `rosser_schoenfeld_theta_diff`, `stirling_log_factorial_remainder`, `erdos_selfridge_consecutive_product_not_square` |
| Theorem 1.1(ii) (Fundamental regulator quantization) | `fundamental_regulator_quantization` | `Thm1_1Collapse.lean` | Same as above |
| Theorem 1.1(iii) (Distinct squarefree cores) | `q_n_ne_of_solutions` | `Thm1_1Collapse.lean` | `breusch_bertrand_mod4`, `erdos_selfridge_consecutive_product_not_square` |
| Prop. 3.2 (Picard 2-torsion characterization) | `J_n_principal_iff_k_eq_2` | `Picard2Torsion.lean` | Standard Lean axioms only |
| Lemma 3.3 (Nagura band prime) | `nagura_prime_in_band` | `Thm1_2Iwasawa.lean` | `nagura_prime_in_interval` |
| Eq. (3.6) ($p$-adic regulator valuation from $n!+1=m^2$) | `thm_1_2_eq_3_6_regulator_valuation` | `Thm1_2Iwasawa.lean` | `erdos_selfridge_consecutive_product_not_square`, `canonicalRealQuadIwasawa`, `padic_log_regulator_pell_power` |
| Finite verification ($1 \le n < 116$, $n \notin \{4,5,7\}$) | `brocard_small_solutions_lt_116` | `Thm1_2Iwasawa.lean` | Standard Lean axioms only (pure kernel `decide`, 112 modular witnesses) |
| Theorem 1.2(i) (Valuation law & $\lambda_p^* \ge 1$) | `thm_1_2_part1_valuation_law` | `Thm1_2Iwasawa.lean` | `thm_1_2_eq_3_6_regulator_valuation` + `leopoldt_coates_valuation_law`, `iwasawa_main_conjecture_free_rank` |
| Theorem 1.2(ii) (Split-prime unramified Iwasawa module) | `thm_1_2_part2_split_primes` | `Thm1_2Iwasawa.lean` | `thm_1_2_eq_3_6_regulator_valuation` + `ozaki_taya_split_prime_iwasawa` |
| Theorem 1.2(iii) (Conditional finiteness) | `thm_1_2_part3_conditional_finiteness`, `thm_1_2_part3_complete_finiteness` | `Thm1_2Iwasawa.lean` | Sec. 3 Iwasawa axioms + `nagura_prime_in_interval`, `rosser_schoenfeld_theta_diff`, `stirling_log_factorial_remainder` |

## Section 4 — Smooth Biquadratic Geometry & Quartic Cores

| Manuscript Result | Lean 4 Declaration | File | External Axioms Used |
| :--- | :--- | :--- | :--- |
| Prop. 4.1(i)–(ii) | `prop_4_1_part1`, `prop_4_1_part2` | `Prop4_1SmoothBiquad.lean` | Standard Lean axioms only |
| Theorem 4.2(i)–(iii) (Euclidean lock, dual quartics, cores) | `thm_4_2_part1_euclidean_lock`, `thm_4_2_part2_dual_quartic`, `thm_4_2_part3_midpoint_core_bounds` | `Thm4_2QuarticCores.lean` | Standard Lean axioms only |
| Theorem 4.2(iii) (Mertens core bound) | `thm_4_2_part3_mertens_bound` | `Thm4_2QuarticCores.lean` | `mertens_first_theorem_odd_primes` |

## Section 5 — Midpoint Bias, Effective Cores & Rédei Cohomology

| Manuscript Result | Lean 4 Declaration | File | External Axioms Used |
| :--- | :--- | :--- | :--- |
| Prop. 5.1(i)–(ii) (Midpoint bias) | `prop_5_1_part1`, `prop_5_1_part2_bias` | `Prop5_1MidpointBias.lean` | `perron_cf_midpoint_symmetry`, `davenport_real_char_half_band_upper` |
| Theorem 5.2(i)–(ii) (Cross-symmetry, radicals, effective cores, Pell $\pm 2$) | `thm_5_2_part1_cross_symmetry`, `thm_5_2_part1_radical_bounds`, `thm_5_2_part2_effective_cores`, `thm_5_2_part2_pell_pm2_insoluble` | `Thm5_2EffectiveCores.lean` | Standard Lean axioms only |
| Theorem 5.3(i) (Rédei cohomology 4-rank via concrete `yMidVec`) | `thm_5_3_part1_cohomology_4rank` | `Thm5_3RedeiCohomology.lean` | `canonicalRealQuadRedei`, `redei_reichardt_exact_sequence` |
| Theorem 5.3(ii) (Inert absorption & dual quartic) | `thm_5_3_part2_inert_absorption`, `thm_5_3_part2_dual_quartic` | `Thm5_3RedeiCohomology.lean` | Standard Lean axioms only |

## Section 6 — Theorem 1.3(i) ($k = 2$ Gap & Counting Bounds)

| Manuscript Result | Lean 4 Declaration | File | External Axioms Used |
| :--- | :--- | :--- | :--- |
| Prop. 6.1 ($\mathrm{SL}_2$ & four-squares structure) | `prop_6_1_part1_sl2_and_four_squares` | `Prop6_1FourGCD.lean` | Standard Lean axioms only |
| Prop. 6.2(i)–(iii) ($n=4$ boundary, consecutive equipartition, square-shift exclusions) | `prop_6_2_part1_n4_boundary`, `prop_6_2_part2_consecutive_equipartition`, `prop_6_2_part3_square_shift_exclusions` | `Prop6_2ConsecutiveSquareShift.lean` | Standard Lean axioms only |
| Lemma 6.3 (Uniform parity flip) | `lem_6_3_parity_flip_uniform` | `Lem6_3ParityFlip.lean` | Sec. 2 analytic axioms |
| Theorem 6.4 & Theorem 1.3(i) (Capacity diamond, $k=2$ gap, polarization) | `thm_6_4_capacity_diamond`, `thm_1_3_part1_k2_gap_and_counting`, `thm_6_4_polarization_concentration` | `Thm6_4CapacityDiamond.lean`, `Thm6_4PolarizationConcentration.lean` | Sec. 2 analytic + Sec. 3 Pell axioms |

## Section 7 — Support-Reduced Padé–Wronskian & Theorem 1.3(ii)

| Manuscript Result | Lean 4 Declaration | File | External Axioms Used |
| :--- | :--- | :--- | :--- |
| Siegel's Lemma (Pigeonhole Principle) | `siegel_lemma_pigeonhole` | `Sec7PadeWronskian.lean` | Standard Lean axioms only |
| Lemma 7.1 (Initial Padé polynomials, parameterized by `AlgebraicTaylorFamily`) | `lem_7_1_initial_pade_polynomials` | `Sec7PadeWronskian.lean` | Standard Lean axioms only (parameterized) |
| Lemma 7.2 (Puiseux coset separation & inductive linear independence, parameterized by local coset-splitting) | `lem_7_2_monomial_product_puiseux_indep` | `Sec7PadeWronskian.lean` | Standard Lean axioms only (parameterized) |
| Lemma 7.3 (Support-reduced Wronskian & Gauss's Lemma divisibility, parameterized by `SupportWronskianData`) | `lem_7_3_support_reduced_wronskian` | `Sec7PadeWronskian.lean` | Standard Lean axioms only (parameterized) |
| Lemma 7.4(i)–(ii) & Sec. 7.4 exponent equivalence | `lem_7_4_denominator_clearing`, `depressed_poly_asymptotic_core`, `pade_chi_lt_ratio_iff_theta_lt` | `Sec7PadeWronskian.lean` | Standard Lean axioms only (parameterized) |
| Eq. (7.17) (Pigeonhole cluster reduction) | `pigeonhole_cluster_reduction` | `Sec7ClusterReduction.lean` | Standard Lean axioms only |
| Section 7.4 Dyadic cluster elimination (wiring Lemmas 7.1, 7.3, 7.4, eq. 7.17) | `dyadic_cluster_elimination_proved` | `Thm1_3Part2Counting.lean` | `bpz_lemma_4_2_taylor_family`, `siegel_ode_wronskian_on_support`, `bpz_cauchy_leibniz_pade_eval` |
| Theorem 1.3(ii) (Global $O(N^{6/7+\varepsilon})$, Brocard $O(N^{6/7+\varepsilon})$, Table 2 degree-gap bounds) | `thm_1_3_part2_global_6_7`, `thm_1_3_part2_brocard_6_7`, `thm_1_3_part2_degree_gap_bounds` | `Thm1_3Part2Counting.lean` | Same 3 external Section 7 axioms |

## Section 8 — Frey Curves & Tatuzawa Class Group Bounds

| Manuscript Result | Lean 4 Declaration | File | External Axioms Used |
| :--- | :--- | :--- | :--- |
| Theorem 8.1(i) (Frey curve $E_n$) | `thm_8_1_part1_frey_E` | `Thm8_1FreyCurves.lean` | `frey_E_modularity` |
| Theorem 8.1(ii) (Frey curve $F_n^{(2)}$, conductor $N(F_n^{(2)})$, level-2 CM, $abc$/Hall) | `thm_8_1_part2_level2_cm_reduction`, `thm_8_1_part2_abc_and_hall_bounds` | `Thm8_1FreyCurves.lean` | `frey_F2_modularity_and_galois` |
| Theorem 8.2 (Tatuzawa effective Siegel & narrow $2J$-rank) | `thm_8_2_tatuzawa_and_narrow_2J_rank` | `Thm8_2TatuzawaClassGroup.lean` | `canonicalRealQuadClassGroup`, `tatuzawa_effective_siegel` |
