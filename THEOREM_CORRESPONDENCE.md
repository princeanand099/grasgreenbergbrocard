# Theorem Correspondence and Kernel Axiom Audit

Mapping between **Prince Anand**, *Arithmetic Structure and Counting Bounds for the Brocard–Ramanujan Equation* ([DOI: 10.5281/zenodo.24278751](https://doi.org/10.5281/zenodo.24278751)) and the Lean 4 (`v4.35.0`) formalization in `GrasGreenbergBrocard`.

Every declaration listed below is checked by `GrasGreenbergBrocard/AuditAxioms.lean` (**63** `#print axioms` declarations, **0** `sorryAx`, **0** `Lean.ofReduceBool`/`Lean.trustCompiler`). Every external-axiom entry below matches the exact Lean 4 kernel `#print axioms` closure (in addition to Lean's standard logical axioms `propext`, `Classical.choice`, `Quot.sound`).

## Section 2 — Valuation Parity & Prime Exponential Sums

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Eq. (2.1) / Layer decomposition ($\log q_n$) | `log_q_n_asymptotic` | `ValuationParityLayer.lean` | `de_la_vallee_poussin_theta` |
| Lemma 2.1 (Vaaler approximation) | `vaaler_parity_approx` | `ValuationParityVaaler.lean` | `vaaler_extremal_polynomials` |
| Prop. 2.2 (Prime exponential sum bounds) | `prime_exp_sum_bounds` | `ExpSumBounds.lean` | `vaughan_van_der_corput_prime_sum` |
| Thm. 2.3 (Second-order parity asymptotic $\Delta(n)$) | `Delta_parity_second_order` | `ValuationParityThm.lean` | `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Thm. 2.3 / 2.5 ($S_{\mathrm{odd}}(n)$ asymptotic) | `S_odd_asymptotic` | `ValuationParityThm.lean` | `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Prop. 2.4 (Multi-modulus equidistribution) | `multi_modulus_power_band_equidistribution` | `ValuationParityMod.lean` | `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |

## Section 3 — Theorems 1.1 & 1.2 (Pell Index Collapse & Iwasawa Theory)

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Known solutions $k(4)=1, k(5)=1, k(7)=2$ | `known_k4`, `known_k5`, `known_k7` | `Thm1_1Collapse.lean` | **Standard Lean axioms only** (`0` external) |
| Lemma 3.1(i) ($\log q_n > 0.4n$ for $n \ge 8, n \notin \{10,11,28\}$) | `log_q_n_gt_point4_ge8` | `PellFundamental.lean` | `rosser_schoenfeld_theta_diff` (plus pure kernel `decide` for $8 \le n < 116$) |
| Lemma 3.1(i) ($\log \varepsilon_n > 0.2n$ for all $n \ge 8$) | `log_fund_pell_gt_point2_ge8` | `PellFundamental.lean` | `rosser_schoenfeld_theta_diff` |
| Lemma 3.1(i) ($1 \le k < 2.5 \log n$ for all $n \ge 8$) | `pell_index_upper_bound_ge8` | `PellFundamental.lean` | `rosser_schoenfeld_theta_diff` |
| Theorem 1.1(i) (Pell index collapse $k \in \{1, 2\}$) | `pell_index_collapse_large` | `Thm1_1Collapse.lean` | `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `rosser_schoenfeld_theta_diff`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Theorem 1.1(ii) (Fundamental regulator quantization) | `fundamental_regulator_quantization` | `Thm1_1Collapse.lean` | `stirling_log_factorial_remainder` |
| Theorem 1.1(iii) (Distinct squarefree cores) | `q_n_ne_of_solutions` | `Thm1_1Collapse.lean` | `erdos_selfridge_consecutive_product_not_square` |
| Prop. 3.2 (Picard 2-torsion characterization) | `J_n_principal_iff_k_eq_2` | `Picard2Torsion.lean` | `breusch_bertrand_mod4` |
| Lemma 3.3 (Nagura band prime) | `nagura_prime_in_band` | `Thm1_2Iwasawa.lean` | `nagura_prime_in_interval` |
| Eq. (3.6) ($p$-adic regulator valuation from $n!+1=m^2$) | `thm_1_2_eq_3_6_regulator_valuation` | `Thm1_2Iwasawa.lean` | `canonicalRealQuadIwasawa`, `erdos_selfridge_consecutive_product_not_square`, `padic_log_regulator_pell_power` |
| Finite verification ($1 \le n < 116$, $n \notin \{4,5,7\}$) | `brocard_small_solutions_lt_116` | `Thm1_2Iwasawa.lean` | **Standard Lean axioms only** (`propext`, `Quot.sound`; pure kernel `decide`, 112 modular witnesses) |
| Theorem 1.2(i) (Valuation law & $\lambda_p^* \ge 1$) | `thm_1_2_part1_valuation_law` | `Thm1_2Iwasawa.lean` | `canonicalRealQuadIwasawa`, `erdos_selfridge_consecutive_product_not_square`, `iwasawa_main_conjecture_free_rank`, `leopoldt_coates_valuation_law`, `padic_log_regulator_pell_power` |
| Theorem 1.2(ii) (Split-prime unramified Iwasawa module) | `thm_1_2_part2_split_primes` | `Thm1_2Iwasawa.lean` | `canonicalRealQuadIwasawa`, `erdos_selfridge_consecutive_product_not_square`, `ozaki_taya_split_prime_iwasawa`, `padic_log_regulator_pell_power` |
| Theorem 1.2(iii) (Conditional finiteness, $n \ge 116$) | `thm_1_2_part3_conditional_finiteness` | `Thm1_2Iwasawa.lean` | `canonicalRealQuadIwasawa`, `erdos_selfridge_consecutive_product_not_square`, `iwasawa_main_conjecture_free_rank`, `leopoldt_coates_valuation_law`, `ozaki_taya_split_prime_iwasawa`, `padic_log_regulator_pell_power`, `rosser_schoenfeld_theta_diff` |
| Theorem 1.2(iii) (Complete conditional finiteness, $n \ge 1$) | `thm_1_2_part3_complete_finiteness` | `Thm1_2Iwasawa.lean` | `canonicalRealQuadIwasawa`, `erdos_selfridge_consecutive_product_not_square`, `iwasawa_main_conjecture_free_rank`, `leopoldt_coates_valuation_law`, `nagura_prime_in_interval`, `ozaki_taya_split_prime_iwasawa`, `padic_log_regulator_pell_power`, `rosser_schoenfeld_theta_diff` |

## Section 4 — Smooth Biquadratic Geometry & Quartic Cores

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Prop. 4.1(i) (Smoothness & raw prime-sum eq. 4.4) | `prop_4_1_part1` | `Prop4_1SmoothBiquad.lean` | `breusch_bertrand_mod4` |
| Prop. 4.1(i) (Asymptotic eq. 4.4: $(\log 2 + o(1))n$, $(1 - \log 2 + o(1))n$) | `prop_4_1_part1_asymptotic` | `Prop4_1SmoothBiquad.lean` | `breusch_bertrand_mod4`, `de_la_vallee_poussin_theta` |
| Prop. 4.1(ii) (Biquadratic splitting & Fermat-quotient lock) | `prop_4_1_part2` | `Prop4_1SmoothBiquad.lean` | `breusch_bertrand_mod4` |
| Theorem 4.2(i) (Euclidean lock) | `thm_4_2_part1_euclidean_lock` | `Thm4_2QuarticCores.lean` | `breusch_bertrand_mod4`, `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Theorem 4.2(ii) (Dual quartic core structure) | `thm_4_2_part2_dual_quartic` | `Thm4_2QuarticCores.lean` | `breusch_bertrand_mod4` |
| Theorem 4.2(iii) (Midpoint core bounds) | `thm_4_2_part3_midpoint_core_bounds` | `Thm4_2QuarticCores.lean` | `breusch_bertrand_mod4`, `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Theorem 4.2(iii) (Explicit Mertens core bound) | `thm_4_2_part3_mertens_bound` | `Thm4_2QuarticCores.lean` | `breusch_bertrand_mod4`, `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `mertens_first_theorem_odd_primes`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |

## Section 5 — Midpoint Bias, Effective Cores & Rédei Cohomology

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Prop. 5.1(i) (CF midpoint symmetry) | `prop_5_1_part1` | `Prop5_1MidpointBias.lean` | `breusch_bertrand_mod4`, `perron_cf_midpoint_symmetry` |
| Prop. 5.1(ii) (Midpoint prime-valuation bias) | `prop_5_1_part2_bias` | `Prop5_1MidpointBias.lean` | `breusch_bertrand_mod4`, `de_la_vallee_poussin_theta`, `perron_cf_midpoint_symmetry` |
| Theorem 5.2(i) (Cross-symmetry identity) | `thm_5_2_part1_cross_symmetry` | `Thm5_2EffectiveCores.lean` | **Standard Lean axioms only** (`0` external) |
| Theorem 5.2(i) (Radical bounds) | `thm_5_2_part1_radical_bounds` | `Thm5_2EffectiveCores.lean` | `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Theorem 5.2(ii) (Effective core bounds) | `thm_5_2_part2_effective_cores` | `Thm5_2EffectiveCores.lean` | `davenport_real_char_half_band_upper`, `rosser_schoenfeld_theta_diff` |
| Theorem 5.2(ii) (Pell $\pm 2$ insolubility) | `thm_5_2_part2_pell_pm2_insoluble` | `Thm5_2EffectiveCores.lean` | `breusch_bertrand_mod4`, `davenport_real_char_half_band_upper`, `rosser_schoenfeld_theta_diff` |
| Theorem 5.3(i) (Rédei cohomology 4-rank via concrete `yMidVec`) | `thm_5_3_part1_cohomology_4rank` | `Thm5_3RedeiCohomology.lean` | `canonicalRealQuadRedei`, `redei_reichardt_exact_sequence` |
| Theorem 5.3(ii) (Inert absorption & dual quartic) | `thm_5_3_part2_inert_absorption`, `thm_5_3_part2_dual_quartic` | `Thm5_3RedeiCohomology.lean` | `breusch_bertrand_mod4` |

## Section 6 — Theorem 1.3(i) ($k = 2$ Gap & Counting Bounds)

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Prop. 6.1 ($\mathrm{SL}_2$ & four-squares structure) | `prop_6_1_part1_sl2_and_four_squares` | `Prop6_1FourGCD.lean` | **Standard Lean axioms only** (`0` external) |
| Prop. 6.2(i) ($n=4$ boundary) | `prop_6_2_part1_n4_boundary` | `Prop6_2ConsecutiveSquareShift.lean` | **Standard Lean axioms only** (`0` external) |
| Prop. 6.2(ii) (Consecutive equipartition) | `prop_6_2_part2_consecutive_equipartition` | `Prop6_2ConsecutiveSquareShift.lean` | `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Prop. 6.2(iii) (Square-shift exclusions) | `prop_6_2_part3_square_shift_exclusions` | `Prop6_2ConsecutiveSquareShift.lean` | **Standard Lean axioms only** (`0` external) |
| Lemma 6.3 (Uniform parity flip) | `lem_6_3_parity_flip_uniform` | `Lem6_3ParityFlip.lean` | `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Theorem 6.4(a) (Capacity diamond) | `thm_6_4_capacity_diamond` | `Thm6_4CapacityDiamond.lean` | `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Theorem 1.3(i) ($k=2$ gap & $O_\varepsilon(N^\varepsilon)$ counting) | `thm_1_3_part1_k2_gap_and_counting` | `Thm6_4CapacityDiamond.lean` | `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |
| Theorem 6.4(b) (Polarization concentration) | `thm_6_4_polarization_concentration` | `Thm6_4PolarizationConcentration.lean` | `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `mertens_first_theorem`, `vaaler_extremal_polynomials`, `vaughan_van_der_corput_prime_sum` |

## Section 7 — Support-Reduced Padé–Wronskian & Theorem 1.3(ii)

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Siegel's Lemma (Pigeonhole Principle) | `siegel_lemma_pigeonhole` | `Sec7PadeWronskian.lean` | **Standard Lean axioms only** (`0` external) |
| Lemma 7.1 (Initial Padé polynomials, parameterized by `AlgebraicTaylorFamily`) | `lem_7_1_initial_pade_polynomials` | `Sec7PadeWronskian.lean` | **Standard Lean axioms only** (`0` external) |
| Lemma 7.2 (Puiseux coset separation & inductive linear independence) | `lem_7_2_monomial_product_puiseux_indep` | `Sec7PadeWronskian.lean` | **Standard Lean axioms only** (`0` external) |
| Lemma 7.3 (Support-reduced Wronskian & Gauss's Lemma divisibility) | `lem_7_3_support_reduced_wronskian` | `Sec7PadeWronskian.lean` | **Standard Lean axioms only** (`0` external) |
| Lemma 7.4(i) (Denominator clearing) | `lem_7_4_denominator_clearing` | `Sec7PadeWronskian.lean` | **Standard Lean axioms only** (`0` external) |
| Lemma 7.4(ii) (Depressed polynomial asymptotic core) | `depressed_poly_asymptotic_core` | `Sec7PadeWronskian.lean` | **Standard Lean axioms only** (`0` external) |
| Sec. 7.4 exponent equivalence ($\chi <$ ratio $\iff \theta <$) | `pade_chi_lt_ratio_iff_theta_lt` | `Sec7PadeWronskian.lean` | **Standard Lean axioms only** (`0` external) |
| Eq. (7.17) (Pigeonhole cluster reduction) | `pigeonhole_cluster_reduction` | `Sec7ClusterReduction.lean` | **Standard Lean axioms only** (`0` external) |
| Sec. 7.4 Dyadic cluster elimination (wiring Lemmas 7.1, 7.3, 7.4, eq. 7.17) | `dyadic_cluster_elimination_proved` | `Thm1_3Part2Counting.lean` | `bpz_cauchy_leibniz_pade_eval`, `bpz_lemma_4_2_taylor_family`, `siegel_ode_wronskian_on_support` |
| Theorem 1.3(ii) (Global $O(N^{6/7+\varepsilon})$, Brocard $O(N^{6/7+\varepsilon})$, Table 2 degree-gap bounds) | `thm_1_3_part2_global_6_7`, `thm_1_3_part2_brocard_6_7`, `thm_1_3_part2_degree_gap_bounds` | `Thm1_3Part2Counting.lean` | `bpz_cauchy_leibniz_pade_eval`, `bpz_lemma_4_2_taylor_family`, `siegel_ode_wronskian_on_support` |

## Section 8 — Frey Curves & Tatuzawa Class Group Bounds

| Manuscript Result | Lean 4 Declaration | File | Exact External Axioms (Kernel `#print axioms`) |
| :--- | :--- | :--- | :--- |
| Theorem 8.1(i) (Frey curve $E_n$) | `thm_8_1_part1_frey_E` | `Thm8_1FreyCurves.lean` | `frey_E_modularity` |
| Theorem 8.1(ii) (Frey curve $F_n^{(2)}$, conductor $N(F_n^{(2)})$, level-2 CM) | `thm_8_1_part2_level2_cm_reduction` | `Thm8_1FreyCurves.lean` | `breusch_bertrand_mod4`, `frey_F2_modularity_and_galois` |
| Theorem 8.1(ii) ($abc$-quality & Hall bounds) | `thm_8_1_part2_abc_and_hall_bounds` | `Thm8_1FreyCurves.lean` | `breusch_bertrand_mod4`, `de_la_vallee_poussin_theta` |
| Theorem 8.2 (Tatuzawa effective Siegel & narrow $2^J$-rank) | `thm_8_2_tatuzawa_and_narrow_2J_rank` | `Thm8_2TatuzawaClassGroup.lean` | `canonicalRealQuadClassGroup`, `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `erdos_selfridge_consecutive_product_not_square`, `pnt_pi_asymptotic`, `tatuzawa_effective_siegel` |
