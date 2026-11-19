# Theorem Correspondence and Kernel Axiom Audit

This document maps every theorem, proposition, lemma, and numerical table in *Arithmetic Structure, Iwasawa Theory, and Counting Bounds for the Brocard–Ramanujan Equation* (`brocard_arithmetic_structure_and_counting_bounds.tex`) to its exact Lean 4 declaration in `GrasGreenbergBrocard/`, together with its machine-checked `#print axioms` status from `GrasGreenbergBrocard/AuditAxioms.lean` ([CI Run #44567866016](https://github.com/princeanand099/grasgreenbergbrocard/actions/runs/44567866016/job/135714460223), [CI Log `56e1d6d4`](https://github.com/princeanand099/grasgreenbergbrocard/commit/56e1d6d4bca09efcde64400ed0b5fb3fe1c5e309)).

All 42 audited declarations compile with **zero `sorry`**, **zero `sorryAx`**, and **zero `Lean.ofReduceBool` / `Lean.trustCompiler`**. Eight core audited results are proved **purely from Lean's standard foundational axioms** (`propext`, `Classical.choice`, `Quot.sound`) with zero external mathematical axioms.

| Manuscript Result | Section | Lean Module (`GrasGreenbergBrocard/`) | Audited Lean Declaration(s) | Kernel Axiom Classification & Status |
| :--- | :--- | :--- | :--- | :--- |
| **Section 2: Valuation Parity & Modular Equidistribution** | | | | |
| Log square-free core asymptotic $\log q_n = (\log 2 + o(1)) n$ | §2.1 | `ValuationParityLayer.lean` | `log_q_n_asymptotic` | Standard + `de_la_vallee_poussin_theta`; CI verified |
| Vaaler parity trigonometric approximation | §2.2 | `ValuationParityVaaler.lean` | `vaaler_parity_approx` | Standard + `vaaler_extremal_polynomials`; CI verified |
| Dyadic prime exponential sum bounds (tightened `IsPrimeSubinterval` + `AntitoneOn w`) | §2.3 | `ExpSumBounds.lean` | `prime_exp_sum_bounds` | Standard + `vaughan_van_der_corput_prime_sum`; CI verified (PR #8) |
| Second-order valuation parity $\Delta(n)$ | §2.4 | `ValuationParityThm.lean` | `Delta_parity_second_order` | Standard + Section 2 analytic axioms; CI verified (PR #8) |
| **Theorem 2.5** ($S_{\mathrm{odd}}(n)$ asymptotic) | §2.4 | `ValuationParityThm.lean` | `S_odd_asymptotic` | Standard + Section 2 analytic axioms; CI verified (PR #8) |
| Multi-modulus power-band equidistribution | §2.5 | `ValuationParityMod.lean` | `multi_modulus_power_band_equidistribution` | Standard + Section 2 analytic axioms (excluding `chebyshev_pi_upper`); CI verified (PR #8) |
| **Section 3 & Theorems 1.1–1.2: Pell Collapse & Iwasawa Theory** | | | | |
| **Theorem 1.1(i)** (Pell index collapse $k \in \{1,2\}$ for large $n$) | §1, §3.1 | `Thm1_1Collapse.lean` | `pell_index_collapse_large` | Standard + Sec. 2 analytic + `rosser_schoenfeld_theta_diff`; CI verified |
| **Theorem 1.1(ii)** (fundamental regulator quantization) | §1, §3.2 | `Thm1_1Collapse.lean` | `fundamental_regulator_quantization` | Standard + `stirling_log_factorial_remainder`; CI verified |
| **Theorem 1.1(iii)** (distinctness of square-free cores $q_n$) | §1, §3.2 | `Thm1_1Collapse.lean` | `q_n_ne_of_solutions` | Standard + `erdos_selfridge_consecutive_product_not_square`; CI verified |
| Principality criterion $J_n$ principal $\iff k = 2$ | §3.3 | `Picard2Torsion.lean` | `J_n_principal_iff_k_eq_2` | Standard + `breusch_bertrand_mod4`; CI verified |
| **Theorem 1.2(i)** (Leopoldt–Coates $p$-adic valuation law) | §1, §3.4 | `Thm1_2Iwasawa.lean` | `thm_1_2_part1_valuation_law` | Standard + `canonicalRealQuadIwasawa`, `leopoldt_coates_valuation_law`, `iwasawa_main_conjecture_free_rank`; CI verified (PR #7) |
| **Theorem 1.2(ii)** (split-prime Iwasawa invariants) | §1, §3.4 | `Thm1_2Iwasawa.lean` | `thm_1_2_part2_split_primes` | Standard + `canonicalRealQuadIwasawa`, `ozaki_taya_split_prime_iwasawa`; CI verified (PR #7) |
| **Theorem 1.2(iii)** (conditional finiteness under Greenberg/Iwasawa) | §1, §3.4 | `Thm1_2Iwasawa.lean` | `thm_1_2_part3_conditional_finiteness` | Standard + `canonicalRealQuadIwasawa`, `leopoldt_coates_valuation_law`, `iwasawa_main_conjecture_free_rank`, `ozaki_taya_split_prime_iwasawa`; CI verified (PR #7) |
| **Section 4: Smooth Biquadratic Models & Quartic Cores** | | | | |
| **Proposition 4.1(i)** (smooth biquadratic realization) | §4.1 | `Prop4_1SmoothBiquad.lean` | `prop_4_1_part1` | Standard + `breusch_bertrand_mod4`; CI verified |
| **Proposition 4.1(ii)** (2-torsion and class-group obstruction) | §4.1 | `Prop4_1SmoothBiquad.lean` | `prop_4_1_part2` | Standard + `breusch_bertrand_mod4`; CI verified |
| **Theorem 4.2(i)** (Euclidean lock) | §4.2 | `Thm4_2QuarticCores.lean` | `thm_4_2_part1_euclidean_lock` | Standard + `breusch_bertrand_mod4` + Sec. 2 analytic axioms; CI verified |
| **Theorem 4.2(ii)** (dual quartic core structure) | §4.2 | `Thm4_2QuarticCores.lean` | `thm_4_2_part2_dual_quartic` | Standard + `breusch_bertrand_mod4`; CI verified |
| **Theorem 4.2(iii)** (midpoint core bounds) | §4.2 | `Thm4_2QuarticCores.lean` | `thm_4_2_part3_midpoint_core_bounds` | Standard + `breusch_bertrand_mod4` + Sec. 2 analytic axioms; CI verified |
| **Section 5: Continued Fractions, Effective Cores & Rédei Cohomology** | | | | |
| **Proposition 5.1(i)** (continued-fraction midpoint symmetry) | §5.1 | `Prop5_1MidpointBias.lean` | `prop_5_1_part1` | Standard + `breusch_bertrand_mod4`, `perron_cf_midpoint_symmetry`; CI verified |
| **Proposition 5.1(ii)** (midpoint prime-valuation bias) | §5.1 | `Prop5_1MidpointBias.lean` | `prop_5_1_part2_bias` | Standard + `breusch_bertrand_mod4`, `de_la_vallee_poussin_theta`, `perron_cf_midpoint_symmetry`; CI verified |
| **Theorem 5.2(i)** (cross-symmetry identity) | §5.2 | `Thm5_2EffectiveCores.lean` | `thm_5_2_part1_cross_symmetry` | **Standard axioms only** (`0` external axioms); CI verified |
| **Theorem 5.2(ii)** (effective core bounds) | §5.2 | `Thm5_2EffectiveCores.lean` | `thm_5_2_part2_effective_cores` | Standard + `davenport_real_char_half_band_upper`, `rosser_schoenfeld_theta_diff`; CI verified |
| **Theorem 5.3(i)** (Rédei cohomology and narrow $4$-rank) | §5.3 | `Thm5_3RedeiCohomology.lean` | `thm_5_3_part1_cohomology_4rank` | Standard + `redei_reichardt_exact_sequence`; CI verified |
| **Theorem 5.3(ii)** (dual quartic Rédei pairing) | §5.3 | `Thm5_3RedeiCohomology.lean` | `thm_5_3_part2_dual_quartic` | Standard + `breusch_bertrand_mod4`; CI verified |
| **Section 6 & Theorem 1.3(i): Capacity Diamond & $k=2$ Counting** | | | | |
| **Proposition 6.1** ($\mathrm{SL}_2$ structure & four-GCD factorization) | §6.1 | `Prop6_1FourGCD.lean` | `prop_6_1_part1_sl2_and_four_squares` | **Standard axioms only** (`0` external axioms); CI verified |
| **Proposition 6.2(iii)** (square-shift exclusions) | §6.2 | `Prop6_2ConsecutiveSquareShift.lean` | `prop_6_2_part3_square_shift_exclusions` | **Standard axioms only** (`0` external axioms); CI verified |
| **Lemma 6.3** (uniform parity-flip bound via honest collar-excised Vaaler proof `lem_6_3_osc_bound_honest`) | §6.3 | `Lem6_3ParityFlipOsc.lean`, `Lem6_3ParityFlip.lean` | `lem_6_3_parity_flip_uniform` | Standard + `mertens_first_theorem`, `vaaler_extremal_polynomials`, tightened `vaughan_van_der_corput_prime_sum`; CI verified (PR #8) |
| **Theorem 6.4(a)** (capacity diamond & log bounds on $ZW, XY$) | §6.4 | `Thm6_4CapacityDiamond.lean` | `thm_6_4_capacity_diamond` | Standard + Sec. 2 analytic axioms (0 new axioms); CI verified (PR #8) |
| **Theorem 1.3(i)** ($k=2$ gap & $O(N^\varepsilon)$ counting bound) & Prop. 6.2(iii) consecutive-square $k=2$ exclusion | §1, §6.4 | `Thm6_4CapacityDiamond.lean` | `thm_1_3_part1_k2_gap_and_counting` (and `prop_6_2_part3_consecutive_squares_k2_exclusion`) | Standard + Sec. 2 analytic axioms (0 new axioms); CI verified (PR #8) |
| **Theorem 6.4(b)** (polarization concentration via Rankin spherical cap Cauchy–Schwarz & $C_\varepsilon \eta^{-2} N^\varepsilon$ bound) | §6.4 | `Thm6_4PolarizationConcentration.lean` | `thm_6_4_polarization_concentration` | Standard + Sec. 2 analytic axioms (0 new axioms); CI verified (PR #8) |
| **Section 7 & Theorem 1.3(ii): Support-Reduced Padé–Wronskian Method** | | | | |
| **Siegel's Lemma** (pigeonhole construction) | §7.1 | `Sec7PadeWronskian.lean` | `siegel_lemma_pigeonhole` | **Standard axioms only** (`0` external axioms); CI verified |
| **Lemma 7.1** (initial Padé polynomials) | §7.1 | `Sec7PadeWronskian.lean` | `lem_7_1_initial_pade_polynomials` | **Standard axioms only** (`0` external axioms); CI verified |
| **Lemma 7.2** (monomial-product Puiseux linear independence) | §7.2 | `Sec7PadeWronskian.lean` | `lem_7_2_monomial_product_puiseux_indep` | **Standard axioms only** (`0` external axioms); CI verified |
| **Lemma 7.3** (support-reduced Wronskian non-vanishing & height bound) | §7.2 | `Sec7PadeWronskian.lean` | `lem_7_3_support_reduced_wronskian` | **Standard axioms only** (`0` external axioms); CI verified |
| **Lemma 7.4** (denominator clearing & Gauss leading-coefficient divisibility) | §7.3 | `Sec7PadeWronskian.lean` | `lem_7_4_denominator_clearing` | **Standard axioms only** (`0` external axioms); CI verified |
| **Tables 1 & 2** and **Theorem 1.3(ii)** (global $O_{P,s,\varepsilon}(N^{6/7+\varepsilon})$, $\mathcal{N}_{\mathrm{Brocard}}(N) \ll_\varepsilon N^{6/7+\varepsilon}$, degree-gap bounds for $\nu=3,4,5,\ge 6,\ge 25$) | §1, §7.4 | `Thm1_3Part2Counting.lean` | `thm_1_3_part2_global_6_7`, `thm_1_3_part2_brocard_6_7`, `thm_1_3_part2_degree_gap_bounds` | Standard + tightened `bpz_dyadic_cluster_elimination` (with internally proved `brocard_poly_depressed_gap`); CI verified (PR #7) |
| **Section 8: Elliptic Curve Realizations & Effective Class Group Bounds** | | | | |
| **Theorem 8.1(i)** (Frey curve $\mathcal{E}_n$, minimality, 2-isogenous $\widehat{\mathcal{E}}_n$, modularity & Frobenius traces) | §8.1 | `Thm8_1FreyCurves.lean` | `thm_8_1_part1_frey_E` | Standard + `frey_curve_modularity_and_galois`; CI verified |
| **Theorem 8.1(ii)** (Level-2 Frey curve $F_n^{(2)}$ & CM reduction) | §8.1 | `Thm8_1FreyCurves.lean` | `thm_8_1_part2_level2_cm_reduction` | Standard + `breusch_bertrand_mod4`, `frey_curve_modularity_and_galois`; CI verified |
| **Theorem 8.1(ii)** ($abc$-quality $\ge (\frac{1}{4}-o(1))\log n$ & Hall cubic-square bound) | §8.1 | `Thm8_1FreyCurves.lean` | `thm_8_1_part2_abc_and_hall_bounds` | Standard + `breusch_bertrand_mod4`, `de_la_vallee_poussin_theta`; synchronized constant fix $\frac{1}{4\log 2} \to \frac{1}{4}$; CI verified |
| **Theorem 8.2** (effective Tatuzawa class number explosion & narrow $2^J$-rank dichotomy) | §8.2 | `Thm8_2TatuzawaClassGroup.lean` | `thm_8_2_tatuzawa_and_narrow_2J_rank` | Standard + `canonicalRealQuadClassGroup`, `tatuzawa_effective_siegel`, `chebyshev_pi_upper`, `de_la_vallee_poussin_theta`, `erdos_selfridge_consecutive_product_not_square`, `pnt_pi_asymptotic`; synchronized exponent fix $n^{\frac{1}{4\log 2}-\varepsilon} \to n^{\frac{1}{4}-\varepsilon}$; CI verified (PR #7) |
