# Theorem Correspondence & Fidelity Audit

| Manuscript Result | Location | Lean Module | Lean Declaration(s) | Fidelity & Proof Status |
|---|---|---|---|---|
| **Section 2** | | | | |
| Base-$p$ digit reduction | §2.1 | `ValuationParityDigits.lean` | `ValuationParityDigits` lemmas | Faithful; CI verified |
| Vaaler Fourier & exp sum bounds | §2.2 | `ValuationParityVaaler.lean`, `ExpSumBounds.lean` | Vaaler & van der Corput bounds | Faithful; CI verified |
| **Theorem 2.5(i)–(ii)** ($\Delta_{\mathrm{parity}}$, $S_{\mathrm{odd}}$, $S_{\mathrm{even}}$) | §2.3 | `ValuationParityThm.lean` | `Delta_parity_isLittleO_mul_log`, `S_odd_asymptotic`, `S_even_asymptotic` | Faithful; CI verified |
| **Theorem 2.5(iii)** (multi-modulus power-band equidistribution) | §2.4 | `ValuationParityMod.lean` | `small_prime_mod_band_isBigO`, `upper_band_mod_isBigO`, `multi_modulus_power_band_equidistribution` | Faithful; CI verified |
| **Section 3** | | | | |
| **Lemma 3.1(i)–(ii)** (fundamental unit norm & growth of $q_n, s_n$) | §3.1 | `PellFundamental.lean` | `q_n_has_prime_mod4`, `neg_pell_no_int_sol`, `log_q_n_gt_point4`, `pell_index_upper_bound`, `log_s_n_asymptotic` | Faithful; CI verified |
| **Lemma 3.2** (Chebyshev–Lucas factorization & LTE) | §3.1 | `ChebyshevLucas.lean` | `lucasY_eq_mul_chebyshevU`, `gcd_pell_chebyshevU_dvd`, `padicValInt_chebyshevU`, `padicValNat_pell_absorption` | Faithful; CI verified (0 external axioms) |
| **Theorem 1.1** (Pell index collapse $k \in \{1,2\}$, regulator quantization, distinct $q_n$) | §1, §3.2 | `Thm1_1Collapse.lean` | `known_k4`, `known_k5`, `known_k7`, `pell_index_collapse_large`, `fundamental_regulator_quantization`, `q_n_ne_of_solutions` | Faithful; CI verified |
| Picard 2-torsion & $k=1,2$ midpoint identities | §3.2–3.3 | `Picard2Torsion.lean` | `J_n_sq_eq`, `J_n_principal_iff_k_eq_2`, `k_eq_1_picard_identity`, `second_stage_nonprincipal_k_eq_2` | Faithful; CI verified |
| **Theorem 1.2(i)–(iii)** (non-$p$-rationality, Iwasawa invariants, conditional finiteness) | §1, §3.3 | `Thm1_2Iwasawa.lean` | `thm_1_2_part1_valuation_law`, `thm_1_2_part2_split_primes`, `thm_1_2_part3_conditional_finiteness` | Faithful; CI verified |
| **Section 4** | | | | |
| **Proposition 4.1(i)–(ii)** (smooth biquadratic structure for $k=2$) | §4.1 | `Prop4_1SmoothBiquad.lean` | `prop_4_1_part1`, `prop_4_1_part2` | Faithful; CI verified |
| **Theorem 4.2(i)** (first-stage Euclidean quartic law & lock, eqs. 4.8–4.10) | §4.2 | `Thm4_2QuarticCores.lean` | `thm_4_2_part1_quartic_law`, `thm_4_2_part1_euclidean_lock` | Faithful; CI verified |
| **Theorem 4.2(ii)** (second-stage dual quartic & locks, eqs. 4.11–4.13, 4.15) | §4.2 | `Thm4_2QuarticCores.lean` | `thm_4_2_part2_dual_quartic`, `thm_4_2_part2_euclidean_locks` | Faithful; CI verified |
| **Theorem 4.2(iii)** (midpoint core bounds & Mertens $n^{1/4}$ bound, eqs. 4.14, 4.16) | §4.2 | `Thm4_2QuarticCores.lean` | `thm_4_2_part3_midpoint_core_bounds`, `thm_4_2_part3_mertens_bound` | Faithful; CI verified |
| **Section 5** | | | | |
| **Proposition 5.1(i)–(ii)** (midpoint bias & cross-symmetry, eqs. 5.1–5.3) | §5.1 | `Prop5_1MidpointBias.lean` | `eq_5_1_midpoint_decomp`, `psi_eval_upper_half`, `prop_5_1_part1_midpoint_bias`, `prop_5_1_part2_cross_symmetry` | Faithful; CI verified |
| **Theorem 5.2(i)** (bipartition, cross-symmetry & radical bounds, eqs. 5.4–5.6) | §5.2 | `Thm5_2EffectiveCores.lean` | `thm_5_2_part1_bipartition`, `thm_5_2_part1_cross_symmetry`, `thm_5_2_part1_radical_bounds` | Faithful; CI verified |
| **Theorem 5.2(ii)** (effective cores $\delta_1, \delta_2$ & $\pm 2$-Pell insolubility, eq. 5.7) | §5.2 | `Thm5_2EffectiveCores.lean` | `delta2Mid_ne_two`, `thm_5_2_part2_effective_cores`, `thm_5_2_part2_pell_pm2_insoluble` | Faithful; CI verified |
| **Theorem 5.3(i)** (Rédei–Reichardt cohomology & 4-rank exact sequence, eq. 5.8) | §5.3 | `Thm5_3RedeiCohomology.lean` | `thm_5_3_part1_cohomology_4rank` | Faithful; CI verified |
| **Theorem 5.3(ii)** (inert prime absorption & dual quartic lock, eqs. 5.9–5.10) | §5.3 | `Thm5_3RedeiCohomology.lean` | `PevenPlus`, `PevenMinus`, `W_split`, `B_tilde`, `A_plus_star`, `thm_5_3_part2_inert_absorption`, `thm_5_3_part2_dual_quartic` | Faithful; CI verified |
| **Section 6** | | | | |
| **Proposition 6.1** (four-GCD decomposition, $\mathrm{SL}_2(\mathbb{Z})$ duality & bilinear relations) | §6.1 | `Prop6_1FourGCD.lean` | `X_gcd`, `Y_gcd`, `Z_gcd`, `W_gcd`, `P_ratio`, `prop_6_1_coprime_and_factorization`, `prop_6_1_sl2_duality`, `prop_6_1_bilinear_relations` | Faithful; CI verified (0 new axioms) |
| **Proposition 6.2(i)–(iii)** (consecutive square shift, unit exclusion & small square ratio) | §6.2 | `Prop6_2ConsecutiveSquareShift.lean`, `Thm6_4CapacityDiamond.lean` | `prop_6_2_part1_square_ratio_gap`, `prop_6_2_part2_no_two_unit_solutions`, `prop_6_2_part3_no_small_square_ratio`, `prop_6_2_part3_consecutive_squares_k2_exclusion` | Faithful; CI verified (0 new axioms) |
| **Lemma 6.3(i)–(ii)** (parity-flip factorization, oscillation bounds & window exclusion) | §6.3 | `Lem6_3ParityFlipOsc.lean`, `Lem6_3ParityFlip.lean` | `lem_6_3_part1_parity_flip_factorization`, `lem_6_3_part2_oscillation_bounds`, `lem_6_3_part2_window_exclusion` | Faithful; CI verified (0 new axioms) |
| **Theorem 6.4(a)** (capacity diamond & log bounds on $ZW, XY$) | §6.4 | `Thm6_4CapacityDiamond.lean` | `theta_weight`, `theta_eps_weight`, `log_ZW_and_XY_bounds`, `thm_6_4_capacity_diamond` | Faithful; CI verified (0 new axioms) |
| **Theorem 1.3(i)** ($k=2$ gap & $O(N^\varepsilon)$ counting bound) | §1, §6.4 | `Thm6_4CapacityDiamond.lean` | `thm_1_3_part1_k2_gap_and_counting` | Faithful; CI verified (0 new axioms) |
| **Theorem 6.4(b)** (polarization concentration via Rankin spherical cap Cauchy–Schwarz & $C_\varepsilon \eta^{-2} N^\varepsilon$ counting bound) | §6.4 | `Thm6_4PolarizationConcentration.lean` | `thm_6_4_polarization_concentration` | Faithful; CI verified (0 new axioms) |
| **Section 7** | | | | |
| **Siegel's Lemma & Lemma 7.1** (initial Padé polynomials via pigeonhole) | §7.1 | `Sec7PadeWronskian.lean` | `siegel_lemma_pigeonhole`, `lem_7_1_initial_pade_polynomials` | Faithful; CI verified |
| **Lemma 7.2** (monomial-product Puiseux linear independence) | §7.2 | `Sec7PadeWronskian.lean` | `lem_7_2_monomial_product_puiseux_indep` | Faithful; CI verified |
| **Lemma 7.3** (support-reduced Wronskian non-vanishing & height bound) | §7.2 | `Sec7PadeWronskian.lean` | `lem_7_3_support_reduced_wronskian` | Faithful; CI verified |
| **Lemma 7.4** (Gauss leading-coefficient divisibility bound) | §7.3 | `Sec7PadeWronskian.lean` | `gauss_leading_coeff_dvd_of_linear_factors`, `lem_7_4_leading_coeff_divisibility` | Faithful; CI verified |
| **Table 1 & Table 2** (exact Padé–Wronskian & decoupled monomial-product exponents) | §7.4 | `Thm1_3Part2Counting.lean` | `theta_m`, `theta_monomial`, `table1_m2_exact`–`table1_m5_exact`, `table2_nu3`–`table2_nu_large` | Faithful; CI verified |
| **Theorem 1.3(ii)** (global $O_{P,s,\varepsilon}(N^{6/7+\varepsilon})$, $\mathcal{N}_{\mathrm{Brocard}}(N) \ll_\varepsilon N^{6/7+\varepsilon}$, and degree-gap bounds for $\nu=3,4,5,\ge 6,\ge 25$, eq. 1.10) | §1, §7.4 | `Thm1_3Part2Counting.lean` | `dyadic_sum_counting`, `thm_1_3_part2_global_6_7`, `thm_1_3_part2_brocard_6_7`, `thm_1_3_part2_degree_gap_bounds` | Faithful; CI verified |
| **Section 8** | | | | |
| **Theorem 8.1(i)** (Frey curve $\mathcal{E}_n$, minimality, 2-isogenous $\widehat{\mathcal{E}}_n$, base-change unit factorization eq. 8.1, modularity & Frobenius traces) | §8.1 | `Thm8_1FreyCurves.lean` | `freyE_c4`, `freyE_Delta`, `thm_8_1_part1_frey_E` | Faithful; CI verified |
| **Theorem 8.1(ii)** (Level-2 Frey curve $F_n^{(2)}$, CM reduction eqs. 8.2–8.3, $v_p(j)=-2$, $abc$ quality $\ge (\frac{1}{4}-o(1))\log n$, Hall cubic-square bound) | §8.1 | `Thm8_1FreyCurves.lean` | `freyF2_c4`, `freyF2_Delta`, `thm_8_1_part2_level2_cm_reduction`, `thm_8_1_part2_abc_and_hall_bounds` | Faithful (with verified constant fix $\frac{1}{4\log 2} \to \frac{1}{4}$); CI verified |
| **Theorem 8.2** (effective Tatuzawa class number explosion eq. 8.4 & narrow $2^J$-rank dichotomy) | §8.2 | `Thm8_2TatuzawaClassGroup.lean` | `hNonGen`, `thm_8_2_tatuzawa_and_narrow_2J_rank` | Faithful (with verified exponent fix $n^{\frac{1}{4\log 2}-\varepsilon} \to n^{\frac{1}{4}-\varepsilon}$); CI verified |
