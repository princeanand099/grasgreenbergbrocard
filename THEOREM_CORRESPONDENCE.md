# Theorem Correspondence: Manuscript ↔ Lean 4

## Section 2: Valuation-Parity Distribution (`O(N^{6/7})` and `O(N^\varepsilon)`)
| Manuscript Reference | Lean 4 Declaration | File |
|---|---|---|
| Core definitions $q_n, s_n, \mathcal{P}_{\mathrm{odd}}, \mathcal{P}_{\mathrm{even}}, S_{\mathrm{odd}}, S_{\mathrm{even}}, \Delta_{\mathrm{parity}}$ | `q_n`, `s_n`, `Podd`, `Peven`, `S_odd`, `S_even`, `Delta_parity`, `factorial_eq_q_n_mul_s_n_sq`, `q_n_squarefree` | `Basic.lean` |
| **Lemma 2.1(i)** (harmonic-layer valuation identities, eqs. 2.1–2.3) | `padicValNat_factorial_eq_div_of_lt_sq`, `padicValNat_factorial_on_harmonicInterval`, `harmonicLayer_odd_layer`, `harmonicLayer_even_layer`, `alt_harmonic_eq_tail_harmonic`, `alt_harmonic_sum_diff_log_two`, `Podd_upper_partition` | `ValuationParityLayer.lean` |
| **Lemma 2.1(ii)** ($\log q_n = (\log 2)n + O(n e^{-c_0\sqrt{\log n}})$ and $|\mathcal{P}_{\mathrm{odd}}(n)|$, eqs. 2.4–2.5) | `log_q_n_eq_sum_log`, `log_q_n_asymptotic`, `card_Podd_asymptotic` | `ValuationParityLayer.lean` |
| **Proposition 2.2** (Vaaler trigonometric polynomial parity approximation, eqs. 2.6–2.8) | `neg_one_pow_floor_eq_sawtooth`, `harmonic_sum_le_log_add_one`, `vaaler_parity_approx` | `ValuationParityVaaler.lean` |
| **Lemmas 2.3–2.4** (prime exponential sum bounds, eqs. 2.9–2.12) | `prime_exp_sum_bounds`, `prime_exp_sum_bounds_mod` | `ExpSumBounds.lean`, `ExpSumBoundsMod.lean` |
| **Theorem 2.5(i)** (second-order parity bound, eqs. 2.13–2.15) | `Delta_parity_second_order`, `collar_band_isBigO`, `interCollar_band_isBigO` | `ValuationParityThmPart1.lean`, `ValuationParityThmCollar.lean`, `ValuationParityThmInterCollar.lean` |
| **Theorem 2.5(ii)** (band parity, $\Sigma^*$, $\Delta_{\mathrm{parity}} = o(n\log n)$, $S_{\mathrm{odd}}, S_{\mathrm{even}} \sim \frac{1}{2}n\log n$, eqs. 2.16–2.17) | `small_prime_parity_band_bound`, `Sigma_star_parity_isLittleO_log`, `Delta_parity_isLittleO_mul_log`, `n_log_n_sub_n_le_log_factorial`, `S_odd_asymptotic`, `S_even_asymptotic` | `ValuationParityThm.lean` |
| **Theorem 2.5(iii)** (multi-modulus power-band equidistribution, eq. 2.18) | `multi_modulus_power_band_equidistribution`, `small_prime_mod_band_isBigO`, `upper_band_mod_isBigO` | `ValuationParityMod.lean` |

## Section 3: Chebyshev–Lucas Absorption, Theorems 1.1–1.2, and Proposition 3.3
| Manuscript Reference | Lean 4 Declaration | File |
|---|---|---|
| **Lemma 3.1(i)** (prime $p \equiv 3 \pmod 4$ dividing $q_n$; no negative Pell solution) | `q_n_has_prime_mod4`, `neg_pell_no_int_sol`, `neg_pell_no_rat_sol` | `PellFundamental.lean` |
| **Lemma 3.1(ii)** ($\log q_n > 0.4n$, $\log \varepsilon_n > 0.2n$, $k < 2.5\log n$, $\log(s_n\sqrt{q_n})$ asymptotic) | `log_q_n_gt_point4`, `log_fund_pell_gt_point2`, `pell_index_upper_bound`, `log_s_n_sqrt_q_n_asymptotic`, `log_s_n_asymptotic` | `PellFundamental.lean` |
| **Lemma 3.2 (eqs. 3.1–3.3)** (Chebyshev–Lucas identity, prime-power divisibility, $p$-adic valuation absorption) | `chebyshevU_eval`, `pell_lucas_identity`, `lucasY_eq_mul_chebyshevU`, `chebyshevU_eval_mod_M`, `gcd_pell_chebyshevU_dvd`, `padicValInt_chebyshevU`, `padicValNat_pell_absorption` | `ChebyshevLucas.lean` |
| **Theorem 1.1** (known solutions $n = 4, 5, 7$) | `known_k4`, `known_k5`, `known_k7` | `Thm1_1Collapse.lean` |
| **Theorem 1.1 (eqs. 1.6, 3.4–3.5)** (unconditional Pell index collapse $k \in \{1, 2\}$ for large $n$) | `pell_index_collapse_large` | `Thm1_1Collapse.lean` |
| **Theorem 1.1 (eq. 1.7)** (fundamental regulator quantization law) | `fundamental_regulator_quantization` | `Thm1_1Collapse.lean` |
| **Theorem 1.1** (distinctness of square-free cores $q_{n_1} \neq q_{n_2}$) | `q_n_ne_of_solutions` | `Thm1_1Collapse.lean` |
| **Theorem 1.2(i) (eqs. 1.8, 3.6–3.7)** (Nagura band primes, $v_p(s_n) \ge 1$, parity-independent non-$p$-rationality & $\lambda_p^*$) | `nagura_prime_in_band`, `prime_in_band_val_and_coprime_k`, `val_s_n_ge_one_on_half`, `thm_1_2_part1_valuation_law` | `Thm1_2Iwasawa.lean` |
| **Theorem 1.2(ii)** (split-prime unramified Iwasawa module & Taya criterion) | `thm_1_2_part2_split_primes` | `Thm1_2Iwasawa.lean` |
| **Theorem 1.2(iii)** (conditional finiteness under (a), (b), or (c)) | `thm_1_2_part3_conditional_finiteness` | `Thm1_2Iwasawa.lean` |
| **Proposition 3.3 (eq. 3.8)** ($\mathfrak{J}_n^2 = (1 + s_n\sqrt{-q_n})$, units $\{\pm 1\}$, $[\mathfrak{J}_n]=1 \iff k=2$, $k=1$ identity, $k=2$ second-stage non-principality) | `J_n_sq_eq`, `zsqrtd_neg_units`, `J_n_principal_iff_k_eq_2`, `k_eq_1_picard_identity`, `second_stage_nonprincipal_k_eq_2` | `Picard2Torsion.lean` |

## Section 4: Arithmetic Structure of the Critical Regime $k = 2$
| Manuscript Reference | Lean 4 Declaration | File |
|---|---|---|
| **Eqs. (4.1)–(4.3)** ($k=2$ algebraic identities) | `k_eq_2_identities` | `Prop4_1SmoothBiquad.lean` |
| **Proposition 4.1(i) (eq. 4.4)** ($(n/2)$-smoothness of $m+1$, radical bounds) | `prop_4_1_part1` | `Prop4_1SmoothBiquad.lean` |
| **Proposition 4.1(ii) (eqs. 4.5–4.6)** (biquadratic splitting & Fermat-quotient lock) | `prop_4_1_part2` | `Prop4_1SmoothBiquad.lean` |
| **Theorem 4.2(i) (eqs. 4.7–4.10)** (first-stage Euclidean division quartic law) | `thm_4_2_part1_quartic_law` | `Thm4_2QuarticCores.lean` |
| **Theorem 4.2(ii) (eqs. 4.11–4.13, 4.15)** (second-stage consecutive splitting & dual quartic locks) | `thm_4_2_part2_dual_quartic` | `Thm4_2QuarticCores.lean` |
| **Theorem 4.2(iii) (eqs. 4.14, 4.16)** (stretched-exponential midpoint core bounds) | `thm_4_2_part3_midpoint_core_bounds` | `Thm4_2QuarticCores.lean` |
