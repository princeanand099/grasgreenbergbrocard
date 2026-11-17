# Theorem Correspondence: Manuscript ↔ Lean 4

## Section 2: Valuation-Parity Distribution
| Manuscript Reference | Lean 4 Declaration | File |
|---|---|---|
| Core definitions $q_n, s_n, \mathcal{P}_{\text{odd}}, \mathcal{P}_{\text{even}}, S_{\text{odd}}$ | `q_n`, `s_n`, `Podd`, `Peven`, `S_odd`, `factorial_eq_q_n_mul_s_n_sq`, `q_n_squarefree` | `Basic.lean` |
| Unconditional $O(N^{6/7})$ & $O(N^\varepsilon)$ parity distribution | `S_odd_asymptotic`, `n_log_n_sub_n_le_log_factorial`, `ValuationParityThm*` | `ValuationParityThm.lean` |
| Modular parity distribution | `ValuationParityMod*` | `ValuationParityMod.lean` |

## Section 3: Chebyshev–Lucas Absorption, Theorems 1.1–1.2, and Proposition 3.3
| Manuscript Reference | Lean 4 Declaration | File |
|---|---|---|
| **Lemma 3.1(i)** (prime $p \equiv 3 \pmod 4$ dividing $q_n$; no negative Pell solution) | `q_n_has_prime_mod4`, `neg_pell_no_int_sol` | `PellFundamental.lean` |
| **Lemma 3.1(ii)** ($\log q_n > 0.4n$, $\log \varepsilon_n > 0.2n$, $k < 2.5\log n$, $\log(s_n\sqrt{q_n})$ asymptotic) | `log_q_n_gt_point4`, `log_fund_pell_gt_point2`, `pell_index_upper_bound`, `log_s_n_sqrt_q_n_asymptotic` | `PellFundamental.lean` |
| **Lemma 3.2 (eqs. 3.1–3.3)** (Chebyshev–Lucas identity, prime-power divisibility, $p$-adic valuation absorption) | `chebyshevU_eval`, `pell_lucas_identity`, `chebyshevU_prime_power_divisibility`, `padicValNat_pell_absorption` | `ChebyshevLucas.lean` |
| **Theorem 1.1** (known solutions $n = 4, 5, 7$) | `known_k4`, `known_k5`, `known_k7` | `Thm1_1Collapse.lean` |
| **Theorem 1.1 (eq. 1.6, 3.4–3.5)** (unconditional Pell index collapse $k \in \{1, 2\}$ for large $n$) | `pell_index_collapse_large` | `Thm1_1Collapse.lean` |
| **Theorem 1.1 (eq. 1.7)** (fundamental regulator quantization law) | `fundamental_regulator_quantization` | `Thm1_1Collapse.lean` |
| **Theorem 1.1** (distinctness of square-free cores $q_{n_1} \neq q_{n_2}$) | `q_n_ne_of_solutions` | `Thm1_1Collapse.lean` |
| **Theorem 1.2(i) (eqs. 1.8, 3.6–3.7)** (Nagura band primes, $v_p(s_n) \ge 1$, parity-independent non-$p$-rationality & $\lambda_p^*$) | `nagura_prime_in_band`, `prime_in_band_val_and_coprime_k`, `val_s_n_ge_one_on_half`, `thm_1_2_part1_valuation_law` | `Thm1_2Iwasawa.lean` |
| **Theorem 1.2(ii)** (split-prime unramified Iwasawa module & Taya criterion) | `thm_1_2_part2_split_primes` | `Thm1_2Iwasawa.lean` |
| **Theorem 1.2(iii)** (conditional finiteness under (a), (b), or (c)) | `thm_1_2_part3_conditional_finiteness` | `Thm1_2Iwasawa.lean` |
| **Proposition 3.3 (eq. 3.8)** ($\mathfrak{J}_n^2 = (1 + s_n\sqrt{-q_n})$, units $\{\pm 1\}$, $[\mathfrak{J}_n]=1 \iff k=2$, $k=1$ identity, $k=2$ second-stage non-principality) | `J_n_sq_eq`, `zsqrtd_neg_units`, `J_n_principal_iff_k_eq_2`, `k_eq_1_picard_identity`, `second_stage_nonprincipal_k_eq_2` | `Picard2Torsion.lean` |
