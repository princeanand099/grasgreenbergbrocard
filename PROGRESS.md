# Formalization Progress Log

## Milestone 1: Section 2 Valuation-Parity Distribution — COMPLETED (`main` CI `exit 0`)
- Formalized `Basic.lean`, `ExternalAxiomsAnalytic.lean`, and all `ValuationParity*` / `ValuationParityMod*` modules.

## Milestone 2: Section 3 Core Pell & Chebyshev–Lucas Foundations — COMPLETED (`sec3` CI `exit 0`)
- `ExternalAxiomsSec3.lean`: External analytic & Iwasawa-theoretic axioms.
- `PellFundamental.lean`: Lemma 3.1(i)–(ii) (`q_n_has_prime_mod4`, `neg_pell_no_int_sol`, `log_q_n_gt_point4`, `log_fund_pell_gt_point2`, `pell_index_upper_bound`, `log_s_n_sqrt_q_n_asymptotic`).
- `ChebyshevLucas.lean`: Lemma 3.2, eqs. 3.1–3.3 (`chebyshevU_eval`, `pell_lucas_identity`, `chebyshevU_prime_power_divisibility`, `padicValNat_pell_absorption`).

## Milestone 3: Section 3 Main Theorems & Proposition 3.3 — COMPLETED (`sec3` CI `exit 0`, commit `4244e7bb`)
- `Thm1_1Collapse.lean`: Theorem 1.1 (`known_k4`, `known_k5`, `known_k7`, `pell_index_collapse_large`, `fundamental_regulator_quantization`, `q_n_ne_of_solutions`).
- `Picard2Torsion.lean`: Proposition 3.3 (`J_n_sq_eq`, `zsqrtd_neg_units`, `J_n_principal_iff_k_eq_2`, `k_eq_1_picard_identity`, `second_stage_nonprincipal_k_eq_2`).
- `Thm1_2Iwasawa.lean`: Theorem 1.2(i)–(iii) (`nagura_prime_in_band`, `prime_in_band_val_and_coprime_k`, `val_s_n_ge_one_on_half`, `thm_1_2_part1_valuation_law`, `thm_1_2_part2_split_primes`, `thm_1_2_part3_conditional_finiteness`).
- Full `lake build` passed (`9071/9071` jobs, `exit 0`, 0 errors, 0 `sorry`s, 0 `admit`s).

## Milestone 4: Protocol Documentation & Merge to `main` — IN PROGRESS
- Updated `README.md`, `EXTERNAL_AXIOMS.md`, `MATHEMATICAL_CORRECTIONS.md`, `THEOREM_CORRESPONDENCE.md`, and `PROGRESS.md`.
- Opening and merging PR from `sec3` to `main` and verifying final `main` CI pass.
