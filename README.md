# Gras–Greenberg–Brocard Lean 4 Formalization

Lean 4 (v4.35.0) + Mathlib formalization of **Sections 2 and 3** (and Theorems 1.1–1.2) of the manuscript:

> *Chebyshev–Lucas Valuation Absorption, Pell Index Collapse, and Non-$p$-Rationality in Brocard's Problem*

## Build Status

- **Branch `sec3` / `main`**: Full `lake build` passes with **0 errors**, **0 `sorry`s**, **0 `admit`s**, and **0 manuscript-owned axioms**.
- **Lean Toolchain**: `leanprover/lean4:v4.35.0`

## Module Structure

### Section 2: Unconditional Valuation-Parity Distribution (`O(N^{6/7})` & `O(N^ε)`)
- `GrasGreenbergBrocard/Basic.lean`: Core definitions (`q_n`, `s_n`, `Podd`, `Peven`, `S_odd`), `factorial_eq_q_n_mul_s_n_sq`, `q_n_squarefree`.
- `GrasGreenbergBrocard/ExternalAxiomsAnalytic.lean`: External classical analytic axioms (e.g., Vaaler trigonometric polynomial approximation, Vinogradov–Korobov / Weyl-type exponential sum bounds).
- `GrasGreenbergBrocard/ValuationParityLayer.lean`, `ValuationParityDigits.lean`, `ValuationParityVaaler.lean`, `ExpSumBounds.lean`, `ValuationParityThmHelpers.lean`, `ValuationParityThmPart1.lean`, `ValuationParityThmCollar.lean`, `ValuationParityThmInterCollar.lean`, `ValuationParityThm.lean`: Unconditional $O(N^{6/7})$ and $O(N^\varepsilon)$ parity-distribution theorems.
- `GrasGreenbergBrocard/ExpSumBoundsMod.lean`, `VaalerMod.lean`, `ValuationParityModWeight.lean`, `ValuationParityModCollar.lean`, `ValuationParityModInterCollar.lean`, `ValuationParityMod.lean`: Modular arithmetic progressions and parity distribution.

### Section 3: Chebyshev–Lucas Valuation Absorption, Theorem 1.1, Theorem 1.2, and Proposition 3.3
- `GrasGreenbergBrocard/ExternalAxiomsSec3.lean`: External peer-reviewed analytic & Iwasawa-theoretic axioms (Breusch 1932, Rosser–Schoenfeld 1962, Stirling remainder, Erdős–Selfridge 1975, Nagura 1952, Leopoldt–Coates, Ferrero–Washington/Mazur–Wiles/Greenberg, Ozaki/Yanagisawa/Taya).
- `GrasGreenbergBrocard/PellFundamental.lean`: **Lemma 3.1(i)–(ii)** (`q_n_has_prime_mod4`, `neg_pell_no_int_sol`, `log_q_n_gt_point4`, `log_fund_pell_gt_point2`, `pell_index_upper_bound`, `log_s_n_sqrt_q_n_asymptotic`).
- `GrasGreenbergBrocard/ChebyshevLucas.lean`: **Lemma 3.2 (eqs. 3.1–3.3)** (`chebyshevU_eval`, `pell_lucas_identity`, `chebyshevU_prime_power_divisibility`, `padicValNat_pell_absorption`).
- `GrasGreenbergBrocard/Thm1_1Collapse.lean`: **Theorem 1.1 (eqs. 1.6–1.7, 3.4–3.5)** (`known_k4`, `known_k5`, `known_k7`, `pell_index_collapse_large`, `fundamental_regulator_quantization`, `q_n_ne_of_solutions`).
- `GrasGreenbergBrocard/Picard2Torsion.lean`: **Proposition 3.3 (eq. 3.8)** (`J_n_sq_eq`, `zsqrtd_neg_units`, `J_n_principal_iff_k_eq_2`, `k_eq_1_picard_identity`, `second_stage_nonprincipal_k_eq_2`).
- `GrasGreenbergBrocard/Thm1_2Iwasawa.lean`: **Theorem 1.2(i)–(iii) (eqs. 1.8, 3.6–3.7)** (`nagura_prime_in_band`, `prime_in_band_val_and_coprime_k`, `val_s_n_ge_one_on_half`, `thm_1_2_part1_valuation_law`, `thm_1_2_part2_split_primes`, `thm_1_2_part3_conditional_finiteness`).

## Documentation
- [`THEOREM_CORRESPONDENCE.md`](THEOREM_CORRESPONDENCE.md): Exact mapping from manuscript theorems, lemmas, propositions, and equations to Lean 4 declarations.
- [`EXTERNAL_AXIOMS.md`](EXTERNAL_AXIOMS.md): Complete inventory of external axioms with published literature citations.
- [`MATHEMATICAL_CORRECTIONS.md`](MATHEMATICAL_CORRECTIONS.md): Formalization clarifications and verification notes.
- [`PROGRESS.md`](PROGRESS.md): Milestone-by-milestone completion log.
