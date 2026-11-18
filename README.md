# Gras–Greenberg–Brocard Lean 4 Formalization

Lean 4 (v4.35.0) + Mathlib formalization of the Brocard–Ramanujan–Greenberg–Gras manuscript:

> *Arithmetic Structure and Counting Bounds for Brocard's Problem*

## Build Status

- **Lean Toolchain**: `leanprover/lean4:v4.35.0`
- **Build Verification**: Full `lake build` passes with **0 errors**, **0 `sorry`s**, **0 `admit`s**, and **0 manuscript-owned axioms**.

## Module Structure

### Section 2: Unconditional Valuation-Parity Distribution (`O(N^{6/7})` & `O(N^ε)`)
- `GrasGreenbergBrocard/Basic.lean`: Core definitions (`q_n`, `s_n`, `Podd`, `Peven`, `S_odd`, `S_even`, `Delta_parity`), `factorial_eq_q_n_mul_s_n_sq`, `q_n_squarefree`.
- `GrasGreenbergBrocard/ExternalAxiomsAnalytic.lean`: External peer-reviewed analytic number theory axioms (de la Vallée Poussin $\vartheta(x)$ error bound, Vaaler trigonometric polynomial approximation bounds, Vinogradov–Korobov / Weyl-type prime exponential sum bounds).
- `GrasGreenbergBrocard/ValuationParityLayer.lean`: Harmonic-layer decomposition of $v_p(n!)$, $\log q_n = (\log 2)n + O(n \exp(-c_0\sqrt{\log n}))$, and $|\mathcal{P}_{\mathrm{odd}}(n)|$ asymptotics (**Lemma 2.1(i)–(ii)**).
- `GrasGreenbergBrocard/ValuationParityDigits.lean`: Base-$p$ digit-sum / Legendre valuation identities.
- `GrasGreenbergBrocard/ValuationParityVaaler.lean`: Sawtooth-floor identity and Vaaler trigonometric polynomial approximation (**Proposition 2.2**).
- `GrasGreenbergBrocard/ExpSumBounds.lean`: Dyadic exponential-sum bounds over primes (**Lemma 2.3 / 2.4**).
- `GrasGreenbergBrocard/ValuationParityThmHelpers.lean`: Dyadic partitions, Mertens-type band bounds (`mertens_sum_le`, `mertens_band_le`, `Mertens_div_p_band_le`), and shifted alternating harmonic bounds.
- `GrasGreenbergBrocard/ValuationParityThmPart1.lean`, `ValuationParityThmCollar.lean`, `ValuationParityThmInterCollar.lean`, `ValuationParityThm.lean`: Collar/inter-collar decomposition and unconditional $O(N^{6/7})$ and $O(N^\varepsilon)$ parity-distribution theorems (**Theorem 2.5(i)–(ii)**, `small_prime_parity_band_bound`, `Sigma_star_parity_isLittleO_log`, `Delta_parity_isLittleO_mul_log`, `Delta_parity_second_order`, `S_odd_asymptotic`, `S_even_asymptotic`, `n_log_n_sub_n_le_log_factorial`).
- `GrasGreenbergBrocard/ExpSumBoundsMod.lean`, `VaalerMod.lean`, `ValuationParityModWeight.lean`, `ValuationParityModCollar.lean`, `ValuationParityModInterCollar.lean`, `ValuationParityMod.lean`: Modular arithmetic progression Vaaler weights and multi-modulus power-band equidistribution (**Theorem 2.5(iii)**, `multi_modulus_power_band_equidistribution`, `small_prime_mod_band_isBigO`, `upper_band_mod_isBigO`).

### Section 3: Chebyshev–Lucas Valuation Absorption, Theorems 1.1–1.2, and Proposition 3.3
- `GrasGreenbergBrocard/ExternalAxiomsSec3.lean`: External peer-reviewed analytic and Iwasawa-theoretic axioms (Breusch 1932, Rosser–Schoenfeld 1962, Stirling remainder, Erdős–Selfridge 1975, Nagura 1952, Leopoldt–Coates, Ferrero–Washington/Mazur–Wiles/Greenberg, Ozaki/Yanagisawa/Taya).
- `GrasGreenbergBrocard/PellFundamental.lean`: **Lemma 3.1(i)–(ii)** (`q_n_has_prime_mod4`, `neg_pell_no_int_sol`, `neg_pell_no_rat_sol`, `log_q_n_gt_point4`, `log_fund_pell_gt_point2`, `pell_index_upper_bound`, `log_s_n_sqrt_q_n_asymptotic`, `log_s_n_asymptotic`).
- `GrasGreenbergBrocard/ChebyshevLucas.lean`: **Lemma 3.2 (eqs. 3.1–3.3)** (`chebyshevU_eval`, `pell_lucas_identity`, `lucasY_eq_mul_chebyshevU`, `chebyshevU_eval_mod_M`, `gcd_pell_chebyshevU_dvd`, `padicValInt_chebyshevU`, `padicValNat_pell_absorption`).
- `GrasGreenbergBrocard/Thm1_1Collapse.lean`: **Theorem 1.1 (eqs. 1.6–1.7, 3.4–3.5)** (`known_k4`, `known_k5`, `known_k7`, `pell_index_collapse_large`, `fundamental_regulator_quantization`, `q_n_ne_of_solutions`).
- `GrasGreenbergBrocard/Picard2Torsion.lean`: **Proposition 3.3 (eq. 3.8)** (`J_n_sq_eq`, `zsqrtd_neg_units`, `J_n_principal_iff_k_eq_2`, `k_eq_1_picard_identity`, `second_stage_nonprincipal_k_eq_2`).
- `GrasGreenbergBrocard/Thm1_2Iwasawa.lean`: **Theorem 1.2(i)–(iii) (eqs. 1.8, 3.6–3.7)** (`nagura_prime_in_band`, `prime_in_band_val_and_coprime_k`, `val_s_n_ge_one_on_half`, `thm_1_2_part1_valuation_law`, `thm_1_2_part2_split_primes`, `thm_1_2_part3_conditional_finiteness`).

### Section 4: Arithmetic Structure of the Critical Regime $k = 2$
- `GrasGreenbergBrocard/ExternalAxiomsSec4.lean`: Mertens' first theorem on odd primes and PNT $n$-th prime asymptotic.
- `GrasGreenbergBrocard/Prop4_1SmoothBiquad.lean`: **Proposition 4.1(i)–(ii) (eqs. 4.1–4.6)** (`k_eq_2_identities`, `prop_4_1_part1`, `prop_4_1_part2`).
- `GrasGreenbergBrocard/Thm4_2QuarticCores.lean`: **Theorem 4.2(i)–(iii) (eqs. 4.7–4.16)** (`thm_4_2_part1_quartic_law`, `thm_4_2_part1_euclidean_lock`, `thm_4_2_part2_dual_quartic`, `thm_4_2_part2_euclidean_locks`, `thm_4_2_part3_midpoint_core_bounds`, `thm_4_2_part3_mertens_bound`).

## Documentation
- [`THEOREM_CORRESPONDENCE.md`](THEOREM_CORRESPONDENCE.md): Exact mapping from manuscript theorems, lemmas, propositions, and equations to Lean 4 declarations.
- [`EXTERNAL_AXIOMS.md`](EXTERNAL_AXIOMS.md): Complete inventory of external axioms with published literature citations.
