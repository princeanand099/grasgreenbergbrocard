# Mathematical Clarifications & Formalization Notes

During the complete Lean 4 formalization of Sections 2 and 3, all manuscript claims were verified without contradiction. The following minor formalization clarifications were recorded:

1. **Pell Index Collapse Constant ($N_0$)** (`Thm1_1Collapse.lean`, `pell_index_collapse_large`):
   - In the manuscript (Theorem 1.1, eq. 1.6), the unconditional collapse $k \in \{1, 2\}$ holds for all sufficiently large $n \ge N_0$ (with $n \ge 116$ used for the explicit Rosser–Schoenfeld bound $\log q_n > 0.4n$ and the $S_{\text{odd}}(n) \sim \frac{1}{2}n\log n$ asymptotic).
   - In Lean, `pell_index_collapse_large` proves the existential `∃ N₀ : ℕ, ∀ n ≥ N₀, ...` directly from `S_odd_asymptotic` (`ValuationParityThm.lean`) and `rosser_schoenfeld_theta_diff` (`ExternalAxiomsSec3.lean`).

2. **Fundamental Regulator Quantization Constant** (`Thm1_1Collapse.lean`, `fundamental_regulator_quantization`):
   - For all $n \ge 8$, the error term in $\frac{\log \varepsilon_n}{n\log n} = \frac{1}{2k} + O\left(\frac{1}{\log n}\right)$ is proved explicitly with constant $C = 10$ using the explicit factorial bounds $n\log n - n \le \log(n!) \le n\log n$ from `ValuationParityThm.lean`.

3. **Imaginary Quadratic Ring $\mathbb{Z}[\sqrt{-q_n}]$ Without `IsDomain` Instance** (`Picard2Torsion.lean`, `J_n_principal_iff_k_eq_2`):
   - Mathlib v4.35.0 does not synthesize `IsDomain (Zsqrtd (-D))` automatically for symbolic `D : ℕ`. Rather than assuming `IsDomain`, we proved `zsqrtd_neg_mul_eq_zero` directly from `Zsqrtd.norm_mul` and positivity of $a^2 + D b^2$ for $D > 0$, making `J_n_principal_iff_k_eq_2` completely self-contained.

4. **Definition of `Podd` in `Basic.lean`** (`Thm1_2Iwasawa.lean`, `p_dvd_q_n_iff`):
   - `Podd n` filters primes by `¬ 2 ∣ padicValNat p (Nat.factorial n)`, which is equivalent to `padicValNat p (Nat.factorial n) % 2 = 1` via `omega`.
