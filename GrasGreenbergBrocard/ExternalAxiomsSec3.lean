import Mathlib
import GrasGreenbergBrocard.Basic

/-!
# External Analytic and Iwasawa-Theoretic Axioms for Section 3

All external axioms in this file encode established peer-reviewed mathematical results
external to the manuscript's own contributions, where Mathlib v4.35.0 does not yet
contain a formalization. Zero manuscript-owned lemmas, propositions, or theorems
are axiomatized here.

Every axiom is documented in `EXTERNAL_AXIOMS.md` with its exact published source.
-/

noncomputable section

open Real Filter Asymptotics

namespace GrasGreenbergBrocard

/-- **Breusch (1932)**: Generalization of Bertrand's postulate to primes `p ≡ 3 [MOD 4]`.
For every real `x ≥ 7`, there exists a prime `p` with `x < p ≤ 2 * x` and `p % 4 = 3`.
Source: R. Breusch, *Zur Verallgemeinerung des Bertrandschen Postulates, dass zwischen x und 2x
stets Primzahlen liegen*, Math. Z. 34 (1932), 505–526. -/
axiom breusch_bertrand_mod4 :
    ∀ x : ℝ, 7 ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ p % 4 = 3

/-- **Rosser–Schoenfeld (1962, Theorem 10)**: Explicit Chebyshev `ϑ(n) - ϑ(n/2) > 0.4 * n`
for all `n ≥ 116`.
Source: J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*,
Illinois J. Math. 6 (1962), Theorem 10. -/
axiom rosser_schoenfeld_theta_diff :
    ∀ n : ℕ, 116 ≤ n →
      0.4 * (n : ℝ) <
        ∑ p ∈ (Finset.Ioc (n / 2) n).filter Nat.Prime, Real.log (p : ℝ)

/-- **Stirling's Asymptotic Formula with `O(n⁻¹)` Remainder**:
`log(n!) = n log n - n + (1/2) log(2πn) + O(n⁻¹)`.
Source: Classical Euler–Maclaurin / Stirling expansion. -/
axiom stirling_log_factorial_remainder :
    (fun n : ℕ =>
      Real.log ((Nat.factorial n : ℕ) : ℝ) -
        ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + (1 / 2 : ℝ) * Real.log (2 * Real.pi * (n : ℝ))))
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹)

/-- **Erdős–Selfridge (1975)**: The product of two or more consecutive positive integers
is never a perfect power (in particular, never a square).
Source: P. Erdős and J. L. Selfridge, *The product of consecutive integers is never a power*,
Illinois J. Math. 19 (1975), 292–301. -/
axiom erdos_selfridge_consecutive_product_not_square :
    ∀ a k : ℕ, 1 ≤ a → 2 ≤ k → ¬ IsSquare (∏ j ∈ Finset.range k, (a + j))

/-- **Nagura (1952)**: For every `x ≥ 25`, there exists a prime `p` with `x < p < (6/5) * x`.
Source: J. Nagura, *On the interval containing at least one prime number*,
Proc. Japan Acad. 28 (1952), 177–181. -/
axiom nagura_prime_in_interval :
    ∀ x : ℝ, 25 ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < (6 / 5 : ℝ) * x

/-- Abstract package of algebraic and Iwasawa-theoretic invariants for the real quadratic field
`K = ℚ(√q)` at an odd prime `p ≥ 5`. -/
structure RealQuadIwasawaInvariants (q p : ℕ) where
  /-- Fundamental discriminant `D ∈ {q, 4q}`. -/
  D : ℕ
  hD : D = q ∨ D = 4 * q
  /-- Class number `h(q)` of `ℚ(√q)`. -/
  classNumber : ℕ
  hClass_pos : 0 < classNumber
  /-- `p`-adic valuation of the normalized `p`-adic regulator `R̃_p(K)`. -/
  v_reg : ℕ
  /-- `p`-adic valuation of `L_p(1, χ_D)`. -/
  v_Lp : ℕ
  /-- `p`-adic valuation of `#T_{K, p}` (order of the abelian `p`-ramification torsion group). -/
  v_T : ℕ
  /-- Whether `K` is `p`-rational (`T_{K, p} = 0`, equivalently `v_T = 0`). -/
  is_p_rational : Bool
  h_prat_iff : is_p_rational = true ↔ v_T = 0
  /-- `p`-ramified Iwasawa `λ`-invariant `λ_p^*(K) = rank_{ℤ_p} X_p(K_∞)`. -/
  lambda_star : ℕ
  /-- Kubota–Leopoldt `λ`-invariant `λ_p(χ_D)`. -/
  lambda_chi : ℕ
  /-- Whether `p` splits in `K` (`χ_D(p) = +1`). -/
  splits : Bool
  /-- `p`-adic valuation of `|X(K_∞)_Γ|` and `|A_m^Γ|`. -/
  v_X_Gamma : ℕ
  v_A_m_Gamma : ℕ → ℕ
  /-- Unramified Iwasawa invariants `λ_p(K)` and `ν_p(K)`. -/
  lambda_p : ℕ
  nu_p : ℕ
  /-- Taya's `r`-th layer `p`-unit invariant `n_0^{(r)}(K)`. -/
  n0_r : ℕ → ℕ
  /-- Whether the unramified Iwasawa module `X(K_∞)` is trivial (`λ_p = ν_p = 0`). -/
  X_trivial : Bool
  h_X_triv : X_trivial = true ↔ lambda_p = 0 ∧ nu_p = 0

/-- Canonical algebraic and Iwasawa-theoretic invariants of the real quadratic field
`K = ℚ(√q)` at an odd prime `p ≥ 5`. Scoping the external Iwasawa axioms strictly to this
canonical object (rather than quantifying universally over arbitrary unconstrained records)
prevents inconsistency from adversarial dummy instances. -/
axiom canonicalRealQuadIwasawa (q p : ℕ) : RealQuadIwasawaInvariants q p

/-- **Leopoldt's `p`-Adic Class Number Formula (Washington 1997, Theorem 5.24)** and
**Coates's Formula (Coates 1977, Appendix Lemma 8; Taya 1996, Prop. 1)** for `K = ℚ(√q)` at `p ≥ 5`. -/
axiom leopoldt_coates_valuation_law :
    ∀ {q p : ℕ},
      let inv := canonicalRealQuadIwasawa q p
      p.Prime → 5 ≤ p → 1 ≤ inv.v_reg →
      ((¬ p ∣ q →
          inv.v_Lp = padicValNat p inv.classNumber + inv.v_reg - 1 ∧
          inv.v_T = padicValNat p inv.classNumber + inv.v_reg - 1) ∧
       (p ∣ q →
          inv.v_Lp = padicValNat p inv.classNumber + inv.v_reg ∧
          inv.v_T = padicValNat p inv.classNumber + inv.v_reg))

/-- **Ferrero–Washington (1979), Mazur–Wiles (1984), and Greenberg (1978, Prop. 3)**:
For the real quadratic field `K = ℚ(√q)` at `p ≥ 5`, `μ_p(χ_D) = 0`, `X_p(K_∞)` is a free
`ℤ_p`-module of rank `λ_p^*(K) = λ_p(χ_D)`, and `T_{K,p} ≠ 0` (`1 ≤ inv.v_T`) implies
`λ_p^*(K) = λ_p(χ_D) ≥ 1`. -/
axiom iwasawa_main_conjecture_free_rank :
    ∀ {q p : ℕ},
      let inv := canonicalRealQuadIwasawa q p
      p.Prime → 5 ≤ p → 1 ≤ inv.v_T →
      inv.lambda_star = inv.lambda_chi ∧ 1 ≤ inv.lambda_star

/-- **Ozaki (1997, Prop. 1), Yanagisawa (2026, Lemmas 6.1–6.2), and Taya (1996, Cor. 2–3, Thm. 4)**:
For a split prime `p ≥ 5` (`¬ p ∣ q`, `inv.splits = true`) with `2 ≤ inv.v_reg`:
- `|X(K_∞)_Γ| = |A_m^Γ| = |T_{K, p}|` for all `m ≥ inv.v_reg - 1`,
- `λ_p(K) + ν_p(K) ≥ inv.v_reg - 1`,
- If `n_0^{(r)}(K) > r + 1` for all `r ≥ 0`, then `λ_p(K) ≥ 1`. -/
axiom ozaki_taya_split_prime_iwasawa :
    ∀ {q p : ℕ},
      let inv := canonicalRealQuadIwasawa q p
      p.Prime → 5 ≤ p → ¬ p ∣ q → inv.splits = true → 2 ≤ inv.v_reg →
      (∀ m : ℕ, inv.v_reg - 1 ≤ m →
        inv.v_X_Gamma = inv.v_T ∧ inv.v_A_m_Gamma m = inv.v_T) ∧
      inv.v_reg - 1 ≤ inv.lambda_p + inv.nu_p ∧
      ((∀ r : ℕ, r + 1 < inv.n0_r r) → 1 ≤ inv.lambda_p)

end GrasGreenbergBrocard
