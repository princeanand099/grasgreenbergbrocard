import Mathlib

/-!
# External Analytic Axioms for Section 4

All external axioms in this file encode established peer-reviewed mathematical results
external to the manuscript's own contributions, where Mathlib v4.35.0 does not yet
contain a formalization. Zero manuscript-owned lemmas, propositions, or theorems
are axiomatized here.

Every axiom is documented in `EXTERNAL_AXIOMS.md` with its exact published source.
-/

noncomputable section

open Real Filter Asymptotics Finset

namespace GrasGreenbergBrocard

/-- **Mertens' First Theorem on Odd Primes** (Mertens 1874; Davenport, *Multiplicative Number Theory*,
3rd ed., Ch. 7):
`∑_{3 ≤ p ≤ x} (log p) / (p - 1) = log x - γ - log 2 + o(1)` as `x → ∞`,
where `γ ≈ 0.57721566...` is the Euler–Mascheroni constant (`0.5772 < γ < 0.5773`). -/
axiom mertens_first_theorem_odd_primes :
    ∃ γ : ℝ, 0.5772 < γ ∧ γ < 0.5773 ∧
      (fun x : ℕ =>
        (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, Real.log (p : ℝ) / ((p : ℝ) - 1)) -
          (Real.log (x : ℝ) - γ - Real.log 2))
        =o[atTop] (fun _ : ℕ => (1 : ℝ))

/-- **Prime Number Theorem (`n`-th Prime Asymptotic)** (Hadamard / de la Vallée Poussin 1896;
Davenport, *Multiplicative Number Theory*, Ch. 18):
The `k`-th prime `p_k` (`Nat.nth Nat.Prime k`, 0-indexed so `p_0 = 2, p_1 = 3, ...`) satisfies
`p_k / (k * log k) → 1` as `k → ∞`. -/
axiom nth_prime_asymptotic :
    Tendsto (fun k : ℕ => (Nat.nth Nat.Prime k : ℝ) / ((k : ℝ) * Real.log (k : ℝ))) atTop (nhds 1)

end GrasGreenbergBrocard
