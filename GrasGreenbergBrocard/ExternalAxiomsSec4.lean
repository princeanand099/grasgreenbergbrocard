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

end GrasGreenbergBrocard
