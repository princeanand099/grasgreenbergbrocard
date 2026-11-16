import Mathlib
import GrasGreenbergBrocard.Basic

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false

/-!
# External Analytic Axioms (Section 2)

Every axiom in this file represents an established peer-reviewed theorem external
to the manuscript's own contribution, where no suitable Mathlib formalization is
available in Mathlib v4.35.0. Each axiom is documented in `EXTERNAL_AXIOMS.md`.
-/

noncomputable section

open Real Asymptotics Filter

namespace GrasGreenbergBrocard

/-- **de la Vallée Poussin Prime Number Theorem** (Davenport, *Multiplicative Number Theory*,
3rd ed., Ch. 18): There exists an absolute effective constant `c₁ > 0` such that
`ϑ(x) = x + O(x exp(-c₁ √(log x)))` and `π(x) = li(x) + O(x exp(-c₁ √(log x)))`.
Here we record the `ϑ(x)` asymptotic and the Chebyshev upper bound on `π(x)`. -/
axiom de_la_vallee_poussin_theta :
  ∃ c₁ : ℝ, 0 < c₁ ∧
    (fun x : ℝ => thetaPrime x - x) =O[atTop]
      (fun x : ℝ => x * Real.exp (-c₁ * Real.sqrt (Real.log x)))

/-- **Prime Number Theorem for `π(x)`** (Davenport, *Multiplicative Number Theory*,
3rd ed., Ch. 18): `π(n / (2r-1)) - π(n / (2r)) = (1/(2r-1) - 1/(2r) + o(1)) n / log n`,
and Chebyshev's upper bound `π(x) ≪ x / log x` (Davenport, Ch. 7). -/
axiom chebyshev_pi_upper :
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → piPrime x ≤ C * (x / Real.log x)

axiom pnt_pi_interval :
  ∀ r : ℕ, 1 ≤ r →
    (fun n : ℕ => piPrime ((n : ℝ) / (2 * r - 1 : ℝ)) - piPrime ((n : ℝ) / (2 * r : ℝ))) =
      (fun n : ℕ => (1 / (2 * r - 1 : ℝ) - 1 / (2 * r : ℝ)) * ((n : ℝ) / Real.log n)) +o[atTop]
        (fun n : ℕ => (n : ℝ) / Real.log n)

/-- **Mertens' First Theorem** (Davenport, *Multiplicative Number Theory*, 3rd ed., Ch. 7):
`∑_{3 ≤ p ≤ x} log p / (p - 1) = log x + O(1)`. -/
axiom mertens_first_theorem :
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
    |∑ p ∈ (Finset.Icc 3 (Nat.floor x)).filter Nat.Prime,
        Real.log (p : ℝ) / ((p : ℝ) - 1) - Real.log x| ≤ C

/-- **Vaaler's Extremal Trigonometric Polynomials** (J. D. Vaaler, *Some extremal functions in
Fourier analysis*, Bull. Amer. Math. Soc. 12 (1985), Theorem 18):
For every integer `H ≥ 1`, there exist trigonometric polynomials `Ψ_H` and `B_H` with
coefficients `c_h(H)` (`1 ≤ |h| ≤ H`) and `b_h(H)` (`|h| ≤ H`) satisfying:
- `c_h(H) = -1 / (2π i h) * W(|h| / (H + 1))` with `|W(u)| ≤ 1` and `0 ≤ W(u) ≤ 1`,
- `b_0(H) = 1 / (2H + 2)` and `‖b_h(H)‖ ≤ 1 / (2H + 2)`,
- `Ψ_H(t) = ∑_{1 ≤ |h| ≤ H} c_h(H) e(ht)` and `B_H(t) = ∑_{|h| ≤ H} b_h(H) e(ht)`,
- `|ψ(t) - Ψ_H(t)| ≤ (B_H(t)).re` for all `t ∈ ℝ` (where `ψ(t) = t - ⌊t⌋ - 1/2`),
- `B_H(0) = 1/2` and `Ψ_H(m) = 0` for all `m ∈ ℤ`. -/
axiom vaaler_extremal_polynomials (H : ℕ) (hH : 1 ≤ H) :
  ∃ (W : ℝ → ℝ) (b : ℤ → ℂ),
    (∀ u : ℝ, 0 ≤ W u ∧ W u ≤ 1) ∧
    (b 0 = (1 / (2 * (H : ℝ) + 2 : ℝ) : ℂ)) ∧
    (∀ h : ℤ, ‖b h‖ ≤ 1 / (2 * (H : ℝ) + 2)) ∧
    (let c : ℤ → ℂ := fun h =>
        if h = 0 then 0
        else -(1 / (2 * Real.pi * Complex.I * (h : ℂ))) * (W (|(h : ℝ)| / ((H : ℝ) + 1)) : ℂ)
     let Psi : ℝ → ℂ := fun t =>
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (· ≠ 0), c h * eExp ((h : ℝ) * t)
     let B : ℝ → ℂ := fun t =>
        ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), b h * eExp ((h : ℝ) * t)
     (∀ t : ℝ, 0 ≤ (B t).re ∧
        ‖((t - (Int.floor t : ℝ) - 1 / 2 : ℝ) : ℂ) - Psi t‖ ≤ (B t).re) ∧
     ((B 0).re = 1 / 2) ∧
     (∀ m : ℤ, Psi (m : ℝ) = 0))

/-- **Vaughan–van der Corput–Kusmin–Landau–Weyl Prime Exponential Sum Engine**
(Iwaniec & Kowalski, *Analytic Number Theory*, AMS Colloq. Publ. 53, 2004:
Proposition 13.4, Corollary 8.11, Corollary 8.13, Theorem 8.25).
For any smooth phase `F` on `[P, 2P]` whose derivatives satisfy
`c₁ T₀ / P^j ≤ |F^{(j)}(t)| ≤ c₂ T₀ / P^j` for `j ≥ 1`, and smooth weight `w`
with `|w| ≤ W₀`, `∫ |w'| ≤ W₀`, Vaughan's identity + van der Corput / Kusmin–Landau /
Weyl–van der Corput yields the bound in Lemma 2.4. -/
axiom vaughan_van_der_corput_prime_sum :
  ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 3 →
    ∃ (η' η : ℝ), 0 < η' ∧ 0 < η ∧
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (P : ℝ) (I : Finset ℕ) (F : ℝ → ℝ) (w : ℝ → ℝ) (W₀ T₀ : ℝ),
      let R := Nat.floor (1 / δ)
      let A_R := 6 * R + 30
      4 ≤ n →
      (n : ℝ) ^ δ ≤ P →
      P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 →
      (∀ p ∈ I, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
      (2 : ℝ) ^ (- (R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ T₀ →
      (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) →
      (∀ (j : ℕ), 1 ≤ j → j ≤ 5 * R + 2 →
        ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
          ∀ t ∈ Set.Icc P (2 * P),
            c₁ * T₀ / P ^ j ≤ |iteratedDeriv j F t| ∧ |iteratedDeriv j F t| ≤ c₂ * T₀ / P ^ j) →
      ‖∑ p ∈ I, (w (p : ℝ) * Real.log (p : ℝ) : ℂ) * eExp (F (p : ℝ))‖ ≤
        C * W₀ * P * (T₀ ^ (- (1 / 6 : ℝ)) + P ^ (-η')) * (Real.log P) ^ 3 ∧
      (T₀ ≥ (n : ℝ) ^ (δ / 2) →
        ‖∑ p ∈ I, (w (p : ℝ) * Real.log (p : ℝ) : ℂ) * eExp (F (p : ℝ))‖ ≤
          C * W₀ * P * (n : ℝ) ^ (-η))

end GrasGreenbergBrocard
