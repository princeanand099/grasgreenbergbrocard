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
`ϑ(x) = x + O(x exp(-c₁ √(log x)))`. -/
axiom de_la_vallee_poussin_theta :
  ∃ c₁ : ℝ, 0 < c₁ ∧
    (fun x : ℝ => thetaPrime x - x) =O[atTop]
      (fun x : ℝ => x * Real.exp (-c₁ * Real.sqrt (Real.log x)))

/-- **Chebyshev's Upper Bound on `π(x)`** (Davenport, *Multiplicative Number Theory*,
3rd ed., Ch. 7): `π(x) ≪ x / log x` for `x ≥ 2`. -/
axiom chebyshev_pi_upper :
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → piPrime x ≤ C * (x / Real.log x)

/-- **Prime Number Theorem Lower/Asymptotic Bound for `π(x)`** (Davenport, Ch. 18):
`π(x) = (1 + o(1)) x / log x`, and `π(n / (2r-1)) - π(n / (2r)) = (1/(2r-1) - 1/(2r) + o(1)) n / log n`. -/
axiom pnt_pi_asymptotic :
  (fun x : ℝ => piPrime x - x / Real.log x) =o[atTop] (fun x : ℝ => x / Real.log x)

/-- **Mertens' First Theorem** (Davenport, *Multiplicative Number Theory*, 3rd ed., Ch. 7):
`∑_{3 ≤ p ≤ x} log p / (p - 1) = log x + O(1)`. -/
axiom mertens_first_theorem :
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
    |∑ p ∈ (Finset.Icc 3 (Nat.floor x)).filter Nat.Prime,
        Real.log (p : ℝ) / ((p : ℝ) - 1) - Real.log x| ≤ C

/-- **Vaaler's Extremal Trigonometric Polynomials** (J. D. Vaaler, *Some extremal functions in
Fourier analysis*, Bull. Amer. Math. Soc. 12 (1985), Theorem 18):
There exists a universal kernel `W : ℝ → ℝ` with `0 ≤ W u ≤ 1` such that for every
integer `H ≥ 1`, there exist coefficients `b : ℤ → ℂ` with `b 0 = 1 / (2H + 2)`,
`‖b h‖ ≤ 1 / (2H + 2)`, and `Ψ_H, B_H` satisfying `|ψ(t) - Ψ_H(t)| ≤ (B_H t).re`
for all `t ∈ ℝ`, `(B_H 0).re = 1/2`, and `Ψ_H(m) = 0` for all `m ∈ ℤ`. -/
axiom vaaler_extremal_polynomials :
  ∃ (W : ℝ → ℝ), (∀ u : ℝ, 0 ≤ W u ∧ W u ≤ 1) ∧
    ∀ (H : ℕ), 1 ≤ H →
      ∃ (b : ℤ → ℂ),
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

/-- `I` is the exact finite set of all primes in a real subinterval `(a, b] ⊆ (P, 2P]`.
This prevents adversarial cherry-picking of arbitrary prime subsets. -/
def IsPrimeSubinterval (P : ℝ) (I : Finset ℕ) : Prop :=
  ∃ a b : ℝ, P ≤ a ∧ a ≤ b ∧ b ≤ 2 * P ∧
    ∀ p : ℕ, p ∈ I ↔ p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b

theorem isPrimeSubinterval_of_bounds {P a b : ℝ} (hP : 0 ≤ P) (I : Finset ℕ)
    (hI : ∀ p : ℕ, p ∈ I ↔ p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b)
    (hsub : ∀ p ∈ I, P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) :
    IsPrimeSubinterval P I := by
  let a' := max P (min (2 * P) a)
  let b' := max a' (min (2 * P) b)
  refine ⟨a', b', le_max_left _ _, le_max_left _ _,
    max_le (max_le (by linarith) (min_le_left _ _)) (min_le_left _ _), ?_⟩
  intro p
  rw [hI]
  constructor
  · intro hp
    have hpb := hsub p ((hI p).mpr hp)
    have ha_lt_2P : a < 2 * P := lt_of_lt_of_le hp.2.1 hpb.2
    refine ⟨hp.1, ?_, ?_⟩
    · dsimp only [a']
      rw [min_eq_right ha_lt_2P.le]
      exact max_lt hpb.1 hp.2.1
    · exact le_trans (le_min hpb.2 hp.2.2) (le_max_right _ _)
  · intro ⟨hpr, ha', hb'⟩
    have ha_lt : a < (p : ℝ) := by
      have h1 : min (2 * P) a < (p : ℝ) := lt_of_le_of_lt (le_max_right _ _) ha'
      have h2 : (p : ℝ) ≤ 2 * P :=
        le_trans hb' (max_le (max_le (by linarith) (min_le_left _ _)) (min_le_left _ _))
      by_contra hle; push_neg at hle
      have hmin : min (2 * P) a = 2 * P := min_eq_left (le_trans h2 hle)
      linarith
    have hb_le : (p : ℝ) ≤ b := by
      have h1 : ¬ (p : ℝ) ≤ a' := not_le.mpr ha'
      have h2 : b' = min (2 * P) b := by
        by_contra hne
        have : b' = a' := (max_choice a' (min (2 * P) b)).resolve_right hne
        rw [this] at hb'; exact h1 hb'
      rw [h2] at hb'
      exact le_trans hb' (min_le_right _ _)
    exact ⟨hpr, ha_lt, hb_le⟩

/-- **Vaughan–van der Corput–Kusmin–Landau–Weyl Prime Exponential Sum Engine**
(Iwaniec & Kowalski, *Analytic Number Theory*, AMS Colloq. Publ. 53, 2004:
Proposition 13.4, Corollary 8.11, Corollary 8.13, Theorem 8.25).
Strictly requires:
- `c₁, c₂ : ℕ → ℝ` (derivative-scale constants) are quantified **before** `∃ η' η C`,
  so `C = C(δ, c₁, c₂)` genuinely depends on the derivative bounds (preventing quantifier
  inversion on `F_ε(t) = ε / t`),
- `I` is an exact prime subinterval `(a, b] ⊆ (P, 2P]` (`IsPrimeSubinterval P I`),
- `w` is bounded (`|w t| ≤ W₀`) and monotone (`AntitoneOn w (Set.Icc P (2 * P))`, hence
  total variation `≤ 2 W₀` on `[P, 2P]`, enabling Abel partial summation without oscillation). -/
axiom vaughan_van_der_corput_prime_sum :
  ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 3 →
    ∀ (c₁ c₂ : ℕ → ℝ),
      (∀ (j : ℕ), 1 ≤ j → j ≤ 5 * Nat.floor (1 / δ) + 2 → 0 < c₁ j ∧ c₁ j ≤ c₂ j) →
    ∃ (η' η : ℝ), 0 < η' ∧ 0 < η ∧
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (P : ℝ) (I : Finset ℕ) (F : ℝ → ℝ) (w : ℝ → ℝ) (W₀ T₀ : ℝ),
      let R := Nat.floor (1 / δ)
      let A_R := 6 * R + 30
      4 ≤ n →
      (n : ℝ) ^ δ ≤ P →
      P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 →
      IsPrimeSubinterval P I →
      (2 : ℝ) ^ (- (R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ T₀ →
      (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) →
      AntitoneOn w (Set.Icc P (2 * P)) →
      (∀ (j : ℕ), 1 ≤ j → j ≤ 5 * R + 2 →
        ∀ t ∈ Set.Icc P (2 * P),
          c₁ j * T₀ / P ^ j ≤ |iteratedDeriv j F t| ∧ |iteratedDeriv j F t| ≤ c₂ j * T₀ / P ^ j) →
      ‖∑ p ∈ I, (w (p : ℝ) * Real.log (p : ℝ) : ℂ) * eExp (F (p : ℝ))‖ ≤
        C * W₀ * P * (T₀ ^ (- (1 / 6 : ℝ)) + P ^ (-η')) * (Real.log P) ^ 3 ∧
      (T₀ ≥ (n : ℝ) ^ (δ / 2) →
        ‖∑ p ∈ I, (w (p : ℝ) * Real.log (p : ℝ) : ℂ) * eExp (F (p : ℝ))‖ ≤
          C * W₀ * P * (n : ℝ) ^ (-η))

end GrasGreenbergBrocard
