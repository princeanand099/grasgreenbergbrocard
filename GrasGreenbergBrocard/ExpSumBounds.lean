import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false

/-!
# Lemma 2.4: Prime Exponential Sum Bound on `[n^δ, n / (log n)^12]`

Formalizes Section 2.3 (eq. 2.11–2.14):
- Transition collars `C_r(n)` (eq. 2.11), subintervals `J_{r, m_r}` (eq. 2.12),
  and inter-collar intervals `D_r(n)`.
- `iteratedDeriv_neg_pow`: exact `j`-th derivative of `t ↦ t^(-r : ℤ)` for `t > 0`.
- `phase_iteratedDeriv_bounds`: `r₀`-domination for `F(t) = ∑_{r ∈ A} h_r n / (2 t^r)`.
- `prime_exp_sum_bound_general` (Lemma 2.4(i), eq. 2.13).
- `prime_exp_sum_bound_collar` (Lemma 2.4(ii), eq. 2.14).
-/

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard

/-- Transition collar `C_r(n) := (n^{1/r} / (log n)^{A_R / r}, n^{1/r}]` (eq. 2.11). -/
def collar (n r A_R : ℕ) : Set ℝ :=
  Set.Ioc
    ((n : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)))
    ((n : ℝ) ^ (1 / (r : ℝ)))

/-- Collar subinterval `J_{r, m_r} := ((n/(m_r+1))^{1/r}, (n/m_r)^{1/r}] ∩ C_r(n)` (eq. 2.12). -/
def collarSubinterval (n r m_r A_R : ℕ) : Set ℝ :=
  Set.Ioc
    (((n : ℝ) / ((m_r : ℝ) + 1)) ^ (1 / (r : ℝ)))
    (((n : ℝ) / (m_r : ℝ)) ^ (1 / (r : ℝ))) ∩ collar n r A_R

/-- Complementary inter-collar interval `D_r(n) := (n^{1/(r+1)}, n^{1/r} / (log n)^{A_R / r}]`. -/
def interCollar (n r A_R : ℕ) : Set ℝ :=
  Set.Ioc
    ((n : ℝ) ^ (1 / ((r : ℝ) + 1)))
    ((n : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)))

/-- Falling-rising factorial coefficient for `j`-th derivative of `t^(-r)`:
`(-1)^j * ∏_{k < j} (r + k)`. -/
def negPowDerivCoeff (r j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * ∏ k ∈ Finset.range j, ((r + k : ℕ) : ℝ)

theorem abs_negPowDerivCoeff_pos {r j : ℕ} (hr : 1 ≤ r) :
    0 < |negPowDerivCoeff r j| := by
  unfold negPowDerivCoeff
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_of_nonneg (Finset.prod_nonneg (fun k _ => by positivity))]
  refine Finset.prod_pos (fun k _ => ?_)
  exact_mod_cast (by omega : 0 < r + k)

/-- Exact `j`-th derivative of `t ↦ t^(-(r : ℤ))` on `{t | 0 < t}`. -/
theorem iteratedDeriv_neg_pow (r j : ℕ) :
    ∀ t : ℝ, 0 < t →
      iteratedDeriv j (fun x : ℝ => x ^ (-(r : ℤ))) t =
        negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ)) := by
  induction j with
  | zero =>
    intro t _
    simp [negPowDerivCoeff]
  | succ j ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have heq : Set.EqOn (iteratedDeriv j (fun x : ℝ => x ^ (-(r : ℤ))))
        (fun x : ℝ => negPowDerivCoeff r j * x ^ (-((r + j : ℕ) : ℤ))) (Set.Ioi 0) :=
      fun x hx => ih x hx
    have hderiv_eq : deriv (iteratedDeriv j (fun x : ℝ => x ^ (-(r : ℤ)))) t =
        deriv (fun x : ℝ => negPowDerivCoeff r j * x ^ (-((r + j : ℕ) : ℤ))) t :=
      Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) heq)
    rw [hderiv_eq]
    have hhas : HasDerivAt (fun x : ℝ => negPowDerivCoeff r j * x ^ (-((r + j : ℕ) : ℤ)))
        (negPowDerivCoeff r j * ((-((r + j : ℕ) : ℤ) : ℝ) * t ^ (-((r + j : ℕ) : ℤ) - 1))) t := by
      apply HasDerivAt.const_mul
      exact hasDerivAt_zpow (-((r + j : ℕ) : ℤ)) t (Or.inl ht.ne')
    rw [hhas.deriv]
    unfold negPowDerivCoeff
    rw [Finset.prod_range_succ, pow_succ]
    have hexp : (-((r + j : ℕ) : ℤ) - 1) = -((r + (j + 1) : ℕ) : ℤ) := by omega
    rw [hexp]
    push_cast
    ring

/-- **Lemma 2.4(i) and (ii) (Prime Exponential Sum Bound on `[n^δ, n/(log n)^12]`)**:
For any `δ ∈ (0, 1/3]`, `R = ⌊1/δ⌋`, `A_R = 6R + 30`, `H = ⌊(log n)^{R+2}⌋`,
and phase `F(t) = ∑_{r ∈ A} (h_r n) / (2 t^r)` with `h ≠ 0`, `|h_r| ≤ 2H + 1`,
and `T₀ = |h_{r₀}| n / P^{r₀} ≥ 2^{-R} (log n)^{A_R}`, both (2.13) and (2.14) hold
for all sufficiently large `n`. -/
theorem prime_exp_sum_bounds (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    ∃ (η' η : ℝ), 0 < η' ∧ 0 < η ∧
    ∃ (C₁ C₂ C₃ : ℝ), 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
    ∀ᶠ n : ℕ in atTop,
      let R := Nat.floor (1 / δ)
      let A_R := 6 * R + 30
      let H := Nat.floor ((Real.log (n : ℝ)) ^ (R + 2))
      ∀ (P : ℝ) (I : Finset ℕ) (A : Finset ℕ) (h : ℕ → ℤ) (w : ℝ → ℝ) (W₀ : ℝ),
        (n : ℝ) ^ δ ≤ P →
        P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 →
        (∀ p ∈ I, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
        (∀ r ∈ A, 1 ≤ r ∧ r ≤ R) →
        (∃ r ∈ A, h r ≠ 0) →
        (∀ r ∈ A, |(h r : ℤ)| ≤ 2 * (H : ℤ) + 1) →
        (∀ r ∈ A, (2 : ℝ) ^ (- (R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) / P ^ r) →
        (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) →
        0 ≤ W₀ →
        let r₀ := (A.filter (fun r => h r ≠ 0)).min' (by
          obtain ⟨r, hrA, hr0⟩ := ‹∃ r ∈ A, h r ≠ 0›
          exact ⟨r, Finset.mem_filter.mpr ⟨hrA, hr0⟩⟩)
        let T₀ := |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀
        let F : ℝ → ℝ := fun t => ∑ r ∈ A, (h r : ℝ) * (n : ℝ) / (2 * t ^ r)
        (‖∑ p ∈ I, (w (p : ℝ) * Real.log (p : ℝ) : ℂ) * eExp (F (p : ℝ))‖ ≤
          C₁ * W₀ * P * (T₀ ^ (-(1 / 6 : ℝ)) + P ^ (-η')) * (Real.log P) ^ 3 ∧
         ‖∑ p ∈ I, (w (p : ℝ) * Real.log (p : ℝ) : ℂ) * eExp (F (p : ℝ))‖ ≤
          C₂ * W₀ * P * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) ∧
        (T₀ ≥ (n : ℝ) ^ (δ / 2) →
          ‖∑ p ∈ I, (w (p : ℝ) * Real.log (p : ℝ) : ℂ) * eExp (F (p : ℝ))‖ ≤
            C₃ * W₀ * P * (n : ℝ) ^ (-η)) := by
  obtain ⟨η', η, hη', hη, C, hC, hVaughan⟩ := vaughan_van_der_corput_prime_sum δ hδ0 hδ1
  refine ⟨η', η, hη', hη, C, ?_, C, ?_, C, ?_, ?_⟩
  · positivity
  · positivity
  · positivity
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    -- Note: for full derivative domination we need (H / P) small; since H ≤ (log n)^{R+2} and P ≥ n^δ,
    -- we can refine the filter threshold inside the existential if needed, or even better,
    -- let's check what filter threshold we need!
    sorry

end GrasGreenbergBrocard
