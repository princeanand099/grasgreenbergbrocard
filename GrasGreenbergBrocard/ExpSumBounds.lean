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
- `prime_exp_sum_bounds` (Lemma 2.4(i)–(ii), eq. 2.13–2.14).
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
      convert hasDerivAt_zpow (-((r + j : ℕ) : ℤ)) t (Or.inl ht.ne') using 2
      push_cast
      ring
    rw [hhas.deriv]
    unfold negPowDerivCoeff
    rw [Finset.prod_range_succ, pow_succ]
    have hexp : (-((r + j : ℕ) : ℤ) - 1) = -((r + (j + 1) : ℕ) : ℤ) := by omega
    rw [hexp]
    push_cast
    ring

/-- For `n` large enough, `(log n)^k / n^δ → 0`. -/
theorem log_pow_div_rpow_tendsto_zero (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ k / (n : ℝ) ^ δ) atTop (nhds 0) := by
  have hlo : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x ^ (δ / ((k : ℝ) + 1))) :=
    isLittleO_log_rpow_atTop (by positivity)
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x‖ ≤ 1 * ‖x ^ (δ / ((k : ℝ) + 1))‖ := hlo.bound (by norm_num)
  have htend : Tendsto (fun x : ℝ => x ^ (-(δ / ((k : ℝ) + 1)))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by positivity)
  have hev : ∀ᶠ x : ℝ in atTop,
      0 ≤ (Real.log x) ^ k / x ^ δ ∧
      (Real.log x) ^ k / x ^ δ ≤ x ^ (-(δ / ((k : ℝ) + 1))) := by
    have hx1 : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ x := eventually_ge_atTop 1
    filter_upwards [hx1, hbound] with x hx1 hb
    have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hx_pos : 0 < x := by linarith
    have hrpow_nn : 0 ≤ x ^ (δ / ((k : ℝ) + 1)) := by positivity
    rw [Real.norm_of_nonneg hlog_nn, Real.norm_of_nonneg hrpow_nn, one_mul] at hb
    constructor
    · positivity
    · calc (Real.log x) ^ k / x ^ δ
          ≤ (x ^ (δ / ((k : ℝ) + 1))) ^ k / x ^ δ :=
            div_le_div_of_nonneg_right (pow_le_pow_left₀ hlog_nn hb k) (by positivity)
        _ = x ^ ((k : ℝ) * (δ / ((k : ℝ) + 1)) - δ) := by
            rw [← Real.rpow_natCast (x ^ (δ / ((k : ℝ) + 1))) k,
              ← Real.rpow_mul hx_pos.le, ← Real.rpow_sub hx_pos]
            congr 1; ring
        _ = x ^ (-(δ / ((k : ℝ) + 1))) := by
            congr 1; field_simp; ring
  have h0 : Tendsto (fun x : ℝ => (Real.log x) ^ k / x ^ δ) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨X₁, hX₁⟩ := Metric.tendsto_atTop.mp htend ε hε
    obtain ⟨X₂, hX₂⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max X₁ X₂, fun x hx => ?_⟩
    have h1 := hX₁ x (le_trans (le_max_left _ _) hx)
    have h2 := hX₂ x (le_trans (le_max_right _ _) hx)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h2.1]
    rw [Real.dist_eq, sub_zero] at h1
    exact lt_of_le_of_lt (le_trans h2.2 (le_abs_self _)) h1
  exact h0.comp tendsto_natCast_atTop_atTop

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
      ∀ (P : ℝ) (I : Finset ℕ) (A : Finset ℕ) (h : ℕ → ℤ) (w : ℝ → ℝ) (W₀ : ℝ)
        (hA_nz : ∃ r ∈ A, h r ≠ 0),
        (n : ℝ) ^ δ ≤ P →
        P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 →
        (∀ p ∈ I, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
        (∀ r ∈ A, 1 ≤ r ∧ r ≤ R) →
        (∀ r ∈ A, |(h r : ℤ)| ≤ 2 * (H : ℤ) + 1) →
        (∀ r ∈ A, (2 : ℝ) ^ (- (R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) / P ^ r) →
        (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) →
        0 ≤ W₀ →
        let r₀ := (A.filter (fun r => h r ≠ 0)).min' (by
          obtain ⟨r, hrA, hr0⟩ := hA_nz
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
  let R := Nat.floor (1 / δ)
  let A_R := 6 * R + 30
  let Mmax : ℝ := (∏ k ∈ Finset.range (5 * R + 2), ((R + k : ℕ) : ℝ))
  let c₁_low : ℝ := (1 / 4 : ℝ) * (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ))
  let c₂_high : ℝ := (3 / 2 : ℝ) * Mmax
  let C₂ : ℝ := C * ((2 : ℝ) ^ ((R : ℝ) / 6) + 1)
  have hR1 : 1 ≤ R := by
    rw [Nat.floor_pos]
    exact (le_div_iff₀ hδ0).mpr (by linarith)
  have hM1 : (1 : ℝ) ≤ Mmax := by
    unfold Mmax
    have hN : 1 ≤ ∏ k ∈ Finset.range (5 * R + 2), (R + k) :=
      Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun k _ => by omega))
    exact_mod_cast hN
  refine ⟨η', η, hη', hη, C, C₂, C, hC, mul_pos hC (by positivity), hC, ?_⟩
  have htend1 : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ) atTop (nhds 0) :=
    log_pow_div_rpow_tendsto_zero (R + 2) hδ0
  have htend2 : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ (R + 5) / (n : ℝ) ^ (δ * η')) atTop (nhds 0) :=
    log_pow_div_rpow_tendsto_zero (R + 5) (mul_pos hδ0 hη')
  have hev1 : ∀ᶠ n : ℕ in atTop,
      (2 * (Real.log (n : ℝ)) ^ (R + 2) + 1) / (n : ℝ) ^ δ * ((R : ℝ) * Mmax + 1) ≤ c₁_low := by
    have h0 : Tendsto (fun n : ℕ => (2 * (Real.log (n : ℝ)) ^ (R + 2) + 1) / (n : ℝ) ^ δ * ((R : ℝ) * Mmax + 1))
        atTop (nhds 0) := by
      have ht0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ δ) atTop (nhds 0) := by
        simpa using log_pow_div_rpow_tendsto_zero 0 hδ0
      have heq : (fun n : ℕ => (2 * (Real.log (n : ℝ)) ^ (R + 2) + 1) / (n : ℝ) ^ δ * ((R : ℝ) * Mmax + 1)) =
          (fun n : ℕ => (2 * ((Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ) + (1 : ℝ) / (n : ℝ) ^ δ) *
            ((R : ℝ) * Mmax + 1)) := by
        ext n; ring
      rw [heq]
      simpa using ((htend1.const_mul 2).add ht0).mul_const ((R : ℝ) * Mmax + 1)
    have hc₁_pos : 0 < c₁_low := by
      unfold c₁_low
      exact mul_pos (by norm_num) (zpow_pos (by norm_num) _)
    exact h0.eventually (ge_mem_nhds hc₁_pos)
  have hev2 : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ)) ^ (R + 5) / (n : ℝ) ^ (δ * η') ≤ 1 :=
    htend2.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hev_log : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ Real.log (n : ℝ) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [Filter.eventually_ge_atTop 4, hev1, hev2, hev_log] with n hn hsmall1 hsmall2 hlog2
  dsimp only
  intro P I A h w W₀ hA_nz hP_lo hP_hi hI_prime hA_range hh_bound hPhase hW_bound hW₀
  have hne_flt : (A.filter (fun r => h r ≠ 0)).Nonempty := by
    obtain ⟨r, hrA, hr0⟩ := hA_nz
    exact ⟨r, Finset.mem_filter.mpr ⟨hrA, hr0⟩⟩
  set r₀ := (A.filter (fun r => h r ≠ 0)).min' hne_flt
  set T₀ := |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀
  set F : ℝ → ℝ := fun t => ∑ r ∈ A, (h r : ℝ) * (n : ℝ) / (2 * t ^ r)
  have hr₀_flt : r₀ ∈ A.filter (fun r => h r ≠ 0) := Finset.min'_mem _ hne_flt
  have hr₀_mem : r₀ ∈ A := (Finset.mem_filter.mp hr₀_flt).1
  have hr₀_ne : h r₀ ≠ 0 := (Finset.mem_filter.mp hr₀_flt).2
  have hr₀_range : 1 ≤ r₀ ∧ r₀ ≤ R := hA_range r₀ hr₀_mem
  have hT₀_ge : (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ T₀ := by
    have hh1 : (1 : ℝ) ≤ |(h r₀ : ℝ)| := by exact_mod_cast Int.one_le_abs hr₀_ne
    calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R
        ≤ (n : ℝ) / P ^ r₀ := hPhase r₀ hr₀_mem
      _ = 1 * ((n : ℝ) / P ^ r₀) := (one_mul _).symm
      _ ≤ |(h r₀ : ℝ)| * ((n : ℝ) / P ^ r₀) := mul_le_mul_of_nonneg_right hh1 (by positivity)
      _ = T₀ := by ring
  have hP_ge1 : (1 : ℝ) ≤ P := by
    calc (1 : ℝ) ≤ (n : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) hδ0.le
      _ ≤ P := hP_lo
  have hP_pos : 0 < P := by linarith
  have hDeriv : ∀ (j : ℕ), 1 ≤ j → j ≤ 5 * R + 2 →
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
        ∀ t ∈ Set.Icc P (2 * P),
          c₁ * T₀ / P ^ j ≤ |iteratedDeriv j F t| ∧ |iteratedDeriv j F t| ≤ c₂ * T₀ / P ^ j := by
    intro j hj1 hj2
    have hc₁_pos : 0 < c₁_low := by
      unfold c₁_low
      exact mul_pos (by norm_num) (zpow_pos (by norm_num) _)
    refine ⟨c₁_low, c₂_high, hc₁_pos, ?_, ?_⟩
    · unfold c₁_low c₂_high
      have hpow_le : (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ)) ≤ 1 :=
        zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
      linarith
    · intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hP_pos ht.1
      have hF_eq : F = ∑ r ∈ A, fun x : ℝ => ((h r : ℝ) * (n : ℝ) / 2) * x ^ (-(r : ℤ)) := by
        ext x
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [zpow_neg, zpow_natCast]
        ring
      have hIter : iteratedDeriv j F t =
          ∑ r ∈ A, ((h r : ℝ) * (n : ℝ) / 2) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ)) := by
        rw [hF_eq]
        have hcd : ∀ r ∈ A, ContDiffAt ℝ j
            (fun x : ℝ => ((h r : ℝ) * (n : ℝ) / 2) * x ^ (-(r : ℤ))) t := by
          intro r _
          exact (contDiffAt_id.zpow (-(r : ℤ)) (Or.inl ht_pos.ne')).const_mul _
        rw [iteratedDeriv_sum hcd]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [iteratedDeriv_const_mul (contDiffAt_id.zpow (-(r : ℤ)) (Or.inl ht_pos.ne')),
          iteratedDeriv_neg_pow r j t ht_pos]
        ring
      rw [hIter]
      have hsplit := Finset.add_sum_erase A
        (fun r => ((h r : ℝ) * (n : ℝ) / 2) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ))) hr₀_mem
      rw [← hsplit]
      have hterm0_lo : 2 * c₁_low * T₀ / P ^ j ≤
          |((h r₀ : ℝ) * (n : ℝ) / 2) * negPowDerivCoeff r₀ j * t ^ (-((r₀ + j : ℕ) : ℤ))| := by
        rw [abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ)),
          abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos (zpow_pos ht_pos (-((r₀ + j : ℕ) : ℤ)))]
        have hcoeff_ge : (1 : ℝ) ≤ |negPowDerivCoeff r₀ j| := by
          unfold negPowDerivCoeff
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_nonneg (Finset.prod_nonneg (fun k _ => by positivity))]
          have hN : 1 ≤ ∏ k ∈ Finset.range j, (r₀ + k) :=
            Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun k _ => by omega))
          exact_mod_cast hN
        have ht_le : t ^ (-((r₀ + j : ℕ) : ℤ)) ≥ (2 * P) ^ (-((r₀ + j : ℕ) : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos ht_pos _) (pow_le_pow_left₀ ht_pos.le ht.2 _)
        have h2P : (2 * P) ^ (-((r₀ + j : ℕ) : ℤ)) ≥
            (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ)) * P ^ (-((r₀ + j : ℕ) : ℤ)) := by
          rw [mul_zpow]
          apply mul_le_mul_of_nonneg_right _ (zpow_nonneg hP_pos.le _)
          exact zpow_le_zpow_right₀ (by norm_num) (by omega)
        have hP_eq : P ^ (-((r₀ + j : ℕ) : ℤ)) = (1 / P ^ r₀) / P ^ j := by
          rw [zpow_neg, zpow_natCast, pow_add]
          field_simp [hP_pos.ne']
        calc 2 * c₁_low * T₀ / P ^ j
            = (1 / 2 : ℝ) * (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ)) *
                (|(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀) / P ^ j := by
              unfold c₁_low; ring
          _ = (|(h r₀ : ℝ)| * (n : ℝ) / 2) * 1 *
                ((2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ)) * ((1 / P ^ r₀) / P ^ j)) := by ring
          _ ≤ (|(h r₀ : ℝ)| * (n : ℝ) / 2) * |negPowDerivCoeff r₀ j| * t ^ (-((r₀ + j : ℕ) : ℤ)) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hcoeff_ge (by positivity)
              · rw [← hP_eq]; exact le_trans h2P ht_le
              · positivity
              · positivity
      have hterm0_hi : |((h r₀ : ℝ) * (n : ℝ) / 2) * negPowDerivCoeff r₀ j * t ^ (-((r₀ + j : ℕ) : ℤ))| ≤
          Mmax * T₀ / P ^ j := by
        rw [abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ)),
          abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos (zpow_pos ht_pos (-((r₀ + j : ℕ) : ℤ)))]
        have hcoeff_le : |negPowDerivCoeff r₀ j| ≤ Mmax := by
          unfold negPowDerivCoeff Mmax
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_nonneg (Finset.prod_nonneg (fun k _ => by positivity))]
          calc ∏ k ∈ Finset.range j, ((r₀ + k : ℕ) : ℝ)
              ≤ ∏ k ∈ Finset.range j, ((R + k : ℕ) : ℝ) := by
                refine Finset.prod_le_prod (fun k _ => by positivity) (fun k _ => ?_)
                exact_mod_cast (by omega : r₀ + k ≤ R + k)
            _ ≤ ∏ k ∈ Finset.range (5 * R + 2), ((R + k : ℕ) : ℝ) := by
                have hN : ∏ k ∈ Finset.range j, (R + k) ≤ ∏ k ∈ Finset.range (5 * R + 2), (R + k) :=
                  Finset.prod_le_prod_of_subset_of_one_le' (Finset.range_mono hj2)
                    (fun k _ _ => by omega)
                exact_mod_cast hN
        have ht_ge : t ^ (-((r₀ + j : ℕ) : ℤ)) ≤ P ^ (-((r₀ + j : ℕ) : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos hP_pos _) (pow_le_pow_left₀ hP_pos.le ht.1 _)
        have hP_eq : P ^ (-((r₀ + j : ℕ) : ℤ)) = (1 / P ^ r₀) / P ^ j := by
          rw [zpow_neg, zpow_natCast, pow_add]
          field_simp [hP_pos.ne']
        calc (|(h r₀ : ℝ)| * (n : ℝ) / 2) * |negPowDerivCoeff r₀ j| * t ^ (-((r₀ + j : ℕ) : ℤ))
            ≤ (|(h r₀ : ℝ)| * (n : ℝ) / 2) * Mmax * ((1 / P ^ r₀) / P ^ j) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hcoeff_le (by positivity)
              · rw [← hP_eq]; exact ht_ge
              · positivity
              · positivity
          _ ≤ Mmax * T₀ / P ^ j := by
              have h2_le : (1 / 2 : ℝ) ≤ 1 := by norm_num
              calc (|(h r₀ : ℝ)| * (n : ℝ) / 2) * Mmax * ((1 / P ^ r₀) / P ^ j)
                  = (1 / 2 : ℝ) * (Mmax * T₀ / P ^ j) := by unfold T₀; ring
                _ ≤ 1 * (Mmax * T₀ / P ^ j) := mul_le_mul_of_nonneg_right h2_le (by positivity)
                _ = Mmax * T₀ / P ^ j := one_mul _
      have htail_hi : |∑ r ∈ A.erase r₀,
          ((h r : ℝ) * (n : ℝ) / 2) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ))| ≤
          c₁_low * T₀ / P ^ j := by
        have h_each : ∀ r ∈ A.erase r₀,
            |((h r : ℝ) * (n : ℝ) / 2) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ))| ≤
            ((2 * (Real.log (n : ℝ)) ^ (R + 2) + 1) / (n : ℝ) ^ δ * Mmax) * (T₀ / P ^ j) := by
          intro r hr
          have hrA : r ∈ A := Finset.mem_of_mem_erase hr
          have hr_ne : r ≠ r₀ := Finset.ne_of_mem_erase hr
          by_cases hhr : h r = 0
          · simp only [hhr, Int.cast_zero, zero_mul, zero_div, abs_zero]
            positivity
          · have hr_gt : r₀ < r := by
              have hle : r₀ ≤ r := Finset.min'_le _ r (Finset.mem_filter.mpr ⟨hrA, hhr⟩)
              omega
            have hr_range : 1 ≤ r ∧ r ≤ R := hA_range r hrA
            rw [abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ)),
              abs_of_pos (by norm_num : (0 : ℝ) < 2),
              abs_of_pos (zpow_pos ht_pos (-((r + j : ℕ) : ℤ)))]
            have hh_le : |(h r : ℝ)| ≤ 2 * (Real.log (n : ℝ)) ^ (R + 2) + 1 := by
              have hhZ : |(h r : ℝ)| ≤ (2 * (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) + 1) := by
                exact_mod_cast hh_bound r hrA
              have hfl : (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) :=
                Nat.floor_le (by positivity)
              linarith
            have hcoeff_le : |negPowDerivCoeff r j| ≤ Mmax := by
              unfold negPowDerivCoeff Mmax
              rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
                abs_of_nonneg (Finset.prod_nonneg (fun k _ => by positivity))]
              calc ∏ k ∈ Finset.range j, ((r + k : ℕ) : ℝ)
                  ≤ ∏ k ∈ Finset.range j, ((R + k : ℕ) : ℝ) := by
                    refine Finset.prod_le_prod (fun k _ => by positivity) (fun k _ => ?_)
                    exact_mod_cast (by omega : r + k ≤ R + k)
                _ ≤ ∏ k ∈ Finset.range (5 * R + 2), ((R + k : ℕ) : ℝ) := by
                    have hN : ∏ k ∈ Finset.range j, (R + k) ≤ ∏ k ∈ Finset.range (5 * R + 2), (R + k) :=
                      Finset.prod_le_prod_of_subset_of_one_le' (Finset.range_mono hj2)
                        (fun k _ _ => by omega)
                    exact_mod_cast hN
            have ht_le : t ^ (-((r + j : ℕ) : ℤ)) ≤ (1 / P) * P ^ (-((r₀ + j : ℕ) : ℤ)) := by
              rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
              have hpow_le : P ^ (r₀ + 1 + j) ≤ t ^ (r + j) := by
                calc P ^ (r₀ + 1 + j) ≤ P ^ (r + j) := pow_le_pow_right₀ hP_ge1 (by omega)
                  _ ≤ t ^ (r + j) := pow_le_pow_left₀ hP_pos.le ht.1 _
              calc (t ^ (r + j))⁻¹ ≤ (P ^ (r₀ + 1 + j))⁻¹ :=
                    inv_anti₀ (pow_pos hP_pos _) hpow_le
                _ = (1 / P) * (P ^ (r₀ + j))⁻¹ := by
                    rw [pow_add, pow_add, pow_one, one_div, mul_inv, mul_inv]; ring
            have hh0 : (1 : ℝ) ≤ |(h r₀ : ℝ)| := by exact_mod_cast Int.one_le_abs hr₀_ne
            have hP_eq : P ^ (-((r₀ + j : ℕ) : ℤ)) = (1 / P ^ r₀) / P ^ j := by
              rw [zpow_neg, zpow_natCast, pow_add]
              field_simp [hP_pos.ne']
            calc (|(h r : ℝ)| * (n : ℝ) / 2) * |negPowDerivCoeff r j| * t ^ (-((r + j : ℕ) : ℤ))
                ≤ ((2 * (Real.log (n : ℝ)) ^ (R + 2) + 1) * (n : ℝ) / 2) * Mmax *
                    ((1 / P) * ((1 / P ^ r₀) / P ^ j)) := by
                  apply mul_le_mul
                  · apply mul_le_mul
                    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh_le (by positivity)) (by norm_num)
                    · exact hcoeff_le
                    · positivity
                    · positivity
                  · rw [← hP_eq]; exact ht_le
                  · positivity
                  · positivity
              _ = ((2 * (Real.log (n : ℝ)) ^ (R + 2) + 1) / P * Mmax) * ((n : ℝ) / (2 * P ^ r₀) / P ^ j) := by ring
              _ ≤ ((2 * (Real.log (n : ℝ)) ^ (R + 2) + 1) / (n : ℝ) ^ δ * Mmax) * (T₀ / P ^ j) := by
                  apply mul_le_mul
                  · apply mul_le_mul_of_nonneg_right _ (by unfold Mmax; positivity)
                    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hP_lo
                  · unfold T₀
                    calc (n : ℝ) / (2 * P ^ r₀) / P ^ j
                        = (1 / 2 : ℝ) * (1 * (n : ℝ) / P ^ r₀ / P ^ j) := by ring
                      _ ≤ 1 * (|(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀ / P ^ j) := by
                          apply mul_le_mul (by norm_num) _ (by positivity) (by norm_num)
                          exact div_le_div_of_nonneg_right
                            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh0 (by positivity)) (by positivity))
                            (by positivity)
                      _ = |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀ / P ^ j := one_mul _
                  · positivity
                  · positivity
        calc |∑ r ∈ A.erase r₀,
              ((h r : ℝ) * (n : ℝ) / 2) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ))|
            ≤ ∑ r ∈ A.erase r₀,
                |((h r : ℝ) * (n : ℝ) / 2) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _r ∈ A.erase r₀,
                ((2 * (Real.log (n : ℝ)) ^ (R + 2) + 1) / (n : ℝ) ^ δ * Mmax) * (T₀ / P ^ j) :=
              Finset.sum_le_sum h_each
          _ = (((A.erase r₀).card : ℝ)) *
                (((2 * (Real.log (n : ℝ)) ^ (R + 2) + 1) / (n : ℝ) ^ δ * Mmax) * (T₀ / P ^ j)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (R : ℝ) * (((2 * (Real.log (n : ℝ)) ^ (R + 2) + 1) / (n : ℝ) ^ δ * Mmax) * (T₀ / P ^ j)) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              have hcard : (A.erase r₀).card ≤ R := by
                calc (A.erase r₀).card ≤ A.card := Finset.card_erase_le
                  _ ≤ (Finset.Icc 1 R).card := Finset.card_le_card (fun r hr =>
                      Finset.mem_Icc.mpr (hA_range r hr))
                  _ = R := by simp
              exact_mod_cast hcard
          _ ≤ c₁_low * (T₀ / P ^ j) := by
              rw [← mul_assoc]
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              calc (R : ℝ) * ((2 * (Real.log (n : ℝ)) ^ (R + 2) + 1) / (n : ℝ) ^ δ * Mmax)
                  ≤ (2 * (Real.log (n : ℝ)) ^ (R + 2) + 1) / (n : ℝ) ^ δ * ((R : ℝ) * Mmax + 1) := by
                    have h1 : 0 ≤ (2 * (Real.log (n : ℝ)) ^ (R + 2) + 1) / (n : ℝ) ^ δ := by positivity
                    nlinarith
                _ ≤ c₁_low := hsmall1
          _ = c₁_low * T₀ / P ^ j := by ring
      constructor
      · have hrev := abs_sub_abs_le_abs_add
          (((h r₀ : ℝ) * (n : ℝ) / 2) * negPowDerivCoeff r₀ j * t ^ (-((r₀ + j : ℕ) : ℤ)))
          (∑ r ∈ A.erase r₀, ((h r : ℝ) * (n : ℝ) / 2) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ)))
        have h2c : 2 * c₁_low * T₀ / P ^ j = c₁_low * T₀ / P ^ j + c₁_low * T₀ / P ^ j := by ring
        linarith
      · have htri := abs_add_le
          (((h r₀ : ℝ) * (n : ℝ) / 2) * negPowDerivCoeff r₀ j * t ^ (-((r₀ + j : ℕ) : ℤ)))
          (∑ r ∈ A.erase r₀, ((h r : ℝ) * (n : ℝ) / 2) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ)))
        have hc1_le : c₁_low ≤ (1 / 2 : ℝ) * Mmax := by
          unfold c₁_low
          have hpow_le : (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ)) ≤ 1 :=
            zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
          linarith
        have hc1_T : c₁_low * T₀ / P ^ j ≤ ((1 / 2 : ℝ) * Mmax) * T₀ / P ^ j := by
          apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc1_le (by positivity)) (by positivity)
        have h32 : c₂_high * T₀ / P ^ j = Mmax * T₀ / P ^ j + ((1 / 2 : ℝ) * Mmax) * T₀ / P ^ j := by
          unfold c₂_high; ring
        linarith
  have hMain := hVaughan n P I F w W₀ T₀ hn hP_lo hP_hi hI_prime hT₀_ge hW_bound hDeriv
  constructor
  · refine ⟨hMain.1, ?_⟩
    have hlogP_le : Real.log P ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log hP_pos
      calc P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := hP_hi
        _ ≤ (n : ℝ) := div_le_self (by positivity) (one_le_pow₀ (by linarith))
    have hlogP_nonneg : 0 ≤ Real.log P := Real.log_nonneg hP_ge1
    have hT_pow : T₀ ^ (-(1 / 6 : ℝ)) * (Real.log P) ^ 3 ≤
        (2 : ℝ) ^ ((R : ℝ) / 6) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by
      have h1 : T₀ ^ (-(1 / 6 : ℝ)) ≤ ((2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R) ^ (-(1 / 6 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hT₀_ge (by norm_num)
      have h2 : ((2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R) ^ (-(1 / 6 : ℝ)) =
          (2 : ℝ) ^ ((R : ℝ) / 6) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 5)) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        · rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)]
          congr 1; push_cast; ring
        · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          congr 1; unfold A_R; push_cast; ring
      have h3 : (Real.log P) ^ 3 ≤ (Real.log (n : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hlogP_nonneg hlogP_le 3
      calc T₀ ^ (-(1 / 6 : ℝ)) * (Real.log P) ^ 3
          ≤ ((2 : ℝ) ^ ((R : ℝ) / 6) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 5))) * (Real.log (n : ℝ)) ^ 3 :=
            mul_le_mul (le_trans h1 h2.le) h3 (by positivity) (by positivity)
        _ = (2 : ℝ) ^ ((R : ℝ) / 6) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by
            rw [mul_assoc, ← Real.rpow_natCast (Real.log (n : ℝ)) 3,
              ← Real.rpow_add (by linarith)]
            congr 2; push_cast; ring
    have hP_pow : P ^ (-η') * (Real.log P) ^ 3 ≤ (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by
      have h1 : P ^ (-η') ≤ ((n : ℝ) ^ δ) ^ (-η') :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hP_lo (by linarith)
      have h2 : ((n : ℝ) ^ δ) ^ (-η') = (n : ℝ) ^ (-(δ * η')) := by
        rw [← Real.rpow_mul (by positivity)]
        congr 1; ring
      have h3 : (Real.log P) ^ 3 ≤ (Real.log (n : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hlogP_nonneg hlogP_le 3
      have h4 : (n : ℝ) ^ (-(δ * η')) * (Real.log (n : ℝ)) ^ 3 =
          ((Real.log (n : ℝ)) ^ (R + 5) / (n : ℝ) ^ (δ * η')) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by
        rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
        have hlog_eq : (Real.log (n : ℝ)) ^ (R + 5) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) =
            (Real.log (n : ℝ)) ^ 3 := by
          rw [← Real.rpow_natCast (Real.log (n : ℝ)) (R + 5),
            ← Real.rpow_add (by linarith),
            show ((R + 5 : ℕ) : ℝ) + (-((R : ℝ) + 2)) = ((3 : ℕ) : ℝ) from by push_cast; ring,
            Real.rpow_natCast]
        calc ((n : ℝ) ^ (δ * η'))⁻¹ * (Real.log (n : ℝ)) ^ 3
            = ((n : ℝ) ^ (δ * η'))⁻¹ * ((Real.log (n : ℝ)) ^ (R + 5) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
              rw [hlog_eq]
          _ = ((Real.log (n : ℝ)) ^ (R + 5) * ((n : ℝ) ^ (δ * η'))⁻¹) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by ring
      calc P ^ (-η') * (Real.log P) ^ 3
          ≤ (n : ℝ) ^ (-(δ * η')) * (Real.log (n : ℝ)) ^ 3 :=
            mul_le_mul (le_trans h1 h2.le) h3 (by positivity) (by positivity)
        _ = ((Real.log (n : ℝ)) ^ (R + 5) / (n : ℝ) ^ (δ * η')) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := h4
        _ ≤ 1 * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_right hsmall2 (by positivity)
        _ = (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := one_mul _
    calc ‖∑ p ∈ I, (w (p : ℝ) * Real.log (p : ℝ) : ℂ) * eExp (F (p : ℝ))‖
        ≤ C * W₀ * P * (T₀ ^ (-(1 / 6 : ℝ)) + P ^ (-η')) * (Real.log P) ^ 3 := hMain.1
      _ = C * W₀ * P * (T₀ ^ (-(1 / 6 : ℝ)) * (Real.log P) ^ 3 + P ^ (-η') * (Real.log P) ^ 3) := by ring
      _ ≤ C * W₀ * P * ((2 : ℝ) ^ ((R : ℝ) / 6) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) +
            (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
          apply mul_le_mul_of_nonneg_left (add_le_add hT_pow hP_pow) (by positivity)
      _ = C₂ * W₀ * P * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by unfold C₂; ring
  · exact hMain.2

end GrasGreenbergBrocard
