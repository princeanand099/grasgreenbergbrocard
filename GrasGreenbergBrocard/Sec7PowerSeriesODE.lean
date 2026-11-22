import Mathlib
import GrasGreenbergBrocard.Sec7TaylorSeries

/-!
# Concrete Section 7 Lemma 7.2 & Support-Reduced Wronskian `Delta_S` (Defect D1, Part 2)

This file eliminates `axiom canonicalSupportWronskian` completely by proving, with **zero external
axioms**:
1. Formal power-series derivative `psDeriv : PowerSeries ℚ → PowerSeries ℚ` (linearity, Leibniz
   product rule, polynomial compatibility, and `a' * b = a * b' → ∃ c : ℚ, a = C c * b`).
2. Exact first-order rational ODE for `unscaledMonomialSeries r β e`:
   `T(X) * Ω_e'(X) = TA_e(X) * Ω_e(X)` where `T(X) = r * ∏_{j=1}^{M-1} (1 - j X) ∈ ℤ[X]`.
3. **Concrete Lemma 7.2 (`monomial_series_linear_indep_poly`)**: `Polynomial ℚ`-linear independence
   of `{unscaledMonomialSeries r β e : e ∈ multiIndexFinset d E}` when `E ≤ r - 1` and `β` is
   strictly increasing with `r ≤ β i ≤ M`.
4. **Wronskian Non-Vanishing (`wronskian_ne_zero_of_linearIndependent`)**: for any `ℚ`-linearly
   independent family `g : Fin s → PowerSeries ℚ`, `det (psDeriv^[k] (g j)) ≠ 0`, and hence
   `det ((T * psDeriv)^[k] (g j)) ≠ 0`.
-/

noncomputable section

open scoped BigOperators
open Polynomial Finset

namespace GrasGreenbergBrocard

/-! ### Part 1: Formal Power-Series Derivative on `PowerSeries ℚ` -/

/-- Formal derivative on `PowerSeries ℚ`: `coeff k (psDeriv f) = (k + 1) * coeff (k + 1) f`. -/
def psDeriv (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun k => ((k + 1 : ℕ) : ℚ) * PowerSeries.coeff (k + 1) f)

@[simp] lemma coeff_psDeriv (f : PowerSeries ℚ) (k : ℕ) :
    PowerSeries.coeff k (psDeriv f) = ((k + 1 : ℕ) : ℚ) * PowerSeries.coeff (k + 1) f := by
  simp [psDeriv]

@[simp] lemma psDeriv_zero : psDeriv 0 = 0 := by
  ext k; simp

@[simp] lemma psDeriv_C (c : ℚ) : psDeriv (PowerSeries.C c) = 0 := by
  ext k; simp

@[simp] lemma psDeriv_one : psDeriv 1 = 0 := by
  simpa using psDeriv_C 1

lemma psDeriv_add (f g : PowerSeries ℚ) : psDeriv (f + g) = psDeriv f + psDeriv g := by
  ext k; simp [mul_add]

lemma psDeriv_neg (f : PowerSeries ℚ) : psDeriv (-f) = -psDeriv f := by
  ext k; simp

lemma psDeriv_sub (f g : PowerSeries ℚ) : psDeriv (f - g) = psDeriv f - psDeriv g := by
  ext k; simp [mul_sub]

lemma psDeriv_smul (c : ℚ) (f : PowerSeries ℚ) : psDeriv (c • f) = c • psDeriv f := by
  ext k; simp; ring

lemma psDeriv_C_mul (c : ℚ) (f : PowerSeries ℚ) :
    psDeriv (PowerSeries.C c * f) = PowerSeries.C c * psDeriv f := by
  ext k; simp; ring

lemma psDeriv_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) :
    psDeriv (∑ i ∈ s, f i) = ∑ i ∈ s, psDeriv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, psDeriv_add, ih]

/-- Leibniz product rule for `psDeriv`. -/
lemma psDeriv_mul (f g : PowerSeries ℚ) :
    psDeriv (f * g) = psDeriv f * g + f * psDeriv g := by
  ext k
  simp only [coeff_psDeriv, map_add, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ]
  rw [Finset.mul_sum]
  have hsplit : ∀ a ∈ Finset.range (k + 2),
      ((k + 1 : ℕ) : ℚ) * (PowerSeries.coeff a f * PowerSeries.coeff (k + 1 - a) g) =
      ((a : ℚ) * PowerSeries.coeff a f) * PowerSeries.coeff (k + 1 - a) g +
      PowerSeries.coeff a f * (((k + 1 - a : ℕ) : ℚ) * PowerSeries.coeff (k + 1 - a) g) := by
    intro a ha
    have hale : a ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hsum : ((a : ℚ) + ((k + 1 - a : ℕ) : ℚ)) = ((k + 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_sub_of_le hale
    linear_combination -hsum * PowerSeries.coeff a f * PowerSeries.coeff (k + 1 - a) g
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro a ha
    have : k + 1 - (a + 1) = k - a := by omega
    rw [this]
  · rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro a ha
    have hale : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have : k + 1 - a = (k - a) + 1 := by omega
    rw [this]

/-- Compatibility of `psDeriv` with `Polynomial.derivative` under `Polynomial ℚ → PowerSeries ℚ`. -/
lemma psDeriv_coe_poly (P : Polynomial ℚ) :
    psDeriv (P : PowerSeries ℚ) = ((Polynomial.derivative P : Polynomial ℚ) : PowerSeries ℚ) := by
  ext k
  simp [Polynomial.coeff_coe, Polynomial.coeff_derivative, mul_comm]

/-- Product-rule ODE helper: if `T * psDeriv (f i) = A i * f i` for every `i ∈ s`, then
`T * psDeriv (∏ i ∈ s, f i) = (∑ i ∈ s, A i) * (∏ i ∈ s, f i)`. -/
lemma psDeriv_finset_prod_ode {ι : Type*} (s : Finset ι) (T : PowerSeries ℚ)
    (f A : ι → PowerSeries ℚ)
    (hode : ∀ i ∈ s, T * psDeriv (f i) = A i * f i) :
    T * psDeriv (∏ i ∈ s, f i) = (∑ i ∈ s, A i) * (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, psDeriv_mul, mul_add]
    have h1 := hode a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hode i (Finset.mem_insert_of_mem hi))
    calc T * (psDeriv (f a) * ∏ i ∈ s, f i) + T * (f a * psDeriv (∏ i ∈ s, f i))
        = (T * psDeriv (f a)) * (∏ i ∈ s, f i) + f a * (T * psDeriv (∏ i ∈ s, f i)) := by ring
      _ = (A a * f a) * (∏ i ∈ s, f i) + f a * ((∑ i ∈ s, A i) * (∏ i ∈ s, f i)) := by rw [h1, h2]
      _ = (A a + ∑ i ∈ s, A i) * (f a * ∏ i ∈ s, f i) := by ring

/-- **Zero-Quotient-Derivative Lemma in `PowerSeries ℚ`**:
If `b ≠ 0` and `psDeriv a * b = a * psDeriv b`, then `∃ c : ℚ, a = C c * b`. -/
theorem psDeriv_quot_eq_zero {a b : PowerSeries ℚ} (hb : b ≠ 0)
    (h : psDeriv a * b = a * psDeriv b) :
    ∃ c : ℚ, a = PowerSeries.C c * b := by
  classical
  have hex : ∃ k : ℕ, PowerSeries.coeff k b ≠ 0 := by
    by_contra h0; push Not at h0
    apply hb; ext k; exact h0 k
  set k₀ := Nat.find hex
  have hk₀_ne : PowerSeries.coeff k₀ b ≠ 0 := Nat.find_spec hex
  have hk₀_min : ∀ j < k₀, PowerSeries.coeff j b = 0 := fun j hj => by
    by_contra hne; exact Nat.find_min hex hj hne
  have hkey : ∀ (d : PowerSeries ℚ), psDeriv d * b = d * psDeriv b →
      ∀ n : ℕ, (∀ u < n, PowerSeries.coeff u d = 0) →
        ((n : ℚ) - (k₀ : ℚ)) * PowerSeries.coeff n d * PowerSeries.coeff k₀ b = 0 := by
    intro d hd n hdn
    by_cases hnk : n + k₀ = 0
    · have hn0 : n = 0 := by omega
      have hk0 : k₀ = 0 := by omega
      simp [hn0, hk0]
    · have hcoeff := congrArg (PowerSeries.coeff (n + k₀ - 1)) hd
      simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ,
        coeff_psDeriv] at hcoeff
      have hlhs : ∑ u ∈ Finset.range (n + k₀ - 1 + 1),
          ((u + 1 : ℕ) : ℚ) * PowerSeries.coeff (u + 1) d * PowerSeries.coeff (n + k₀ - 1 - u) b =
          (n : ℚ) * PowerSeries.coeff n d * PowerSeries.coeff k₀ b := by
        by_cases hn0 : n = 0
        · subst hn0
          simp only [Nat.cast_zero, zero_mul]
          apply Finset.sum_eq_zero
          intro u hu
          have hlt : 0 + k₀ - 1 - u < k₀ := by omega
          rw [hk₀_min _ hlt, mul_zero]
        · have hmem : n - 1 ∈ Finset.range (n + k₀ - 1 + 1) := Finset.mem_range.mpr (by omega)
          rw [Finset.sum_eq_single (n - 1)]
          · have h1 : n - 1 + 1 = n := by omega
            have h2 : n + k₀ - 1 - (n - 1) = k₀ := by omega
            rw [h1, h2]
          · intro u hu hne
            have hle : u ≤ n + k₀ - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
            by_cases hlt : u + 1 < n
            · rw [hdn (u + 1) hlt, mul_zero, zero_mul]
            · have hv_lt : n + k₀ - 1 - u < k₀ := by omega
              rw [hk₀_min _ hv_lt, mul_zero]
          · intro habs; exact absurd hmem habs
      have hrhs : ∑ u ∈ Finset.range (n + k₀ - 1 + 1),
          PowerSeries.coeff u d * (((n + k₀ - 1 - u + 1 : ℕ) : ℚ) * PowerSeries.coeff (n + k₀ - 1 - u + 1) b) =
          PowerSeries.coeff n d * ((k₀ : ℚ) * PowerSeries.coeff k₀ b) := by
        by_cases hk0 : k₀ = 0
        · subst hk0
          simp only [Nat.cast_zero, zero_mul, mul_zero]
          apply Finset.sum_eq_zero
          intro u hu
          have hlt : u < n := by
            have := Finset.mem_range.mp hu; omega
          rw [hdn u hlt, zero_mul]
        · have hmem : n ∈ Finset.range (n + k₀ - 1 + 1) := Finset.mem_range.mpr (by omega)
          rw [Finset.sum_eq_single n]
          · have h1 : n + k₀ - 1 - n + 1 = k₀ := by omega
            rw [h1]
          · intro u hu hne
            have hle : u ≤ n + k₀ - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
            by_cases hlt : u < n
            · rw [hdn u hlt, zero_mul]
            · have hv_lt : n + k₀ - 1 - u + 1 < k₀ := by omega
              rw [hk₀_min _ hv_lt, mul_zero, mul_zero]
          · intro habs; exact absurd hmem habs
      rw [hlhs, hrhs] at hcoeff
      linarith
  have ha_lt : ∀ j < k₀, PowerSeries.coeff j a = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hjk
      have h0 := hkey a h j (fun u hu => ih u hu (lt_trans hu hjk))
      have hne : ((j : ℚ) - (k₀ : ℚ)) ≠ 0 := by
        have : (j : ℚ) < (k₀ : ℚ) := by exact_mod_cast hjk
        linarith
      rcases mul_eq_zero.mp h0 with h1 | h2
      · exact (mul_eq_zero.mp h1).resolve_left hne
      · exact absurd h2 hk₀_ne
  let c : ℚ := PowerSeries.coeff k₀ a / PowerSeries.coeff k₀ b
  refine ⟨c, ?_⟩
  let d : PowerSeries ℚ := a - PowerSeries.C c * b
  have hd_ode : psDeriv d * b = d * psDeriv b := by
    dsimp only [d]
    rw [psDeriv_sub, psDeriv_C_mul]
    linear_combination h
  have hd_zero : ∀ n : ℕ, PowerSeries.coeff n d = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hlt : n < k₀
      · dsimp only [d]
        simp only [map_sub, PowerSeries.coeff_C_mul, ha_lt n hlt, hk₀_min n hlt, mul_zero, sub_self]
      · by_cases heq : n = k₀
        · subst heq
          dsimp only [d, c]
          simp only [map_sub, PowerSeries.coeff_C_mul]
          field_simp [hk₀_ne]
          ring
        · have hgt : k₀ < n := by omega
          have h0 := hkey d hd_ode n ih
          have hne : ((n : ℚ) - (k₀ : ℚ)) ≠ 0 := by
            have : (k₀ : ℚ) < (n : ℚ) := by exact_mod_cast hgt
            linarith
          rcases mul_eq_zero.mp h0 with h1 | h2
          · exact (mul_eq_zero.mp h1).resolve_left hne
          · exact absurd h2 hk₀_ne
  have hd0 : d = 0 := by ext n; simp [hd_zero n]
  exact sub_eq_zero.mp hd0

/-! ### Part 2: Unscaled Monomial-Product Series & Exact Rational ODE -/

/-- Exact rational Taylor series of `(1 - j x)^{-e / r}` in `PowerSeries ℚ`. -/
def unscaledFactorSeries (e r j : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun k =>
    ((pochhammerInt e r k : ℚ) / ((r : ℚ) ^ k * (Nat.factorial k : ℚ))) * (j : ℚ) ^ k)

@[simp] lemma coeff_unscaledFactorSeries (e r j k : ℕ) :
    PowerSeries.coeff k (unscaledFactorSeries e r j) =
      ((pochhammerInt e r k : ℚ) / ((r : ℚ) ^ k * (Nat.factorial k : ℚ))) * (j : ℚ) ^ k := by
  simp [unscaledFactorSeries]

lemma unscaledFactorSeries_const (e r j : ℕ) :
    PowerSeries.constantCoeff (unscaledFactorSeries e r j) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_unscaledFactorSeries]
  simp [pochhammerInt]

lemma unscaledFactorSeries_zero_e (r j : ℕ) : unscaledFactorSeries 0 r j = 1 := by
  ext k
  cases k with
  | zero => simp [pochhammerInt]
  | succ k => simp [pochhammerInt_zero_e (Nat.succ_pos k)]

/-- Exact scaling relation between `clearedFactorSeries` (in `PowerSeries ℤ`) and
`unscaledFactorSeries` (in `PowerSeries ℚ`): `c_cleared(k) = r^(2k) * c_unscaled(k)`. -/
lemma clearedFactorCoeff_eq_scaled {e r j : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    (clearedFactorCoeff e r j k : ℚ) =
      (r : ℚ) ^ (2 * k) * PowerSeries.coeff k (unscaledFactorSeries e r j) := by
  unfold clearedFactorCoeff
  rw [coeff_unscaledFactorSeries]
  have hdvd := factorial_dvd_r_pow_mul_pochhammer e r k hr
  have hfac_ne : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hr_ne : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdiv_cast : ((r ^ k * pochhammerInt e r k / Nat.factorial k : ℕ) : ℚ) =
      ((r : ℚ) ^ k * (pochhammerInt e r k : ℚ)) / (Nat.factorial k : ℚ) := by
    rw [Nat.cast_div hdvd hfac_ne]
    push_cast; rfl
  push_cast
  rw [hdiv_cast]
  have hr2 : (r : ℚ) ^ (2 * k) = (r : ℚ) ^ k * (r : ℚ) ^ k := by
    rw [show 2 * k = k + k by omega, pow_add]
  rw [hr2]
  field_simp [hfac_ne, pow_ne_zero k hr_ne]

/-- Exact first-order ODE for `(1 - j x)^{-e / r}`:
`(1 - j X) * f'(X) = (e * j / r) * f(X)`. -/
lemma unscaledFactorSeries_ode {e r j : ℕ} (hr : 1 ≤ r) :
    (((1 - Polynomial.C (j : ℚ) * Polynomial.X : Polynomial ℚ) : PowerSeries ℚ)) *
      psDeriv (unscaledFactorSeries e r j) =
    PowerSeries.C (((e : ℚ) * (j : ℚ)) / (r : ℚ)) * unscaledFactorSeries e r j := by
  have hr_ne : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hstep : ∀ k : ℕ, ((k + 1 : ℕ) : ℚ) * PowerSeries.coeff (k + 1) (unscaledFactorSeries e r j) =
      (((e : ℚ) + (k : ℚ) * (r : ℚ)) / (r : ℚ)) * (j : ℚ) *
        PowerSeries.coeff k (unscaledFactorSeries e r j) := by
    intro k
    rw [coeff_unscaledFactorSeries, coeff_unscaledFactorSeries]
    have hpoch : pochhammerInt e r (k + 1) = pochhammerInt e r k * (e + k * r) := by
      unfold pochhammerInt; exact Finset.prod_range_succ _ k
    have hfac : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := Nat.factorial_succ k
    rw [hpoch, hfac, pow_succ, pow_succ]
    push_cast
    have hk1_ne : ((k : ℚ) + 1) ≠ 0 := by positivity
    have hfac_ne : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp [hr_ne, hk1_ne, hfac_ne, pow_ne_zero k hr_ne]
  ext k
  have hlin : (((1 - Polynomial.C (j : ℚ) * Polynomial.X : Polynomial ℚ) : PowerSeries ℚ)) =
      1 - PowerSeries.C (j : ℚ) * PowerSeries.X := by
    simp
  rw [hlin, sub_mul, one_mul, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  rw [mul_assoc, PowerSeries.coeff_C_mul]
  cases k with
  | zero =>
    simp only [PowerSeries.coeff_zero_X_mul, mul_zero, sub_zero, coeff_psDeriv, hstep 0]
    push_cast; ring
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul, coeff_psDeriv, coeff_psDeriv, hstep (k + 1)]
    have hk_eq : PowerSeries.coeff k (psDeriv (unscaledFactorSeries e r j)) =
        ((k + 1 : ℕ) : ℚ) * PowerSeries.coeff (k + 1) (unscaledFactorSeries e r j) := rfl
    rw [show PowerSeries.coeff k (psDeriv (unscaledFactorSeries e r j)) =
      ((k + 1 : ℕ) : ℚ) * PowerSeries.coeff (k + 1) (unscaledFactorSeries e r j) from rfl]
    push_cast
    field_simp [hr_ne]
    ring

/-- Unscaled rational formal power series
`Ω_e(x) = ∏_{i=0}^{d-1} ∏_{j=1}^{β_i - 1} (1 - j x)^{-e_i / r}` in `PowerSeries ℚ`. -/
def unscaledMonomialSeries {d : ℕ} (r : ℕ) (β : Fin d → ℕ) (e : Fin d → ℕ) : PowerSeries ℚ :=
  ∏ i : Fin d, ∏ j ∈ Finset.Ico 1 (β i), unscaledFactorSeries (e i) r j

lemma unscaledMonomialSeries_const {d : ℕ} (r : ℕ) (β : Fin d → ℕ) (e : Fin d → ℕ) :
    PowerSeries.constantCoeff (unscaledMonomialSeries r β e) = 1 := by
  unfold unscaledMonomialSeries
  rw [map_prod]
  apply Finset.prod_eq_one; intro i _
  rw [map_prod]
  apply Finset.prod_eq_one; intro j _
  exact unscaledFactorSeries_const _ _ _

lemma unscaledMonomialSeries_ne_zero {d : ℕ} (r : ℕ) (β : Fin d → ℕ) (e : Fin d → ℕ) :
    unscaledMonomialSeries r β e ≠ 0 := by
  intro h0
  have := congrArg PowerSeries.constantCoeff h0
  rw [unscaledMonomialSeries_const, map_zero] at this
  exact one_ne_zero this

lemma unscaledMonomialSeries_zero {d : ℕ} (r : ℕ) (β : Fin d → ℕ) :
    unscaledMonomialSeries r β (fun _ => 0) = 1 := by
  unfold unscaledMonomialSeries
  apply Finset.prod_eq_one; intro i _
  apply Finset.prod_eq_one; intro j _
  exact unscaledFactorSeries_zero_e r j

/-- Exact scaling relation between `clearedMonomialSeries` (in `PowerSeries ℤ`) and
`unscaledMonomialSeries` (in `PowerSeries ℚ`). -/
lemma clearedMonomialSeries_coeff_eq_scaled {d : ℕ} {r : ℕ} (hr : 1 ≤ r)
    (β e : Fin d → ℕ) (k : ℕ) :
    (PowerSeries.coeff k (clearedMonomialSeries r β e) : ℚ) =
      (r : ℚ) ^ (2 * k) * PowerSeries.coeff k (unscaledMonomialSeries r β e) := by
  have hprod_scale : ∀ {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℤ) (g : ι → PowerSeries ℚ),
      (∀ a ∈ s, ∀ n, (PowerSeries.coeff n (f a) : ℚ) = (r : ℚ) ^ (2 * n) * PowerSeries.coeff n (g a)) →
      ∀ n, (PowerSeries.coeff n (∏ a ∈ s, f a) : ℚ) = (r : ℚ) ^ (2 * n) * PowerSeries.coeff n (∏ a ∈ s, g a) := by
    classical
    intro ι s f g hfg
    induction s using Finset.induction_on with
    | empty =>
      intro n; cases n with
      | zero => simp
      | succ n => simp
    | @insert a s ha ih =>
      intro n
      rw [Finset.prod_insert ha, Finset.prod_insert ha, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      have hle : u ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
      rw [hfg a (Finset.mem_insert_self a s) u, ih (fun b hb => hfg b (Finset.mem_insert_of_mem hb)) (n - u)]
      have hpow : (r : ℚ) ^ (2 * u) * (r : ℚ) ^ (2 * (n - u)) = (r : ℚ) ^ (2 * n) := by
        rw [← pow_add, show 2 * u + 2 * (n - u) = 2 * n by omega]
      calc ((r : ℚ) ^ (2 * u) * PowerSeries.coeff u (g a)) *
            ((r : ℚ) ^ (2 * (n - u)) * PowerSeries.coeff (n - u) (∏ b ∈ s, g b))
          = ((r : ℚ) ^ (2 * u) * (r : ℚ) ^ (2 * (n - u))) *
            (PowerSeries.coeff u (g a) * PowerSeries.coeff (n - u) (∏ b ∈ s, g b)) := by ring
        _ = (r : ℚ) ^ (2 * n) * (PowerSeries.coeff u (g a) * PowerSeries.coeff (n - u) (∏ b ∈ s, g b)) := by rw [hpow]
  unfold clearedMonomialSeries unscaledMonomialSeries
  apply hprod_scale Finset.univ
  intro i _ n
  apply hprod_scale (Finset.Ico 1 (β i))
  intro j _ m
  simp only [clearedFactorSeries, PowerSeries.coeff_mk]
  exact_mod_cast clearedFactorCoeff_eq_scaled hr m

/-- Common integer denominator polynomial `T(X) = r * ∏_{j=1}^{M-1} (1 - j X) ∈ ℤ[X]`. -/
def T_int (r M : ℕ) : Polynomial ℤ :=
  Polynomial.C (r : ℤ) * ∏ j ∈ Finset.Ico 1 M, (1 - Polynomial.C (j : ℤ) * Polynomial.X)

/-- Integer ODE numerator polynomial `TA_e(X) ∈ ℤ[X]` for `Ω_e`. -/
def TA_int {d : ℕ} (M : ℕ) (β e : Fin d → ℕ) : Polynomial ℤ :=
  ∑ i : Fin d, Polynomial.C (e i : ℤ) *
    ∑ j ∈ Finset.Ico 1 (β i), Polynomial.C (j : ℤ) *
      ∏ ℓ ∈ (Finset.Ico 1 M).erase j, (1 - Polynomial.C (ℓ : ℤ) * Polynomial.X)

/-- Rational cast of `T_int`. -/
def T_rat (r M : ℕ) : Polynomial ℚ := (T_int r M).map (Int.castRingHom ℚ)

/-- Rational cast of `TA_int`. -/
def TA_rat {d : ℕ} (M : ℕ) (β e : Fin d → ℕ) : Polynomial ℚ := (TA_int M β e).map (Int.castRingHom ℚ)

lemma T_rat_eq (r M : ℕ) :
    T_rat r M = Polynomial.C (r : ℚ) * ∏ j ∈ Finset.Ico 1 M, (1 - Polynomial.C (j : ℚ) * Polynomial.X) := by
  unfold T_rat T_int
  simp [Polynomial.map_prod]

lemma TA_rat_eq {d : ℕ} (M : ℕ) (β e : Fin d → ℕ) :
    TA_rat M β e = ∑ i : Fin d, Polynomial.C (e i : ℚ) *
      ∑ j ∈ Finset.Ico 1 (β i), Polynomial.C (j : ℚ) *
        ∏ ℓ ∈ (Finset.Ico 1 M).erase j, (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X) := by
  unfold TA_rat TA_int
  simp [Polynomial.map_sum, Polynomial.map_prod]

lemma T_rat_ne_zero {r M : ℕ} (hr : 1 ≤ r) : T_rat r M ≠ 0 := by
  rw [T_rat_eq]
  apply mul_ne_zero
  · exact Polynomial.C_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    intro h0
    have := congrArg (fun P : Polynomial ℚ => P.eval 0) h0
    simp at this

lemma natDegree_T_int_le (r M : ℕ) : (T_int r M).natDegree ≤ M := by
  unfold T_int
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  rw [Polynomial.natDegree_C, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  calc ∑ j ∈ Finset.Ico 1 M, (1 - Polynomial.C (j : ℤ) * Polynomial.X).natDegree
      ≤ ∑ _j ∈ Finset.Ico 1 M, 1 := by
        apply Finset.sum_le_sum; intro j _
        refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (by simp) ?_)
        refine le_trans Polynomial.natDegree_mul_le ?_; simp
    _ = (Finset.Ico 1 M).card := by simp
    _ ≤ M := by simp; omega

lemma natDegree_TA_int_le {d : ℕ} (M : ℕ) (β e : Fin d → ℕ) :
    (TA_int M β e).natDegree ≤ M := by
  unfold TA_int
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le M, fun i _ => ?_⟩
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_C, zero_add]
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le M, fun j _ => ?_⟩
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_C, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  calc ∑ ℓ ∈ (Finset.Ico 1 M).erase j, (1 - Polynomial.C (ℓ : ℤ) * Polynomial.X).natDegree
      ≤ ∑ _ℓ ∈ (Finset.Ico 1 M).erase j, 1 := by
        apply Finset.sum_le_sum; intro ℓ _
        refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le (by simp) ?_)
        refine le_trans Polynomial.natDegree_mul_le ?_; simp
    _ = ((Finset.Ico 1 M).erase j).card := by simp
    _ ≤ (Finset.Ico 1 M).card := Finset.card_erase_le
    _ ≤ M := by simp; omega

/-- **Exact First-Order Rational ODE for `unscaledMonomialSeries`**:
`T_rat r M * psDeriv (Ω_e) = TA_rat M β e * Ω_e`. -/
theorem unscaledMonomialSeries_ode {d r M : ℕ} (hr : 1 ≤ r) (β e : Fin d → ℕ)
    (hβ_hi : ∀ i, β i ≤ M) :
    (T_rat r M : PowerSeries ℚ) * psDeriv (unscaledMonomialSeries r β e) =
      (TA_rat M β e : PowerSeries ℚ) * unscaledMonomialSeries r β e := by
  have hr_ne : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold unscaledMonomialSeries
  have h1 : ∀ i : Fin d,
      (T_rat r M : PowerSeries ℚ) *
        psDeriv (∏ j ∈ Finset.Ico 1 (β i), unscaledFactorSeries (e i) r j) =
      ((Polynomial.C (e i : ℚ) * ∑ j ∈ Finset.Ico 1 (β i), Polynomial.C (j : ℚ) *
          ∏ ℓ ∈ (Finset.Ico 1 M).erase j, (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X) : Polynomial ℚ) :
        PowerSeries ℚ) * (∏ j ∈ Finset.Ico 1 (β i), unscaledFactorSeries (e i) r j) := by
    intro i
    have hinner := psDeriv_finset_prod_ode (Finset.Ico 1 (β i)) (T_rat r M : PowerSeries ℚ)
      (fun j => unscaledFactorSeries (e i) r j)
      (fun j => ((Polynomial.C (e i : ℚ) * Polynomial.C (j : ℚ) *
        ∏ ℓ ∈ (Finset.Ico 1 M).erase j, (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X) : Polynomial ℚ) : PowerSeries ℚ))
      (fun j hj => by
        have hjM : j ∈ Finset.Ico 1 M := Finset.mem_Ico.mpr
          ⟨(Finset.mem_Ico.mp hj).1, lt_of_lt_of_le (Finset.mem_Ico.mp hj).2 (hβ_hi i)⟩
        have hT_split : T_rat r M =
            (Polynomial.C (r : ℚ) * ∏ ℓ ∈ (Finset.Ico 1 M).erase j, (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X)) *
              (1 - Polynomial.C (j : ℚ) * Polynomial.X) := by
          rw [T_rat_eq, ← Finset.mul_prod_erase (Finset.Ico 1 M) _ hjM]
          ring
        rw [hT_split, Polynomial.coe_mul, mul_assoc, unscaledFactorSeries_ode hr]
        have hC_eq : ((Polynomial.C (r : ℚ) * ∏ ℓ ∈ (Finset.Ico 1 M).erase j,
            (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X) : Polynomial ℚ) : PowerSeries ℚ) *
            PowerSeries.C (((e i : ℚ) * (j : ℚ)) / (r : ℚ)) =
            ((Polynomial.C (e i : ℚ) * Polynomial.C (j : ℚ) *
              ∏ ℓ ∈ (Finset.Ico 1 M).erase j, (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X) : Polynomial ℚ) :
              PowerSeries ℚ) := by
          have hC : PowerSeries.C (((e i : ℚ) * (j : ℚ)) / (r : ℚ)) =
              ((Polynomial.C (((e i : ℚ) * (j : ℚ)) / (r : ℚ)) : Polynomial ℚ) : PowerSeries ℚ) := by simp
          rw [hC, ← Polynomial.coe_mul]
          congr 1
          rw [mul_comm _ (Polynomial.C _), ← mul_assoc, ← Polynomial.C_mul]
          congr 1
          rw [show (r : ℚ) * ((e i : ℚ) * (j : ℚ) / (r : ℚ)) = (e i : ℚ) * (j : ℚ) by field_simp [hr_ne]]
          simp [Polynomial.C_mul]
        rw [← mul_assoc, hC_eq])
    rw [hinner]
    congr 1
    rw [Finset.mul_sum, Polynomial.coe_sum]
    apply Finset.sum_congr rfl; intro j _
    simp [mul_assoc]
  have houter := psDeriv_finset_prod_ode (Finset.univ : Finset (Fin d)) (T_rat r M : PowerSeries ℚ)
    (fun i => ∏ j ∈ Finset.Ico 1 (β i), unscaledFactorSeries (e i) r j)
    (fun i => ((Polynomial.C (e i : ℚ) * ∑ j ∈ Finset.Ico 1 (β i), Polynomial.C (j : ℚ) *
        ∏ ℓ ∈ (Finset.Ico 1 M).erase j, (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X) : Polynomial ℚ) :
      PowerSeries ℚ))
    (fun i _ => h1 i)
  rw [houter, TA_rat_eq, Polynomial.coe_sum]

/-! ### Part 3: Concrete Lemma 7.2 (`Polynomial ℚ`-Linear Independence of Monomial Products) -/

/-- Helper for extracting the leading `(X - C α)`-factor in the Wronskian of two polynomials. -/
private lemma poly_wronskian_root_order {α : ℚ} {P₀ P₁ : Polynomial ℚ}
    (hP₀ : P₀ ≠ 0) (hP₁ : P₁ ≠ 0) :
    let k₀ := P₀.rootMultiplicity α
    let k₁ := P₁.rootMultiplicity α
    ∃ R₀ R₁ : Polynomial ℚ,
      P₀ = (Polynomial.X - Polynomial.C α) ^ k₀ * R₀ ∧ R₀.eval α ≠ 0 ∧
      P₁ = (Polynomial.X - Polynomial.C α) ^ k₁ * R₁ ∧ R₁.eval α ≠ 0 ∧
      ∃ W : Polynomial ℚ,
        (Polynomial.X - Polynomial.C α) * (Polynomial.derivative P₁ * P₀ - P₁ * Polynomial.derivative P₀) =
          (Polynomial.X - Polynomial.C α) ^ (k₀ + k₁) *
            (Polynomial.C ((k₁ : ℚ) - (k₀ : ℚ)) * R₀ * R₁ + (Polynomial.X - Polynomial.C α) * W) := by
  intro k₀ k₁
  obtain ⟨R₀, hR₀_eq, hR₀_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P₀ hP₀ α
  obtain ⟨R₁, hR₁_eq, hR₁_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P₁ hP₁ α
  have hR₀_eval : R₀.eval α ≠ 0 := by
    intro h0; exact hR₀_ndvd (Polynomial.dvd_iff_isRoot.mpr h0)
  have hR₁_eval : R₁.eval α ≠ 0 := by
    intro h0; exact hR₁_ndvd (Polynomial.dvd_iff_isRoot.mpr h0)
  refine ⟨R₀, R₁, hR₀_eq, hR₀_eval, hR₁_eq, hR₁_eval,
    Polynomial.derivative R₁ * R₀ - R₁ * Polynomial.derivative R₀, ?_⟩
  set L : Polynomial ℚ := Polynomial.X - Polynomial.C α
  have hL_deriv : Polynomial.derivative L = 1 := by simp [L]
  have hderiv_pow : ∀ k : ℕ, L * Polynomial.derivative (L ^ k) = Polynomial.C (k : ℚ) * L ^ k := by
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [Polynomial.derivative_pow, hL_deriv, mul_one, pow_succ]
      push_cast; ring
  have hP₀_d : L * Polynomial.derivative P₀ =
      L ^ k₀ * (Polynomial.C (k₀ : ℚ) * R₀ + L * Polynomial.derivative R₀) := by
    rw [hR₀_eq, Polynomial.derivative_mul]
    calc L * (Polynomial.derivative (L ^ k₀) * R₀ + L ^ k₀ * Polynomial.derivative R₀)
        = (L * Polynomial.derivative (L ^ k₀)) * R₀ + L ^ k₀ * (L * Polynomial.derivative R₀) := by ring
      _ = Polynomial.C (k₀ : ℚ) * L ^ k₀ * R₀ + L ^ k₀ * (L * Polynomial.derivative R₀) := by rw [hderiv_pow k₀]
      _ = L ^ k₀ * (Polynomial.C (k₀ : ℚ) * R₀ + L * Polynomial.derivative R₀) := by ring
  have hP₁_d : L * Polynomial.derivative P₁ =
      L ^ k₁ * (Polynomial.C (k₁ : ℚ) * R₁ + L * Polynomial.derivative R₁) := by
    rw [hR₁_eq, Polynomial.derivative_mul]
    calc L * (Polynomial.derivative (L ^ k₁) * R₁ + L ^ k₁ * Polynomial.derivative R₁)
        = (L * Polynomial.derivative (L ^ k₁)) * R₁ + L ^ k₁ * (L * Polynomial.derivative R₁) := by ring
      _ = Polynomial.C (k₁ : ℚ) * L ^ k₁ * R₁ + L ^ k₁ * (L * Polynomial.derivative R₁) := by rw [hderiv_pow k₁]
      _ = L ^ k₁ * (Polynomial.C (k₁ : ℚ) * R₁ + L * Polynomial.derivative R₁) := by ring
  calc L * (Polynomial.derivative P₁ * P₀ - P₁ * Polynomial.derivative P₀)
      = (L * Polynomial.derivative P₁) * P₀ - P₁ * (L * Polynomial.derivative P₀) := by ring
    _ = (L ^ k₁ * (Polynomial.C (k₁ : ℚ) * R₁ + L * Polynomial.derivative R₁)) * (L ^ k₀ * R₀) -
        (L ^ k₁ * R₁) * (L ^ k₀ * (Polynomial.C (k₀ : ℚ) * R₀ + L * Polynomial.derivative R₀)) := by
        rw [hP₁_d, hP₀_d]; conv_lhs => rw [hR₀_eq, hR₁_eq]
    _ = L ^ (k₀ + k₁) * (Polynomial.C ((k₁ : ℚ) - (k₀ : ℚ)) * R₀ * R₁ +
        L * (Polynomial.derivative R₁ * R₀ - R₁ * Polynomial.derivative R₀)) := by
        rw [pow_add, Polynomial.C_sub]; ring

/-- **Concrete Lemma 7.2 (`Polynomial ℚ`-Linear Independence of Monomial Products, Zero Axioms)**:
For `1 ≤ d`, `1 ≤ E`, `2 ≤ r`, `E ≤ r - 1`, `1 ≤ M`, and strictly increasing `β : Fin d → ℕ`
with `r ≤ β i ≤ M`, the formal power series `{unscaledMonomialSeries r β e : e ∈ multiIndexFinset d E}`
are linearly independent over `Polynomial ℚ`. -/
theorem monomial_series_linear_indep_poly {d E r M : ℕ}
    (hd : 1 ≤ d) (hE : 1 ≤ E) (hr : 2 ≤ r) (hEr : E ≤ r - 1) (hM : 1 ≤ M)
    (β : Fin d → ℕ)
    (hβ_lo : ∀ i, r ≤ β i) (hβ_hi : ∀ i, β i ≤ M) (hβ_mono : StrictMono β)
    (U : Finset (Fin d → ℕ)) (hU : U ⊆ multiIndexFinset d E)
    (P : (Fin d → ℕ) → Polynomial ℚ)
    (hrel : ∑ e ∈ U, (P e : PowerSeries ℚ) * unscaledMonomialSeries r β e = 0) :
    ∀ e ∈ U, P e = 0 := by
  classical
  have hr1 : 1 ≤ r := by omega
  suffices h : ∀ n : ℕ, ∀ (U : Finset (Fin d → ℕ)), U.card = n → U ⊆ multiIndexFinset d E →
      ∀ P : (Fin d → ℕ) → Polynomial ℚ,
        (∑ e ∈ U, (P e : PowerSeries ℚ) * unscaledMonomialSeries r β e = 0) →
        ∀ e ∈ U, P e = 0 from h U.card U rfl hU P hrel
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U hcard hU P hrel
    by_cases hzero : ∃ e ∈ U, P e = 0
    · obtain ⟨e₀, he₀, hPe₀⟩ := hzero
      have hrel' : ∑ e ∈ U.erase e₀, (P e : PowerSeries ℚ) * unscaledMonomialSeries r β e = 0 := by
        have hsum := Finset.add_sum_erase U (fun e => (P e : PowerSeries ℚ) * unscaledMonomialSeries r β e) he₀
        rw [hPe₀, Polynomial.coe_zero, zero_mul, zero_add] at hsum
        exact hsum.trans hrel
      have hcard' : (U.erase e₀).card < n := by rw [← hcard]; exact Finset.card_erase_lt_of_mem he₀
      have hall' := ih (U.erase e₀).card hcard' (U.erase e₀) rfl (Finset.erase_subset e₀ U |>.trans hU) P hrel'
      intro e he
      by_cases hee : e = e₀
      · subst hee; exact hPe₀
      · exact hall' e (Finset.mem_erase.mpr ⟨hee, he⟩)
    · push Not at hzero
      by_cases hU0 : U = ∅
      · subst hU0; intro e he; exact absurd he (Finset.notMem_empty e)
      · obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hU0
        by_cases hU1 : (U.erase e₀).Nonempty
        · let Q : (Fin d → ℕ) → Polynomial ℚ := fun e =>
            (T_rat r M * Polynomial.derivative (P e) + TA_rat M β e * P e) * P e₀ -
            (T_rat r M * Polynomial.derivative (P e₀) + TA_rat M β e₀ * P e₀) * P e
          have hderiv_rel : ∑ e ∈ U,
              ((T_rat r M * Polynomial.derivative (P e) + TA_rat M β e * P e : Polynomial ℚ) : PowerSeries ℚ) *
                unscaledMonomialSeries r β e = 0 := by
            have h0 : (T_rat r M : PowerSeries ℚ) *
                psDeriv (∑ e ∈ U, (P e : PowerSeries ℚ) * unscaledMonomialSeries r β e) = 0 := by
              rw [hrel, psDeriv_zero, mul_zero]
            rw [psDeriv_sum, Finset.mul_sum] at h0
            rw [← h0]
            apply Finset.sum_congr rfl
            intro e _
            rw [psDeriv_mul, psDeriv_coe_poly, mul_add]
            have hode := unscaledMonomialSeries_ode hr1 β e hβ_hi
            calc ((T_rat r M * Polynomial.derivative (P e) + TA_rat M β e * P e : Polynomial ℚ) : PowerSeries ℚ) *
                  unscaledMonomialSeries r β e
                = (T_rat r M : PowerSeries ℚ) * ((Polynomial.derivative (P e) : Polynomial ℚ) : PowerSeries ℚ) *
                    unscaledMonomialSeries r β e +
                  (P e : PowerSeries ℚ) * ((TA_rat M β e : PowerSeries ℚ) * unscaledMonomialSeries r β e) := by
                  simp [Polynomial.coe_add, Polynomial.coe_mul]; ring
              _ = (T_rat r M : PowerSeries ℚ) * (((Polynomial.derivative (P e) : Polynomial ℚ) : PowerSeries ℚ) *
                    unscaledMonomialSeries r β e) +
                  (T_rat r M : PowerSeries ℚ) * ((P e : PowerSeries ℚ) *
                    psDeriv (unscaledMonomialSeries r β e)) := by
                  rw [← hode]; ring
          have hQ_rel : ∑ e ∈ U.erase e₀, (Q e : PowerSeries ℚ) * unscaledMonomialSeries r β e = 0 := by
            have hQ0 : Q e₀ = 0 := by dsimp only [Q]; ring
            have hfull : ∑ e ∈ U, (Q e : PowerSeries ℚ) * unscaledMonomialSeries r β e = 0 := by
              have h1 : ∑ e ∈ U, (Q e : PowerSeries ℚ) * unscaledMonomialSeries r β e =
                  (P e₀ : PowerSeries ℚ) * (∑ e ∈ U,
                    ((T_rat r M * Polynomial.derivative (P e) + TA_rat M β e * P e : Polynomial ℚ) : PowerSeries ℚ) *
                      unscaledMonomialSeries r β e) -
                  ((T_rat r M * Polynomial.derivative (P e₀) + TA_rat M β e₀ * P e₀ : Polynomial ℚ) : PowerSeries ℚ) *
                    (∑ e ∈ U, (P e : PowerSeries ℚ) * unscaledMonomialSeries r β e) := by
                rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl; intro e _
                dsimp only [Q]; simp [Polynomial.coe_sub, Polynomial.coe_mul]; ring
              rw [h1, hderiv_rel, hrel, mul_zero, mul_zero, sub_self]
            have hsum := Finset.add_sum_erase U (fun e => (Q e : PowerSeries ℚ) * unscaledMonomialSeries r β e) he₀
            rw [hQ0, Polynomial.coe_zero, zero_mul, zero_add] at hsum
            exact hsum.trans hfull
          have hcard' : (U.erase e₀).card < n := by rw [← hcard]; exact Finset.card_erase_lt_of_mem he₀
          have hQ_zero := ih (U.erase e₀).card hcard' (U.erase e₀) rfl
            (Finset.erase_subset e₀ U |>.trans hU) Q hQ_rel
          obtain ⟨e₁, he₁_er⟩ := hU1
          have he₁_ne : e₁ ≠ e₀ := (Finset.mem_erase.mp he₁_er).1
          have he₁ : e₁ ∈ U := (Finset.mem_erase.mp he₁_er).2
          have hQe₁ : Q e₁ = 0 := hQ_zero e₁ he₁_er
          have hdiff_ode : T_rat r M * (Polynomial.derivative (P e₁) * P e₀ - P e₁ * Polynomial.derivative (P e₀)) =
              (TA_rat M β e₀ - TA_rat M β e₁) * P e₀ * P e₁ := by
            dsimp only [Q] at hQe₁
            linear_combination hQe₁
          have hdiff_ne : (Finset.univ.filter (fun i : Fin d => e₀ i ≠ e₁ i)).Nonempty := by
            by_contra hempty
            rw [Finset.not_nonempty_iff_eq_empty] at hempty
            apply he₁_ne; funext i
            by_contra hne
            have : i ∈ Finset.univ.filter (fun i : Fin d => e₀ i ≠ e₁ i) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ i, Ne.symm hne⟩
            rw [hempty] at this; exact Finset.notMem_empty i this
          let iStar : Fin d := (Finset.univ.filter (fun i : Fin d => e₀ i ≠ e₁ i)).max' hdiff_ne
          have hiStar_mem : iStar ∈ Finset.univ.filter (fun i : Fin d => e₀ i ≠ e₁ i) :=
            Finset.max'_mem _ hdiff_ne
          have hiStar_ne : e₀ iStar ≠ e₁ iStar := (Finset.mem_filter.mp hiStar_mem).2
          have hiStar_max : ∀ i : Fin d, iStar < i → e₀ i = e₁ i := by
            intro i hi
            by_contra hne
            have hle := Finset.le_max' (Finset.univ.filter (fun j : Fin d => e₀ j ≠ e₁ j)) i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
            exact not_lt_of_ge hle hi
          let jStar : ℕ := β iStar - 1
          have hjStar_pos : 1 ≤ jStar := by have := hβ_lo iStar; omega
          have hjStar_lt_M : jStar < M := by have := hβ_lo iStar; have := hβ_hi iStar; omega
          have hjStar_mem : jStar ∈ Finset.Ico 1 M := Finset.mem_Ico.mpr ⟨hjStar_pos, hjStar_lt_M⟩
          let α : ℚ := ((jStar : ℚ))⁻¹
          have hjStar_q_ne : (jStar : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          let P_rest : Polynomial ℚ := ∏ ℓ ∈ (Finset.Ico 1 M).erase jStar, (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X)
          have hT_fac : T_rat r M = Polynomial.C (-(r : ℚ) * (jStar : ℚ)) * (Polynomial.X - Polynomial.C α) * P_rest := by
            rw [T_rat_eq, ← Finset.mul_prod_erase (Finset.Ico 1 M) _ hjStar_mem]
            have hlin : (1 - Polynomial.C (jStar : ℚ) * Polynomial.X : Polynomial ℚ) =
                Polynomial.C (-(jStar : ℚ)) * (Polynomial.X - Polynomial.C α) := by
              rw [mul_sub, ← Polynomial.C_mul]
              have : -(jStar : ℚ) * α = -1 := by dsimp only [α]; field_simp [hjStar_q_ne]
              rw [this]; simp only [Polynomial.C_neg, Polynomial.C_1]; ring
            dsimp only [P_rest]
            rw [hlin]; simp only [Polynomial.C_mul, Polynomial.C_neg]; ring
          have hP_eval_ne : P_rest.eval α ≠ 0 := by
            dsimp only [P_rest]
            rw [Polynomial.eval_prod]
            apply Finset.prod_ne_zero_iff.mpr
            intro ℓ hℓ
            have hℓ_ne : ℓ ≠ jStar := (Finset.mem_erase.mp hℓ).1
            simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
              Polynomial.eval_C, Polynomial.eval_X, α]
            intro h0
            have h1 : (ℓ : ℚ) = (jStar : ℚ) := by
              have : (ℓ : ℚ) * (jStar : ℚ)⁻¹ = 1 := by linarith
              field_simp [hjStar_q_ne] at this; linarith
            exact hℓ_ne (Nat.cast_injective h1)
          have hTA_eval : (TA_rat M β e₀ - TA_rat M β e₁).eval α =
              ((e₀ iStar : ℚ) - (e₁ iStar : ℚ)) * (jStar : ℚ) * P_rest.eval α := by
            rw [Polynomial.eval_sub, TA_rat_eq, TA_rat_eq, Polynomial.eval_finset_sum,
              Polynomial.eval_finset_sum, ← Finset.sum_sub_distrib]
            have hterm : ∀ i : Fin d,
                (Polynomial.C (e₀ i : ℚ) * ∑ j ∈ Finset.Ico 1 (β i), Polynomial.C (j : ℚ) *
                  ∏ ℓ ∈ (Finset.Ico 1 M).erase j, (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X)).eval α -
                (Polynomial.C (e₁ i : ℚ) * ∑ j ∈ Finset.Ico 1 (β i), Polynomial.C (j : ℚ) *
                  ∏ ℓ ∈ (Finset.Ico 1 M).erase j, (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X)).eval α =
                if i = iStar then ((e₀ iStar : ℚ) - (e₁ iStar : ℚ)) * (jStar : ℚ) * P_rest.eval α else 0 := by
              intro i
              simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finset_sum]
              split_ifs with hi
              · subst hi
                rw [← sub_mul]
                have hinner : ∑ j ∈ Finset.Ico 1 (β iStar),
                    (Polynomial.C (j : ℚ) * ∏ ℓ ∈ (Finset.Ico 1 M).erase j,
                      (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X)).eval α =
                    (jStar : ℚ) * P_rest.eval α := by
                  have hj_in : jStar ∈ Finset.Ico 1 (β iStar) :=
                    Finset.mem_Ico.mpr ⟨hjStar_pos, by have := hβ_lo iStar; omega⟩
                  rw [Finset.sum_eq_single jStar]
                  · simp [P_rest]
                  · intro j hj hne
                    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
                    have hzero_prod : ∏ ℓ ∈ (Finset.Ico 1 M).erase j,
                        (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X).eval α = 0 := by
                      apply Finset.prod_eq_zero (i := jStar) (Finset.mem_erase.mpr ⟨hne.symm, hjStar_mem⟩)
                      simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
                        Polynomial.eval_C, Polynomial.eval_X, α]
                      field_simp [hjStar_q_ne]; ring
                    rw [hzero_prod, mul_zero]
                  · intro habs; exact absurd hj_in habs
                rw [hinner]; ring
              · rcases lt_or_gt_of_ne hi with hlt | hgt
                · have hβ_lt : β i ≤ jStar := by
                    have := hβ_mono hlt; omega
                  have hsum0 : ∑ j ∈ Finset.Ico 1 (β i),
                      (Polynomial.C (j : ℚ) * ∏ ℓ ∈ (Finset.Ico 1 M).erase j,
                        (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X)).eval α = 0 := by
                    apply Finset.sum_eq_zero; intro j hj
                    have hj_ne : jStar ≠ j := by
                      have := (Finset.mem_Ico.mp hj).2; omega
                    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
                    have hzero_prod : ∏ ℓ ∈ (Finset.Ico 1 M).erase j,
                        (1 - Polynomial.C (ℓ : ℚ) * Polynomial.X).eval α = 0 := by
                      apply Finset.prod_eq_zero (i := jStar) (Finset.mem_erase.mpr ⟨hj_ne, hjStar_mem⟩)
                      simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
                        Polynomial.eval_C, Polynomial.eval_X, α]
                      field_simp [hjStar_q_ne]; ring
                    rw [hzero_prod, mul_zero]
                  rw [hsum0, mul_zero, mul_zero, sub_self]
                · rw [hiStar_max i hgt, sub_self]
            rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq' Finset.univ iStar]
            simp
          obtain ⟨R₀, R₁, hR₀_eq, hR₀_ev, hR₁_eq, hR₁_ev, W, hW⟩ :=
            poly_wronskian_root_order (α := α) (hzero e₀ he₀) (hzero e₁ he₁)
          set k₀ := (P e₀).rootMultiplicity α
          set k₁ := (P e₁).rootMultiplicity α
          set L : Polynomial ℚ := Polynomial.X - Polynomial.C α
          have hL_pow_ne : L ^ (k₀ + k₁) ≠ 0 := pow_ne_zero _ (Polynomial.X_sub_C_ne_zero α)
          have hcancel : L ^ (k₀ + k₁) *
              (Polynomial.C (-(r : ℚ) * (jStar : ℚ)) * P_rest *
                (Polynomial.C ((k₁ : ℚ) - (k₀ : ℚ)) * R₀ * R₁ + L * W)) =
              L ^ (k₀ + k₁) * ((TA_rat M β e₀ - TA_rat M β e₁) * R₀ * R₁) := by
            calc L ^ (k₀ + k₁) * (Polynomial.C (-(r : ℚ) * (jStar : ℚ)) * P_rest *
                  (Polynomial.C ((k₁ : ℚ) - (k₀ : ℚ)) * R₀ * R₁ + L * W))
                = Polynomial.C (-(r : ℚ) * (jStar : ℚ)) * P_rest *
                    (L ^ (k₀ + k₁) * (Polynomial.C ((k₁ : ℚ) - (k₀ : ℚ)) * R₀ * R₁ + L * W)) := by ring
              _ = Polynomial.C (-(r : ℚ) * (jStar : ℚ)) * P_rest *
                    (L * (Polynomial.derivative (P e₁) * P e₀ - P e₁ * Polynomial.derivative (P e₀))) := by
                  rw [← hW]
              _ = T_rat r M * (Polynomial.derivative (P e₁) * P e₀ - P e₁ * Polynomial.derivative (P e₀)) := by
                  rw [hT_fac]; ring
              _ = (TA_rat M β e₀ - TA_rat M β e₁) * P e₀ * P e₁ := hdiff_ode
              _ = L ^ (k₀ + k₁) * ((TA_rat M β e₀ - TA_rat M β e₁) * R₀ * R₁) := by
                  rw [hR₀_eq, hR₁_eq, pow_add]; ring
          have heq_poly := mul_left_cancel₀ hL_pow_ne hcancel
          have hev := congrArg (Polynomial.eval α) heq_poly
          simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, L,
            Polynomial.eval_sub, Polynomial.eval_X, sub_self, zero_mul, add_zero, hTA_eval] at hev
          have hprod_ne : (jStar : ℚ) * P_rest.eval α * R₀.eval α * R₁.eval α ≠ 0 :=
            mul_ne_zero (mul_ne_zero (mul_ne_zero hjStar_q_ne hP_eval_ne) hR₀_ev) hR₁_ev
          have hrat_eq : (r : ℚ) * ((k₀ : ℚ) - (k₁ : ℚ)) = (e₀ iStar : ℚ) - (e₁ iStar : ℚ) := by
            apply mul_right_cancel₀ hprod_ne
            linear_combination -hev
          have hint_eq : (r : ℤ) * ((k₀ : ℤ) - (k₁ : ℤ)) = (e₀ iStar : ℤ) - (e₁ iStar : ℤ) := by
            exact_mod_cast hrat_eq
          have he₀_le : e₀ iStar ≤ E := by
            have hm := (Finset.mem_filter.mp (hU he₀)).1
            have := Finset.mem_range.mp (Fintype.mem_piFinset.mp hm iStar); omega
          have he₁_le : e₁ iStar ≤ E := by
            have hm := (Finset.mem_filter.mp (hU he₁)).1
            have := Finset.mem_range.mp (Fintype.mem_piFinset.mp hm iStar); omega
          have hk_eq : (k₀ : ℤ) = (k₁ : ℤ) := by
            by_contra hkne
            rcases lt_or_gt_of_ne hkne with hlt | hgt
            · have : (r : ℤ) * ((k₀ : ℤ) - (k₁ : ℤ)) ≤ -(r : ℤ) := by nlinarith
              omega
            · have : (r : ℤ) ≤ (r : ℤ) * ((k₀ : ℤ) - (k₁ : ℤ)) := by nlinarith
              omega
          rw [hk_eq, sub_self, mul_zero] at hint_eq
          exact hiStar_ne (by omega)
        · have hU_eq : U = {e₀} := by
            ext e
            simp only [Finset.mem_singleton]
            constructor
            · intro he
              by_contra hne
              exact hU1 ⟨e, Finset.mem_erase.mpr ⟨hne, he⟩⟩
            · rintro rfl; exact he₀
          rw [hU_eq, Finset.sum_singleton] at hrel
          have hP0 : (P e₀ : PowerSeries ℚ) = 0 :=
            (mul_eq_zero.mp hrel).resolve_right (unscaledMonomialSeries_ne_zero r β e₀)
          have hPe₀ : P e₀ = 0 := by
            ext k
            have := congrArg (PowerSeries.coeff k) hP0
            simpa [Polynomial.coeff_coe] using this
          exact absurd hPe₀ (hzero e₀ he₀)

/-! ### Part 4: Wronskian Non-Vanishing in `PowerSeries ℚ` -/

/-- Quotient-field formal derivative on `FractionRing (PowerSeries ℚ)` extending `psDeriv`. -/
private def fracDeriv (x : FractionRing (PowerSeries ℚ)) : FractionRing (PowerSeries ℚ) :=
  Localization.liftOn x
    (fun a b => Localization.mk (psDeriv a * (b : PowerSeries ℚ) - a * psDeriv (b : PowerSeries ℚ)) (b * b))
    (by
      intro a₁ a₂ b₁ b₂ h
      rcases Localization.r_iff_exists.mp h with ⟨c, hc⟩
      have hc' : (c : PowerSeries ℚ) * ((b₂ : PowerSeries ℚ) * a₁ - (b₁ : PowerSeries ℚ) * a₂) = 0 := by
        linear_combination hc
      have hcnz : (c : PowerSeries ℚ) ≠ 0 := nonZeroDivisors.ne_zero c.2
      have hba : (b₂ : PowerSeries ℚ) * a₁ = (b₁ : PowerSeries ℚ) * a₂ :=
        sub_eq_zero.mp ((mul_eq_zero.mp hc').resolve_left hcnz)
      have hba_d : psDeriv (b₂ : PowerSeries ℚ) * a₁ + (b₂ : PowerSeries ℚ) * psDeriv a₁ =
          psDeriv (b₁ : PowerSeries ℚ) * a₂ + (b₁ : PowerSeries ℚ) * psDeriv a₂ := by
        have := congrArg psDeriv hba
        simpa only [psDeriv_mul] using this
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [Submonoid.coe_one, one_mul, Submonoid.coe_mul]
      linear_combination (b₁ : PowerSeries ℚ) * (b₂ : PowerSeries ℚ) * hba_d -
        ((b₁ : PowerSeries ℚ) * psDeriv (b₂ : PowerSeries ℚ) +
         (b₂ : PowerSeries ℚ) * psDeriv (b₁ : PowerSeries ℚ)) * hba)

private lemma fracDeriv_mk (a : PowerSeries ℚ) (b : nonZeroDivisors (PowerSeries ℚ)) :
    fracDeriv (Localization.mk a b) =
      Localization.mk (psDeriv a * (b : PowerSeries ℚ) - a * psDeriv (b : PowerSeries ℚ)) (b * b) :=
  Localization.liftOn_mk _ _ _ _

private lemma fracDeriv_algebraMap (a : PowerSeries ℚ) :
    fracDeriv (algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) a) =
      algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (psDeriv a) := by
  have h1 : algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) a = Localization.mk a 1 := by
    simp [Localization.mk_one_eq_algebraMap]
  rw [h1, fracDeriv_mk]
  simp [Localization.mk_one_eq_algebraMap]

private lemma fracDeriv_zero : fracDeriv 0 = 0 := by
  have h0 : (0 : FractionRing (PowerSeries ℚ)) = algebraMap (PowerSeries ℚ) _ 0 := (map_zero _).symm
  rw [h0, fracDeriv_algebraMap, psDeriv_zero, map_zero]

private lemma fracDeriv_one : fracDeriv 1 = 0 := by
  have h1 : (1 : FractionRing (PowerSeries ℚ)) = algebraMap (PowerSeries ℚ) _ 1 := (map_one _).symm
  rw [h1, fracDeriv_algebraMap, psDeriv_one, map_zero]

private lemma fracDeriv_add (x y : FractionRing (PowerSeries ℚ)) :
    fracDeriv (x + y) = fracDeriv x + fracDeriv y := by
  induction x using Localization.induction_on with
  | H p =>
    induction y using Localization.induction_on with
    | H q =>
      rcases p with ⟨a₁, b₁⟩; rcases q with ⟨a₂, b₂⟩
      rw [Localization.add_mk, fracDeriv_mk, fracDeriv_mk, fracDeriv_mk, Localization.add_mk]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [Submonoid.coe_one, one_mul, Submonoid.coe_mul, psDeriv_add, psDeriv_mul]
      ring

private lemma fracDeriv_mul (x y : FractionRing (PowerSeries ℚ)) :
    fracDeriv (x * y) = fracDeriv x * y + x * fracDeriv y := by
  induction x using Localization.induction_on with
  | H p =>
    induction y using Localization.induction_on with
    | H q =>
      rcases p with ⟨a₁, b₁⟩; rcases q with ⟨a₂, b₂⟩
      rw [Localization.mk_mul, fracDeriv_mk, fracDeriv_mk, fracDeriv_mk,
        Localization.mk_mul, Localization.mk_mul, Localization.add_mk]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [Submonoid.coe_one, one_mul, Submonoid.coe_mul, psDeriv_mul]
      ring

private lemma fracDeriv_rat_smul (c : ℚ) (x : FractionRing (PowerSeries ℚ)) :
    fracDeriv (algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (PowerSeries.C c) * x) =
      algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (PowerSeries.C c) * fracDeriv x := by
  rw [fracDeriv_mul, fracDeriv_algebraMap, psDeriv_C, map_zero, zero_mul, zero_add]

private lemma fracDeriv_sum {ι : Type*} (s : Finset ι) (f : ι → FractionRing (PowerSeries ℚ)) :
    fracDeriv (∑ i ∈ s, f i) = ∑ i ∈ s, fracDeriv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fracDeriv_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fracDeriv_add, ih]

private lemma fracDeriv_eq_zero_iff (x : FractionRing (PowerSeries ℚ)) :
    fracDeriv x = 0 ↔ ∃ c : ℚ, x = algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) (PowerSeries.C c) := by
  constructor
  · intro hx
    induction x using Localization.induction_on with
    | H p =>
      rcases p with ⟨a, b⟩
      rw [fracDeriv_mk] at hx
      have h0 : Localization.mk (psDeriv a * (b : PowerSeries ℚ) - a * psDeriv (b : PowerSeries ℚ)) (b * b) =
          Localization.mk 0 1 := by
        simpa [Localization.mk_zero] using hx
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h0
      rcases h0 with ⟨c, hc⟩
      simp only [Submonoid.coe_one, one_mul, mul_zero, zero_mul, sub_zero] at hc
      have hcnz : (c : PowerSeries ℚ) ≠ 0 := nonZeroDivisors.ne_zero c.2
      have hbnz : (b : PowerSeries ℚ) ≠ 0 := nonZeroDivisors.ne_zero b.2
      have hsub : psDeriv a * (b : PowerSeries ℚ) - a * psDeriv (b : PowerSeries ℚ) = 0 :=
        (mul_eq_zero.mp hc).resolve_left hcnz
      obtain ⟨q, hq⟩ := psDeriv_quot_eq_zero hbnz (sub_eq_zero.mp hsub)
      refine ⟨q, ?_⟩
      rw [← Localization.mk_one_eq_algebraMap, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp [hq, mul_comm]
  · rintro ⟨c, rfl⟩
    rw [fracDeriv_algebraMap, psDeriv_C, map_zero]

/-- Iterated Leibniz rule for `fracDeriv`. -/
private lemma fracDeriv_iter_mul (g h : FractionRing (PowerSeries ℚ)) :
    ∀ k : ℕ, fracDeriv^[k] (g * h) =
      ∑ r ∈ Finset.range (k + 1),
        ((Nat.choose k r : ℕ) : FractionRing (PowerSeries ℚ)) *
          fracDeriv^[k - r] g * fracDeriv^[r] h := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, fracDeriv_sum]
    have hstep : ∀ r ∈ Finset.range (k + 1),
        fracDeriv (((Nat.choose k r : ℕ) : FractionRing (PowerSeries ℚ)) *
          fracDeriv^[k - r] g * fracDeriv^[r] h) =
        ((Nat.choose k r : ℕ) : FractionRing (PowerSeries ℚ)) *
          fracDeriv^[k + 1 - r] g * fracDeriv^[r] h +
        ((Nat.choose k r : ℕ) : FractionRing (PowerSeries ℚ)) *
          fracDeriv^[k - r] g * fracDeriv^[r + 1] h := by
      intro r hr
      have hrle : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hnat : ((Nat.choose k r : ℕ) : FractionRing (PowerSeries ℚ)) =
          algebraMap (PowerSeries ℚ) _ (PowerSeries.C (Nat.choose k r : ℚ)) := by simp
      rw [mul_assoc, hnat, fracDeriv_rat_smul, fracDeriv_mul, mul_add, ← hnat]
      have h1 : k + 1 - r = (k - r) + 1 := by omega
      rw [h1, Function.iterate_succ_apply', Function.iterate_succ_apply']
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun r => ((Nat.choose (k + 1) r : ℕ) : FractionRing (PowerSeries ℚ)) *
        fracDeriv^[k + 1 - r] g * fracDeriv^[r] h)]
    rw [Finset.sum_range_succ (fun r => ((Nat.choose (k + 1) (r + 1) : ℕ) : FractionRing (PowerSeries ℚ)) *
        fracDeriv^[k + 1 - (r + 1)] g * fracDeriv^[r + 1] h)]
    rw [Finset.sum_range_succ' (fun r => ((Nat.choose k r : ℕ) : FractionRing (PowerSeries ℚ)) *
        fracDeriv^[k + 1 - r] g * fracDeriv^[r] h)]
    rw [Finset.sum_range_succ (fun r => ((Nat.choose k r : ℕ) : FractionRing (PowerSeries ℚ)) *
        fracDeriv^[k - r] g * fracDeriv^[r + 1] h)]
    have hmid : ∑ r ∈ Finset.range k,
        ((Nat.choose (k + 1) (r + 1) : ℕ) : FractionRing (PowerSeries ℚ)) *
          fracDeriv^[k + 1 - (r + 1)] g * fracDeriv^[r + 1] h =
        (∑ r ∈ Finset.range k,
          ((Nat.choose k (r + 1) : ℕ) : FractionRing (PowerSeries ℚ)) *
            fracDeriv^[k + 1 - (r + 1)] g * fracDeriv^[r + 1] h) +
        (∑ r ∈ Finset.range k,
          ((Nat.choose k r : ℕ) : FractionRing (PowerSeries ℚ)) *
            fracDeriv^[k - r] g * fracDeriv^[r + 1] h) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro r _
      have h1 : k + 1 - (r + 1) = k - r := by omega
      rw [h1, Nat.choose_succ_succ, Nat.cast_add]; ring
    rw [hmid]
    simp only [Nat.choose_zero_right, Nat.choose_self, Nat.sub_self, Nat.cast_one, one_mul,
      Nat.sub_zero, Function.iterate_zero_apply]
    ring

/-- **Wronskian Non-Vanishing over `FractionRing (PowerSeries ℚ)`**:
If `g : Fin s → FractionRing (PowerSeries ℚ)` is `ℚ`-linearly independent, then
`det (fun k j => fracDeriv^[k] (g j)) ≠ 0`. -/
private theorem fracWronskian_ne_zero : ∀ (s : ℕ) (g : Fin s → FractionRing (PowerSeries ℚ)),
    (∀ c : Fin s → ℚ, (∑ j : Fin s, algebraMap (PowerSeries ℚ) _ (PowerSeries.C (c j)) * g j = 0) →
      ∀ j, c j = 0) →
    Matrix.det (Matrix.of (fun k j : Fin s => fracDeriv^[k.val] (g j))) ≠ 0 := by
  intro s
  induction s with
  | zero => intro g _; simp
  | succ s ih =>
    intro g hli
    have hg0_ne : g 0 ≠ 0 := by
      intro h0
      have hc := hli (fun j => if j = 0 then 1 else 0) (by
        rw [Finset.sum_eq_single 0]
        · simp [h0]
        · intro j _ hj; simp [hj]
        · intro habs; exact absurd (Finset.mem_univ 0) habs) 0
      simp at hc
    let h : Fin (s + 1) → FractionRing (PowerSeries ℚ) := fun j => g j * (g 0)⁻¹
    have hmul : ∀ j : Fin (s + 1), g j = g 0 * h j := fun j => by
      dsimp only [h]; rw [mul_comm (g j), ← mul_assoc, mul_inv_cancel₀ hg0_ne, one_mul]
    have hh0 : h 0 = 1 := mul_inv_cancel₀ hg0_ne
    let L : Matrix (Fin (s + 1)) (Fin (s + 1)) (FractionRing (PowerSeries ℚ)) :=
      Matrix.of fun k r =>
        if r.val ≤ k.val then
          ((Nat.choose k.val r.val : ℕ) : FractionRing (PowerSeries ℚ)) * fracDeriv^[k.val - r.val] (g 0)
        else 0
    let Wh : Matrix (Fin (s + 1)) (Fin (s + 1)) (FractionRing (PowerSeries ℚ)) :=
      Matrix.of fun k j => fracDeriv^[k.val] (h j)
    have hW_eq : Matrix.of (fun k j : Fin (s + 1) => fracDeriv^[k.val] (g j)) = L * Wh := by
      ext k j
      simp only [Matrix.of_apply, Matrix.mul_apply, L, Wh]
      rw [hmul j, fracDeriv_iter_mul]
      have hfilt : ∑ r : Fin (s + 1),
          (if r.val ≤ k.val then
            ((Nat.choose k.val r.val : ℕ) : FractionRing (PowerSeries ℚ)) * fracDeriv^[k.val - r.val] (g 0)
           else 0) * fracDeriv^[r.val] (h j) =
          ∑ r ∈ Finset.univ.filter (fun r : Fin (s + 1) => r.val ≤ k.val),
            ((Nat.choose k.val r.val : ℕ) : FractionRing (PowerSeries ℚ)) *
              fracDeriv^[k.val - r.val] (g 0) * fracDeriv^[r.val] (h j) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro r _
        split_ifs <;> simp
      rw [hfilt]
      symm
      refine Finset.sum_nbij (fun r : Fin (s + 1) => r.val) ?_ ?_ ?_ ?_
      · intro r hr
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hr).2)
      · intro r₁ _ r₂ _ heq; exact Fin.ext heq
      · intro r hr
        have hr_le : r ≤ k.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        exact ⟨⟨r, lt_of_le_of_lt hr_le k.isLt⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr_le⟩, rfl⟩
      · intro r _; rfl
    have hL_tri : L.BlockTriangular OrderDual.toDual := by
      intro i j hij
      have hlt : i.val < j.val := hij
      dsimp only [L, Matrix.of_apply]
      rw [if_neg (not_le.mpr hlt)]
    have hL_det : L.det = (g 0) ^ (s + 1) := by
      rw [Matrix.det_of_lowerTriangular L hL_tri]
      have hdiag : ∀ i : Fin (s + 1), L i i = g 0 := fun i => by
        simp [L]
      simp [hdiag]
    have hWh_col0 : ∀ k : Fin (s + 1), Wh k 0 = if k = 0 then 1 else 0 := by
      intro k
      dsimp only [Wh, Matrix.of_apply]
      rw [hh0]
      cases hkv : k.val with
      | zero =>
        have hk0 : k = 0 := Fin.ext hkv
        simp [hk0]
      | succ m =>
        have hk_ne : k ≠ 0 := fun h0 => by rw [h0] at hkv; simp at hkv
        rw [if_neg hk_ne, Function.iterate_succ_apply, fracDeriv_one]
        clear hkv hk_ne
        induction m with
        | zero => rfl
        | succ m ihm => rw [Function.iterate_succ_apply', ihm, fracDeriv_zero]
    have hWh_det : Wh.det =
        Matrix.det (Matrix.of (fun k j : Fin s => fracDeriv^[k.val] (fracDeriv (h j.succ)))) := by
      rw [Matrix.det_succ_column_zero Wh]
      rw [Finset.sum_eq_single (0 : Fin (s + 1))]
      · simp only [Fin.val_zero, pow_zero, one_mul, hWh_col0 0, ↓reduceIte]
        apply congrArg Matrix.det
        ext k j
        simp only [Matrix.submatrix_apply, Matrix.of_apply, Wh, Fin.succAbove_zero, Fin.val_succ,
          Function.iterate_succ_apply]
      · intro k _ hk0
        rw [hWh_col0 k, if_neg hk0, mul_zero, zero_mul]
      · intro habs; exact absurd (Finset.mem_univ 0) habs
    rw [hW_eq, Matrix.det_mul, hL_det, hWh_det]
    apply mul_ne_zero (pow_ne_zero (s + 1) hg0_ne)
    apply ih (fun j : Fin s => fracDeriv (h j.succ))
    intro c hc
    have hsum_d : fracDeriv (∑ j : Fin s, algebraMap (PowerSeries ℚ) _ (PowerSeries.C (c j)) * h j.succ) = 0 := by
      rw [fracDeriv_sum]
      rw [← hc]
      apply Finset.sum_congr rfl; intro j _
      exact fracDeriv_rat_smul (c j) (h j.succ)
    obtain ⟨c₀, hc₀⟩ := (fracDeriv_eq_zero_iff _).mp hsum_d
    let cfull : Fin (s + 1) → ℚ := Fin.cons (-c₀) c
    have hfull_zero : ∑ j : Fin (s + 1), algebraMap (PowerSeries ℚ) _ (PowerSeries.C (cfull j)) * g j = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [cfull, Fin.cons_zero, Fin.cons_succ]
      have hmul_c0 : (∑ j : Fin s, algebraMap (PowerSeries ℚ) _ (PowerSeries.C (c j)) * g j.succ) =
          g 0 * (∑ j : Fin s, algebraMap (PowerSeries ℚ) _ (PowerSeries.C (c j)) * h j.succ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [hmul j.succ]; ring
      rw [hmul_c0, hc₀, map_neg, map_neg]
      ring
    intro j
    have := hli cfull hfull_zero j.succ
    simpa [cfull] using this

/-- **Wronskian Non-Vanishing in `PowerSeries ℚ`**:
If `g : Fin s → PowerSeries ℚ` is `ℚ`-linearly independent, then
`det (fun k j => psDeriv^[k] (g j)) ≠ 0`. -/
theorem wronskian_ne_zero_of_linearIndependent {s : ℕ} (g : Fin s → PowerSeries ℚ)
    (hli : ∀ c : Fin s → ℚ, (∑ j : Fin s, PowerSeries.C (c j) * g j = 0) → ∀ j, c j = 0) :
    Matrix.det (Matrix.of (fun k j : Fin s => psDeriv^[k.val] (g j))) ≠ 0 := by
  let ι := algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))
  have hinj : Function.Injective ι := IsFractionRing.injective (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))
  have hiter : ∀ (k : ℕ) (f : PowerSeries ℚ), fracDeriv^[k] (ι f) = ι (psDeriv^[k] f) := by
    intro k
    induction k with
    | zero => intro f; rfl
    | succ k ih =>
      intro f
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, fracDeriv_algebraMap]
  intro hdet0
  have hmap0 : Matrix.det (Matrix.of (fun k j : Fin s => fracDeriv^[k.val] (ι (g j)))) = 0 := by
    have hmat : Matrix.of (fun k j : Fin s => fracDeriv^[k.val] (ι (g j))) =
        ι.mapMatrix (Matrix.of (fun k j : Fin s => psDeriv^[k.val] (g j))) := by
      ext k j; simp [hiter]
    rw [hmat, ← RingHom.map_det, hdet0, map_zero]
  apply fracWronskian_ne_zero s (fun j => ι (g j)) ?_ hmap0
  intro c hc
  apply hli c
  apply hinj
  rw [map_zero, map_sum]
  simpa [map_mul] using hc

/-- Lower-triangular expansion of `(fun f => T * psDeriv f)^[k] g` in terms of `psDeriv^[r] g`. -/
private lemma iter_T_psDeriv_expand (T : PowerSeries ℚ) :
    ∀ k : ℕ, ∃ c : ℕ → PowerSeries ℚ, ∀ g : PowerSeries ℚ,
      (fun f => T * psDeriv f)^[k] g = T ^ k * psDeriv^[k] g + ∑ r ∈ Finset.range k, c r * psDeriv^[r] g := by
  intro k
  induction k with
  | zero => exact ⟨fun _ => 0, fun g => by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    let c' : ℕ → PowerSeries ℚ := fun r =>
      (if r = k then T * psDeriv (T ^ k) else 0) +
      (if r < k then T * psDeriv (c r) else 0) +
      (if 1 ≤ r ∧ r ≤ k then T * c (r - 1) else 0)
    refine ⟨c', fun g => ?_⟩
    rw [Function.iterate_succ_apply', hc g, psDeriv_add, psDeriv_mul, psDeriv_sum,
      mul_add, mul_add, Finset.mul_sum]
    have h1 : T * (T ^ k * psDeriv (psDeriv^[k] g)) = T ^ (k + 1) * psDeriv^[k + 1] g := by
      rw [Function.iterate_succ_apply', pow_succ]; ring
    have h2 : ∑ x ∈ Finset.range k, T * psDeriv (c x * psDeriv^[x] g) =
        (∑ x ∈ Finset.range k, (T * psDeriv (c x)) * psDeriv^[x] g) +
        (∑ x ∈ Finset.range k, (T * c x) * psDeriv^[x + 1] g) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [psDeriv_mul, mul_add, Function.iterate_succ_apply']; ring
    rw [h1, h2]
    have hsplit : ∑ r ∈ Finset.range (k + 1), c' r * psDeriv^[r] g =
        (∑ r ∈ Finset.range (k + 1), (if r = k then T * psDeriv (T ^ k) else 0) * psDeriv^[r] g) +
        (∑ r ∈ Finset.range (k + 1), (if r < k then T * psDeriv (c r) else 0) * psDeriv^[r] g) +
        (∑ r ∈ Finset.range (k + 1), (if 1 ≤ r ∧ r ≤ k then T * c (r - 1) else 0) * psDeriv^[r] g) := by
      simp only [c', add_mul, Finset.sum_add_distrib]
    rw [hsplit]
    have hp1 : ∑ r ∈ Finset.range (k + 1), (if r = k then T * psDeriv (T ^ k) else 0) * psDeriv^[r] g =
        T * (psDeriv (T ^ k) * psDeriv^[k] g) := by
      rw [Finset.sum_eq_single k]
      · simp; ring
      · intro r _ hr; simp [hr]
      · intro habs; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) habs
    have hp2 : ∑ r ∈ Finset.range (k + 1), (if r < k then T * psDeriv (c r) else 0) * psDeriv^[r] g =
        ∑ x ∈ Finset.range k, (T * psDeriv (c x)) * psDeriv^[x] g := by
      rw [Finset.sum_range_succ]; simp only [lt_self_iff_false, ↓reduceIte, zero_mul, add_zero]
      apply Finset.sum_congr rfl; intro x hx
      rw [if_pos (Finset.mem_range.mp hx)]
    have hp3 : ∑ r ∈ Finset.range (k + 1), (if 1 ≤ r ∧ r ≤ k then T * c (r - 1) else 0) * psDeriv^[r] g =
        ∑ x ∈ Finset.range k, (T * c x) * psDeriv^[x + 1] g := by
      rw [Finset.sum_range_succ']; simp only [Nat.not_succ_le_zero, false_and, ↓reduceIte, zero_mul, add_zero]
      apply Finset.sum_congr rfl; intro x hx
      have hxlt : x < k := Finset.mem_range.mp hx
      rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel]
    rw [hp1, hp2, hp3]; ring

/-- Non-vanishing of the `T`-weighted Wronskian `det ((T * psDeriv)^[k] (g j))`. -/
theorem weighted_wronskian_ne_zero {s : ℕ} (T : PowerSeries ℚ) (hT : T ≠ 0)
    (g : Fin s → PowerSeries ℚ)
    (hli : ∀ c : Fin s → ℚ, (∑ j : Fin s, PowerSeries.C (c j) * g j = 0) → ∀ j, c j = 0) :
    Matrix.det (Matrix.of (fun k j : Fin s => (fun f => T * psDeriv f)^[k.val] (g j))) ≠ 0 := by
  classical
  choose coeffOf hcoeffOf using iter_T_psDeriv_expand T
  let L : Matrix (Fin s) (Fin s) (PowerSeries ℚ) :=
    Matrix.of fun k r =>
      if r.val = k.val then T ^ k.val
      else if r.val < k.val then coeffOf k.val r.val
      else 0
  let W : Matrix (Fin s) (Fin s) (PowerSeries ℚ) :=
    Matrix.of fun r j => psDeriv^[r.val] (g j)
  have hG_eq : Matrix.of (fun k j : Fin s => (fun f => T * psDeriv f)^[k.val] (g j)) = L * W := by
    apply Matrix.ext
    intro k j
    simp only [Matrix.of_apply, Matrix.mul_apply, L, W]
    rw [hcoeffOf k.val (g j)]
    have hsplit : ∑ r : Fin s,
        (if r.val = k.val then T ^ k.val else if r.val < k.val then coeffOf k.val r.val else 0) *
          psDeriv^[r.val] (g j) =
        T ^ k.val * psDeriv^[k.val] (g j) +
        ∑ r ∈ Finset.univ.filter (fun r : Fin s => r.val < k.val), coeffOf k.val r.val * psDeriv^[r.val] (g j) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k), if_pos rfl]
      congr 1
      rw [Finset.sum_filter]
      have hsub : ∀ r ∈ Finset.univ.erase k,
          (if r.val = k.val then T ^ k.val else if r.val < k.val then coeffOf k.val r.val else 0) *
            psDeriv^[r.val] (g j) =
          if r.val < k.val then coeffOf k.val r.val * psDeriv^[r.val] (g j) else 0 := by
        intro r hr
        have hne : r.val ≠ k.val := fun heq => (Finset.mem_erase.mp hr).1 (Fin.ext heq)
        rw [if_neg hne]; split_ifs <;> simp
      rw [Finset.sum_congr rfl hsub]
      rw [← Finset.add_sum_erase Finset.univ
        (fun r : Fin s => if r.val < k.val then coeffOf k.val r.val * psDeriv^[r.val] (g j) else 0)
        (Finset.mem_univ k)]
      simp
    rw [hsplit]
    apply congrArg (T ^ k.val * psDeriv^[k.val] (g j) + ·)
    symm
    refine Finset.sum_nbij (fun r : Fin s => r.val) ?_ ?_ ?_ ?_
    · intro r hr; exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2
    · intro r₁ _ r₂ _ heq; exact Fin.ext heq
    · intro r hr
      have hrlt : r < k.val := Finset.mem_range.mp hr
      exact ⟨⟨r, lt_trans hrlt k.isLt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrlt⟩, rfl⟩
    · intro r _; rfl
  have hL_tri : L.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i.val < j.val := hij
    dsimp only [L, Matrix.of_apply]
    rw [if_neg (ne_of_gt hlt), if_neg (not_lt.mpr (le_of_lt hlt))]
  have hL_det : L.det = ∏ k : Fin s, T ^ k.val := by
    rw [Matrix.det_of_lowerTriangular L hL_tri]
    apply Finset.prod_congr rfl; intro k _
    simp [L]
  rw [hG_eq, Matrix.det_mul, hL_det]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero k.val hT)
  · exact wronskian_ne_zero_of_linearIndependent g hli

end GrasGreenbergBrocard
