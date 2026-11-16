import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false

/-!
# Lemma 2.3: Vaaler's Trigonometric Polynomial Approximation

Formalizes Section 2.3 (eq. 2.8–2.9):
- `Psi_tilde`, `B_tilde`
- Exact cancellation of even harmonics `h = 2m` (`1 ≤ |m| ≤ H`)
- Coefficient bounds `|c_tilde_h| ≤ 2 / (π |h|)` and `‖b_tilde_h‖ < 3 / (H + 1)`
- `parity_approx_by_Psi_tilde`: `|(-1)^⌊x⌋ - Ψ̃_H(x)| ≤ Re(B̃_H(x))` for all `x ∈ ℝ`
- `Psi_tilde_L1_bound`: `∑_{1 ≤ |h| ≤ 2H+1, 2 ∤ h} |c_tilde_h(H)| ≤ (4 / π) * (log (2H + 1) + 1)`
-/

noncomputable section

open Real Finset BigOperators

namespace GrasGreenbergBrocard

/-- Sawtooth function `ψ(t) := t - ⌊t⌋ - 1/2`. -/
def sawtoothPsi (t : ℝ) : ℝ :=
  t - (Int.floor t : ℝ) - 1 / 2

/-- For `x ∉ ℤ`, `(-1)^⌊x⌋ = 2 ψ(x) - 4 ψ(x / 2)`. -/
theorem neg_one_pow_floor_eq_sawtooth {x : ℝ} (hx : ∀ m : ℤ, x ≠ (m : ℝ)) :
    (-1 : ℝ) ^ (Int.floor x) = 2 * sawtoothPsi x - 4 * sawtoothPsi (x / 2) := by
  unfold sawtoothPsi
  have hfl : Int.floor x = 2 * Int.floor (x / 2) ∨ Int.floor x = 2 * Int.floor (x / 2) + 1 := by
    have h1 : (Int.floor (x / 2) : ℝ) ≤ x / 2 := Int.floor_le (x / 2)
    have h2 : x / 2 < (Int.floor (x / 2) : ℝ) + 1 := Int.lt_floor_add_one (x / 2)
    have h3 : (2 * Int.floor (x / 2) : ℤ) ≤ Int.floor x := by
      rw [Int.le_floor]
      push_cast
      linarith
    have h4 : Int.floor x < 2 * Int.floor (x / 2) + 2 := by
      rw [Int.floor_lt]
      push_cast
      linarith
    omega
  rcases hfl with h | h
  · rw [h]
    have hpow : (-1 : ℝ) ^ (2 * Int.floor (x / 2)) = 1 := by
      rw [zpow_mul, zpow_two, neg_one_sq, one_zpow]
    rw [hpow, Int.cast_mul, Int.cast_ofNat]
    ring
  · rw [h]
    have hpow : (-1 : ℝ) ^ (2 * Int.floor (x / 2) + 1) = -1 := by
      rw [zpow_add₀ (by norm_num), zpow_mul, zpow_two, neg_one_sq, one_zpow, zpow_one]
      norm_num
    rw [hpow, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
    ring

/-- Harmonic sum bound: `∑_{k=1}^N 1/k ≤ log N + 1` for `N ≥ 1`. -/
theorem harmonic_sum_le_log_add_one {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ≤ Real.log (N : ℝ) + 1 := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hlog : (1 : ℝ) / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) := by
      have h1 : Real.log ((m : ℝ) / ((m : ℝ) + 1)) ≤ (m : ℝ) / ((m : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h1
      linarith
    push_cast
    linarith

/-- **Lemma 2.3 (Vaaler's Trigonometric Polynomial Approximation)**:
Existence of `Ψ̃_H` and `B̃_H` with exact odd-frequency support, coefficient bounds,
pointwise parity majorization, and `L¹` norm bound (eq. 2.8–2.9). -/
theorem vaaler_parity_approx (H : ℕ) (hH : 1 ≤ H) :
    ∃ (c_tilde : ℤ → ℂ) (b_tilde : ℤ → ℂ),
      (∀ h : ℤ, Even h → c_tilde h = 0) ∧
      (∀ h : ℤ, h ≠ 0 → ‖c_tilde h‖ ≤ 2 / (Real.pi * |(h : ℝ)|)) ∧
      (b_tilde 0 = (2 / ((H : ℝ) + 1) : ℂ)) ∧
      (∀ h : ℤ, ‖b_tilde h‖ < 3 / ((H : ℝ) + 1)) ∧
      (let Psi_tilde : ℝ → ℂ := fun x =>
          ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
            c_tilde h * eExp ((h : ℝ) * x / 2)
       let B_tilde : ℝ → ℂ := fun x =>
          ∑ h ∈ Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1),
            b_tilde h * eExp ((h : ℝ) * x / 2)
       (∀ x : ℝ, ‖((-1 : ℝ) ^ (Int.floor x) : ℂ) - Psi_tilde x‖ ≤ (B_tilde x).re) ∧
       (∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
          ‖c_tilde h‖ ≤ (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1))) := by
  obtain ⟨W, hW_bounds, hVaaler⟩ := vaaler_extremal_polynomials
  obtain ⟨b1, hb1_0, hb1_bound, h1⟩ := hVaaler H hH
  obtain ⟨b2, hb2_0, hb2_bound, h2⟩ := hVaaler (2 * H + 1) (by omega)
  let c1 : ℤ → ℂ := fun h =>
    if h = 0 then 0
    else -(1 / (2 * Real.pi * Complex.I * (h : ℂ))) * (W (|(h : ℝ)| / ((H : ℝ) + 1)) : ℂ)
  let c2 : ℤ → ℂ := fun h =>
    if h = 0 then 0
    else -(1 / (2 * Real.pi * Complex.I * (h : ℂ))) * (W (|(h : ℝ)| / ((2 * H + 1 : ℕ) + 1 : ℝ)) : ℂ)
  let c_tilde : ℤ → ℂ := fun h =>
    if Even h then 0 else -4 * c2 h
  let b_tilde : ℤ → ℂ := fun h =>
    (if Even h then 2 * b1 (h / 2) else 0) + 4 * b2 h
  refine ⟨c_tilde, b_tilde, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    simp [c_tilde, hh]
  · intro h hh
    by_cases hev : Even h
    · simp only [c_tilde, hev, ↓reduceIte, norm_zero]
      positivity
    · simp only [c_tilde, hev, ↓reduceIte, c2, hh]
      rw [norm_mul, norm_neg, show (4 : ℂ) = ((4 : ℝ) : ℂ) from rfl, Complex.norm_real]
      have hc2_norm : ‖-(1 / (2 * Real.pi * Complex.I * (h : ℂ))) *
          (W (|(h : ℝ)| / ((2 * H + 1 : ℕ) + 1 : ℝ)) : ℂ)‖ ≤ 1 / (2 * Real.pi * |(h : ℝ)|) := by
        rw [norm_mul, norm_neg, norm_div, norm_one, Complex.norm_real]
        have hW : |W (|(h : ℝ)| / ((2 * H + 1 : ℕ) + 1 : ℝ))| ≤ 1 := by
          have hb := hW_bounds (|(h : ℝ)| / ((2 * H + 1 : ℕ) + 1 : ℝ))
          rw [abs_of_nonneg hb.1]
          exact hb.2
        have hden : ‖2 * Real.pi * Complex.I * (h : ℂ)‖ = 2 * Real.pi * |(h : ℝ)| := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
          have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
            rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_real,
              abs_of_pos (by positivity)]
          have hhC : ‖(h : ℂ)‖ = |(h : ℝ)| := by
            rw [← Complex.ofReal_intCast, Complex.norm_real]
          rw [show (2 : ℂ) * Real.pi = (2 : ℂ) * (Real.pi : ℂ) from rfl, h2pi, hhC]
        rw [hden]
        calc (1 / (2 * Real.pi * |(h : ℝ)|)) * |W (|(h : ℝ)| / ((2 * H + 1 : ℕ) + 1 : ℝ))|
            ≤ (1 / (2 * Real.pi * |(h : ℝ)|)) * 1 :=
              mul_le_mul_of_nonneg_left hW (by positivity)
          _ = 1 / (2 * Real.pi * |(h : ℝ)|) := mul_one _
      calc |4| * ‖-(1 / (2 * Real.pi * Complex.I * (h : ℂ))) *
              (W (|(h : ℝ)| / ((2 * H + 1 : ℕ) + 1 : ℝ)) : ℂ)‖
          ≤ 4 * (1 / (2 * Real.pi * |(h : ℝ)|)) := by
            rw [abs_of_pos (by norm_num)]
            exact mul_le_mul_of_nonneg_left hc2_norm (by norm_num)
        _ = 2 / (Real.pi * |(h : ℝ)|) := by ring
  · simp only [b_tilde, even_zero, ↓reduceIte, Int.zero_ediv, hb1_0, hb2_0]
    push_cast
    have hH0 : (H : ℂ) + 1 ≠ 0 := by
      have : (0 : ℝ) < (H : ℝ) + 1 := by positivity
      exact_mod_cast this.ne'
    field_simp [hH0]
    ring
  · intro h
    have hH_pos : (0 : ℝ) < (H : ℝ) + 1 := by positivity
    by_cases hev : Even h
    · simp only [b_tilde, hev, ↓reduceIte]
      calc ‖2 * b1 (h / 2) + 4 * b2 h‖
          ≤ ‖2 * b1 (h / 2)‖ + ‖4 * b2 h‖ := norm_add_le _ _
        _ = 2 * ‖b1 (h / 2)‖ + 4 * ‖b2 h‖ := by
            rw [norm_mul, norm_mul]
            congr 1
            · rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, Complex.norm_real, abs_of_pos (by norm_num)]
            · rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) from rfl, Complex.norm_real, abs_of_pos (by norm_num)]
        _ ≤ 2 * (1 / (2 * (H : ℝ) + 2)) + 4 * (1 / (2 * ((2 * H + 1 : ℕ) : ℝ) + 2)) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left (hb1_bound (h / 2)) (by norm_num)
            · exact mul_le_mul_of_nonneg_left (hb2_bound h) (by norm_num)
        _ = 2 / ((H : ℝ) + 1) := by push_cast; field_simp; ring
        _ < 3 / ((H : ℝ) + 1) := by
            apply div_lt_div_of_pos_right (by norm_num) hH_pos
    · simp only [b_tilde, hev, ↓reduceIte, zero_add]
      calc ‖4 * b2 h‖
          = 4 * ‖b2 h‖ := by
            rw [norm_mul, show (4 : ℂ) = ((4 : ℝ) : ℂ) from rfl, Complex.norm_real, abs_of_pos (by norm_num)]
        _ ≤ 4 * (1 / (2 * ((2 * H + 1 : ℕ) : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left (hb2_bound h) (by norm_num)
        _ = 1 / ((H : ℝ) + 1) := by push_cast; field_simp; ring
        _ < 3 / ((H : ℝ) + 1) := by
            apply div_lt_div_of_pos_right (by norm_num) hH_pos
  · dsimp only
    constructor
    · let Psi1 : ℝ → ℂ := fun t =>
        ∑ h ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (· ≠ 0), c1 h * eExp ((h : ℝ) * t)
      let Psi2 : ℝ → ℂ := fun t =>
        ∑ h ∈ (Finset.Icc (-((2 * H + 1 : ℕ) : ℤ)) ((2 * H + 1 : ℕ) : ℤ)).filter (· ≠ 0),
          c2 h * eExp ((h : ℝ) * t)
      let B1 : ℝ → ℂ := fun t =>
        ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), b1 h * eExp ((h : ℝ) * t)
      let B2 : ℝ → ℂ := fun t =>
        ∑ h ∈ Finset.Icc (-((2 * H + 1 : ℕ) : ℤ)) ((2 * H + 1 : ℕ) : ℤ), b2 h * eExp ((h : ℝ) * t)
      have hPsi_eq : ∀ x : ℝ,
          ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
            c_tilde h * eExp ((h : ℝ) * x / 2) = 2 * Psi1 x - 4 * Psi2 (x / 2) := by
        intro x
        have hS2 : Finset.Icc (-((2 * H + 1 : ℕ) : ℤ)) ((2 * H + 1 : ℕ) : ℤ) =
            Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1) := by
          congr 1 <;> push_cast <;> ring
        have hsplit2 : ((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0)) =
            ((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h)) ∪
            ((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Even h)) := by
          ext h
          simp only [Finset.mem_union, Finset.mem_filter, Int.not_odd_iff_even]
          tauto
        have hdisj2 : Disjoint
            ((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h))
            ((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Even h)) := by
          rw [Finset.disjoint_left]
          intro h hp1 hp2
          exact (Int.not_odd_iff_even.mpr (Finset.mem_filter.mp hp2).2.2) (Finset.mem_filter.mp hp1).2.2
        have hPsi2_split : Psi2 (x / 2) =
            (∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
              c2 h * eExp ((h : ℝ) * (x / 2))) +
            (∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Even h),
              c2 h * eExp ((h : ℝ) * (x / 2))) := by
          dsimp only [Psi2]
          rw [hS2, hsplit2, Finset.sum_union hdisj2]
        have h_even_match :
            4 * (∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Even h),
              c2 h * eExp ((h : ℝ) * (x / 2))) = 2 * Psi1 x := by
          dsimp only [Psi1]
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_bij (fun h _ => h / 2) ?_ ?_ ?_ ?_
          · intro h hh
            simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢
            obtain ⟨⟨hl, hu⟩, hne, ⟨k, hk⟩⟩ := hh
            have hk_eq : h / 2 = k := by omega
            rw [hk_eq]
            refine ⟨⟨by omega, by omega⟩, by omega⟩
          · intro h1 hh1 h2 hh2 heq
            simp only [Finset.mem_filter] at hh1 hh2
            obtain ⟨k1, hk1⟩ := hh1.2.2
            obtain ⟨k2, hk2⟩ := hh2.2.2
            omega
          · intro m hm
            simp only [Finset.mem_filter, Finset.mem_Icc] at hm
            refine ⟨2 * m, ?_, by omega⟩
            simp only [Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨by omega, by omega⟩, by omega, ⟨m, by omega⟩⟩
          · intro h hh
            simp only [Finset.mem_filter] at hh
            obtain ⟨k, hk⟩ := hh.2.2
            have hne : h ≠ 0 := hh.2.1
            have hk_ne : k ≠ 0 := by omega
            have h_div : h / 2 = k := by omega
            rw [h_div]
            simp only [c2, c1, hne, hk_ne, ↓reduceIte]
            have h_arg : |(h : ℝ)| / ((2 * H + 1 : ℕ) + 1 : ℝ) = |(k : ℝ)| / ((H : ℝ) + 1) := by
              have hkR : (h : ℝ) = 2 * (k : ℝ) := by exact_mod_cast (by omega : h = 2 * k)
              rw [hkR, abs_mul, abs_of_pos (by norm_num)]
              push_cast
              ring
            rw [h_arg]
            have hexp : eExp ((h : ℝ) * (x / 2)) = eExp ((k : ℝ) * x) := by
              congr 1
              have hkR : (h : ℝ) = 2 * (k : ℝ) := by exact_mod_cast (by omega : h = 2 * k)
              rw [hkR]
              ring
            rw [hexp]
            have h_cast : (h : ℂ) = 2 * (k : ℂ) := by exact_mod_cast (by omega : h = 2 * k)
            rw [h_cast]
            ring
        rw [hPsi2_split, mul_add, h_even_match]
        have hodd_sum :
            ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
              c_tilde h * eExp ((h : ℝ) * x / 2) =
            -4 * ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
              c2 h * eExp ((h : ℝ) * (x / 2)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun h hh => ?_)
          have hodd : Odd h := (Finset.mem_filter.mp hh).2.2
          have hnev : ¬ Even h := Int.not_even_iff_odd.mpr hodd
          simp only [c_tilde, hnev, ↓reduceIte]
          rw [show (h : ℝ) * x / 2 = (h : ℝ) * (x / 2) from by ring]
          ring
        rw [hodd_sum]
        ring
      have hB_eq : ∀ x : ℝ,
          (∑ h ∈ Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1),
            b_tilde h * eExp ((h : ℝ) * x / 2)) = 2 * B1 x + 4 * B2 (x / 2) := by
        intro x
        have hS2 : Finset.Icc (-((2 * H + 1 : ℕ) : ℤ)) ((2 * H + 1 : ℕ) : ℤ) =
            Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1) := by
          congr 1 <;> push_cast <;> ring
        dsimp only [b_tilde, B1, B2]
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib, hS2]
        have h_even_part :
            ∑ h ∈ Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1),
              (if Even h then 2 * b1 (h / 2) else 0) * eExp ((h : ℝ) * x / 2) =
            2 * ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), b1 h * eExp ((h : ℝ) * x) := by
          rw [← Finset.sum_filter (p := Even)]
          · rw [Finset.mul_sum]
            refine Finset.sum_bij (fun h _ => h / 2) ?_ ?_ ?_ ?_
            · intro h hh
              simp only [Finset.mem_filter, Finset.mem_Icc] at hh ⊢
              obtain ⟨⟨hl, hu⟩, ⟨k, hk⟩⟩ := hh
              have hk_eq : h / 2 = k := by omega
              rw [hk_eq]
              omega
            · intro h1 hh1 h2 hh2 heq
              simp only [Finset.mem_filter] at hh1 hh2
              obtain ⟨k1, hk1⟩ := hh1.2
              obtain ⟨k2, hk2⟩ := hh2.2
              omega
            · intro m hm
              simp only [Finset.mem_Icc] at hm
              refine ⟨2 * m, ?_, by omega⟩
              simp only [Finset.mem_filter, Finset.mem_Icc]
              exact ⟨⟨by omega, by omega⟩, ⟨m, by omega⟩⟩
            · intro h hh
              simp only [Finset.mem_filter] at hh
              obtain ⟨k, hk⟩ := hh.2
              have h_div : h / 2 = k := by omega
              rw [h_div]
              have hexp : eExp ((h : ℝ) * x / 2) = eExp ((k : ℝ) * x) := by
                congr 1
                have hkR : (h : ℝ) = 2 * (k : ℝ) := by exact_mod_cast (by omega : h = 2 * k)
                rw [hkR]
                ring
              rw [hexp]
              ring
          · intro h hh
            by_cases hev : Even h
            · simp [hev]
            · simp [hev]
        have h_odd_part :
            ∑ h ∈ Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1),
              4 * b2 h * eExp ((h : ℝ) * x / 2) =
            4 * ∑ h ∈ Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1),
              b2 h * eExp ((h : ℝ) * (x / 2)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun h _ => ?_)
          rw [show (h : ℝ) * x / 2 = (h : ℝ) * (x / 2) from by ring]
          ring
        rw [h_even_part, h_odd_part]
      intro x
      rw [hPsi_eq x, hB_eq x]
      have hre : (2 * B1 x + 4 * B2 (x / 2)).re = 2 * (B1 x).re + 4 * (B2 (x / 2)).re := by
        simp [Complex.add_re, Complex.mul_re]
      rw [hre]
      by_cases hx : ∃ m : ℤ, x = (m : ℝ)
      · obtain ⟨m, rfl⟩ := hx
        have hPsi1_zero : Psi1 (m : ℝ) = 0 := h1.2.2 m
        have hfl : Int.floor (m : ℝ) = m := Int.floor_intCast m
        have hB1_0 : (B1 (m : ℝ)).re = 1 / 2 := by
          have he : ∀ h : ℤ, eExp ((h : ℝ) * (m : ℝ)) = 1 := by
            intro h
            unfold eExp
            rw [show (2 : ℂ) * Real.pi * Complex.I * (((h : ℝ) * (m : ℝ) : ℝ) : ℂ) =
                ((h * m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) from by push_cast; ring]
            exact Complex.exp_int_mul_two_pi_mul_I (h * m)
          have hB1_eq : B1 (m : ℝ) = B1 0 := by
            dsimp only [B1]
            refine Finset.sum_congr rfl (fun h _ => ?_)
            rw [he h, mul_zero, show eExp 0 = 1 from by unfold eExp; simp]
          rw [hB1_eq]
          exact h1.2.1
        have h2_bound := (h2.1 ((m : ℝ) / 2)).2
        have hB2_nonneg := (h2.1 ((m : ℝ) / 2)).1
        rw [hPsi1_zero, mul_zero, zero_sub, hfl, hB1_0]
        have hnorm1 : ‖((-1 : ℝ) ^ m : ℂ)‖ = 1 := by
          rw [← Complex.ofReal_zpow, Complex.norm_real, abs_zpow, abs_neg, abs_one, one_zpow]
        rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
        · have hk_eq : (m : ℝ) / 2 = (k : ℝ) := by
            have : (m : ℝ) = 2 * (k : ℝ) := by exact_mod_cast (by omega : m = 2 * k)
            linarith
          have hPsi2_zero : Psi2 ((m : ℝ) / 2) = 0 := by rw [hk_eq]; exact h2.2.2 k
          rw [hPsi2_zero, mul_zero, neg_zero]
          calc ‖((-1 : ℝ) ^ m : ℂ)‖ = 1 := hnorm1
            _ = 2 * (1 / 2) + 4 * 0 := by norm_num
            _ ≤ 2 * (1 / 2) + 4 * (B2 ((m : ℝ) / 2)).re := by linarith [hB2_nonneg]
        · have hsaw_zero : sawtoothPsi ((m : ℝ) / 2) = 0 := by
            unfold sawtoothPsi
            have hfl_half : Int.floor ((m : ℝ) / 2) = k := by
              rw [Int.floor_eq_iff]
              have hmR : (m : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast (by omega : m = 2 * k + 1)
              constructor <;> linarith
            rw [hfl_half]
            have hmR : (m : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast (by omega : m = 2 * k + 1)
            linarith
          have hPsi2_norm : ‖Psi2 ((m : ℝ) / 2)‖ ≤ (B2 ((m : ℝ) / 2)).re := by
            have h2b := h2_bound
            have h0 : (((m : ℝ) / 2 - (Int.floor ((m : ℝ) / 2) : ℝ) - 1 / 2 : ℝ) : ℂ) = 0 := by
              exact_mod_cast hsaw_zero
            rw [h0, zero_sub, norm_neg] at h2b
            exact h2b
          calc ‖((-1 : ℝ) ^ m : ℂ) - -4 * Psi2 ((m : ℝ) / 2)‖
              ≤ ‖((-1 : ℝ) ^ m : ℂ)‖ + ‖4 * Psi2 ((m : ℝ) / 2)‖ := by
                rw [show ((-1 : ℝ) ^ m : ℂ) - -4 * Psi2 ((m : ℝ) / 2) =
                    ((-1 : ℝ) ^ m : ℂ) + 4 * Psi2 ((m : ℝ) / 2) from by ring]
                exact norm_add_le _ _
            _ = 1 + 4 * ‖Psi2 ((m : ℝ) / 2)‖ := by
                rw [hnorm1, norm_mul, show (4 : ℂ) = ((4 : ℝ) : ℂ) from rfl,
                  Complex.norm_real, abs_of_pos (by norm_num)]
            _ ≤ 2 * (1 / 2) + 4 * (B2 ((m : ℝ) / 2)).re := by linarith
      · push_neg at hx
        rw [neg_one_pow_floor_eq_sawtooth hx]
        have hdiff : ((2 * sawtoothPsi x - 4 * sawtoothPsi (x / 2) : ℝ) : ℂ) - (2 * Psi1 x - 4 * Psi2 (x / 2)) =
            2 * (((sawtoothPsi x : ℝ) : ℂ) - Psi1 x) - 4 * (((sawtoothPsi (x / 2) : ℝ) : ℂ) - Psi2 (x / 2)) := by
          push_cast; ring
        rw [hdiff]
        calc ‖2 * (((sawtoothPsi x : ℝ) : ℂ) - Psi1 x) - 4 * (((sawtoothPsi (x / 2) : ℝ) : ℂ) - Psi2 (x / 2))‖
            ≤ ‖2 * (((sawtoothPsi x : ℝ) : ℂ) - Psi1 x)‖ + ‖4 * (((sawtoothPsi (x / 2) : ℝ) : ℂ) - Psi2 (x / 2))‖ :=
              norm_sub_le _ _
          _ = 2 * ‖((sawtoothPsi x : ℝ) : ℂ) - Psi1 x‖ + 4 * ‖((sawtoothPsi (x / 2) : ℝ) : ℂ) - Psi2 (x / 2)‖ := by
              rw [norm_mul, norm_mul, show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl,
                show (4 : ℂ) = ((4 : ℝ) : ℂ) from rfl, Complex.norm_real, Complex.norm_real,
                abs_of_pos (by norm_num), abs_of_pos (by norm_num)]
          _ ≤ 2 * (B1 x).re + 4 * (B2 (x / 2)).re :=
              add_le_add (mul_le_mul_of_nonneg_left (h1.1 x).2 (by norm_num))
                (mul_le_mul_of_nonneg_left (h2.1 (x / 2)).2 (by norm_num))
    · have hc_bound_each : ∀ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
          ‖c_tilde h‖ ≤ 2 / (Real.pi * |(h : ℝ)|) := by
        intro h hh
        have hne : h ≠ 0 := (Finset.mem_filter.mp hh).2.1
        have hev : ¬ Even h := Int.not_even_iff_odd.mpr (Finset.mem_filter.mp hh).2.2
        simp only [c_tilde, hev, ↓reduceIte, c2, hne]
        rw [norm_mul, norm_neg, show (4 : ℂ) = ((4 : ℝ) : ℂ) from rfl, Complex.norm_real,
          abs_of_pos (by norm_num)]
        have hW : |W (|(h : ℝ)| / ((2 * H + 1 : ℕ) + 1 : ℝ))| ≤ 1 := by
          have hb := hW_bounds (|(h : ℝ)| / ((2 * H + 1 : ℕ) + 1 : ℝ))
          rw [abs_of_nonneg hb.1]
          exact hb.2
        have hden : ‖2 * Real.pi * Complex.I * (h : ℂ)‖ = 2 * Real.pi * |(h : ℝ)| := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
          have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
            rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_real,
              abs_of_pos (by positivity)]
          have hhC : ‖(h : ℂ)‖ = |(h : ℝ)| := by
            rw [← Complex.ofReal_intCast, Complex.norm_real]
          rw [show (2 : ℂ) * Real.pi = (2 : ℂ) * (Real.pi : ℂ) from rfl, h2pi, hhC]
        calc 4 * (‖1 / (2 * Real.pi * Complex.I * (h : ℂ))‖ *
                ‖(W (|(h : ℝ)| / ((2 * H + 1 : ℕ) + 1 : ℝ)) : ℂ)‖)
            = 4 * ((1 / (2 * Real.pi * |(h : ℝ)|)) * |W (|(h : ℝ)| / ((2 * H + 1 : ℕ) + 1 : ℝ))|) := by
              rw [norm_div, norm_one, hden, Complex.norm_real]
          _ ≤ 4 * ((1 / (2 * Real.pi * |(h : ℝ)|)) * 1) := by
              apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW (by positivity)) (by norm_num)
          _ = 2 / (Real.pi * |(h : ℝ)|) := by ring
      let posSet : Finset ℤ := (Finset.Icc 1 (2 * H + 1)).map ⟨fun k => (k : ℤ), fun _ _ h => Int.ofNat.inj h⟩
      let negSet : Finset ℤ := (Finset.Icc 1 (2 * H + 1)).map ⟨fun k => -(k : ℤ), fun _ _ h => Int.ofNat.inj (neg_inj.mp h)⟩
      have hsub :
          ((Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h)) ⊆
          posSet ∪ negSet := by
        intro h hh
        simp only [Finset.mem_filter, Finset.mem_Icc] at hh
        rcases lt_trichotomy h 0 with hneg | rfl | hpos
        · right
          simp only [negSet, Finset.mem_map, Finset.mem_Icc, Function.Embedding.coeFn_mk]
          refine ⟨(-h).toNat, ⟨by omega, by omega⟩, by omega⟩
        · exact absurd rfl hh.2.1
        · left
          simp only [posSet, Finset.mem_map, Finset.mem_Icc, Function.Embedding.coeFn_mk]
          refine ⟨h.toNat, ⟨by omega, by omega⟩, by omega⟩
      have hdisj_pn : Disjoint posSet negSet := by
        rw [Finset.disjoint_left]
        intro h hp hn
        simp only [posSet, negSet, Finset.mem_map, Finset.mem_Icc, Function.Embedding.coeFn_mk] at hp hn
        obtain ⟨k1, hk1, rfl⟩ := hp
        obtain ⟨k2, hk2, hk_eq⟩ := hn
        omega
      have hsum_pos_neg :
          ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
            (2 / (Real.pi * |(h : ℝ)|)) ≤
          2 * ∑ k ∈ Finset.Icc 1 (2 * H + 1), (2 / (Real.pi * (k : ℝ))) := by
        calc ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
              (2 / (Real.pi * |(h : ℝ)|))
            ≤ ∑ h ∈ posSet ∪ negSet, (2 / (Real.pi * |(h : ℝ)|)) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
          _ = (∑ h ∈ posSet, (2 / (Real.pi * |(h : ℝ)|))) +
              (∑ h ∈ negSet, (2 / (Real.pi * |(h : ℝ)|))) := Finset.sum_union hdisj_pn
          _ = (∑ k ∈ Finset.Icc 1 (2 * H + 1), (2 / (Real.pi * (k : ℝ)))) +
              (∑ k ∈ Finset.Icc 1 (2 * H + 1), (2 / (Real.pi * (k : ℝ)))) := by
              congr 1
              · rw [Finset.sum_map]
                refine Finset.sum_congr rfl (fun k hk => ?_)
                simp only [Function.Embedding.coeFn_mk, Int.cast_natCast, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
              · rw [Finset.sum_map]
                refine Finset.sum_congr rfl (fun k hk => ?_)
                simp only [Function.Embedding.coeFn_mk, Int.cast_neg, Int.cast_natCast, abs_neg,
                  abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
          _ = 2 * ∑ k ∈ Finset.Icc 1 (2 * H + 1), (2 / (Real.pi * (k : ℝ))) := by ring
      calc ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
            ‖c_tilde h‖
          ≤ ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
              (2 / (Real.pi * |(h : ℝ)|)) := Finset.sum_le_sum hc_bound_each
        _ ≤ 2 * ∑ k ∈ Finset.Icc 1 (2 * H + 1), (2 / (Real.pi * (k : ℝ))) := hsum_pos_neg
        _ = (4 / Real.pi) * ∑ k ∈ Finset.Icc 1 (2 * H + 1), (1 : ℝ) / (k : ℝ) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => by ring)
        _ ≤ (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hle := harmonic_sum_le_log_add_one (N := 2 * H + 1) (by omega)
            push_cast at hle
            exact hle

end GrasGreenbergBrocard
