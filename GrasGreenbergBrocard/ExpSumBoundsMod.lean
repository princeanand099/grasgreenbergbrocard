import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.ValuationParityDigits
import GrasGreenbergBrocard.ValuationParityVaaler
import GrasGreenbergBrocard.ExpSumBounds
import GrasGreenbergBrocard.ValuationParityThmHelpers
import GrasGreenbergBrocard.ValuationParityThm

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard


theorem prime_exp_sum_bounds_mod (h_mod : ℕ) (hh_mod : 2 ≤ h_mod)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
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
        (∀ r ∈ A, |(h r : ℤ)| ≤ (H : ℤ)) →
        (∀ r ∈ A, (2 : ℝ) ^ (- (R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) / P ^ r) →
        (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) →
        0 ≤ W₀ →
        let r₀ := (A.filter (fun r => h r ≠ 0)).min' (by
          obtain ⟨r, hrA, hr0⟩ := hA_nz
          exact ⟨r, Finset.mem_filter.mpr ⟨hrA, hr0⟩⟩)
        let T₀ := |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀
        let F : ℝ → ℝ := fun t => ∑ r ∈ A, (h r : ℝ) * (n : ℝ) / ((h_mod : ℝ) * t ^ r)
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
  let Mmax : ℝ := ∏ k ∈ Finset.range (5 * R + 2), ((R + k : ℕ) : ℝ)
  let c₁_low : ℝ := (1 / (2 * (h_mod : ℝ))) * (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ))
  let c₂_high : ℝ := (2 / (h_mod : ℝ)) * Mmax
  let C₂ : ℝ := C * ((2 : ℝ) ^ ((R : ℝ) / 6) + 1)
  have hh_pos : (0 : ℝ) < (h_mod : ℝ) := by exact_mod_cast (by omega : 0 < h_mod)
  have hR1 : 1 ≤ R := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hδ0]; linarith)
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
      ((Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ) * ((R : ℝ) * Mmax / (h_mod : ℝ) + 1) ≤ c₁_low := by
    have h0 : Tendsto (fun n : ℕ => ((Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ) * ((R : ℝ) * Mmax / (h_mod : ℝ) + 1))
        atTop (nhds 0) := by
      simpa using htend1.mul_const ((R : ℝ) * Mmax / (h_mod : ℝ) + 1)
    have hc₁_pos : 0 < c₁_low := by
      unfold c₁_low
      exact mul_pos (by positivity) (zpow_pos (by norm_num) _)
    exact (h0.eventually (Iio_mem_nhds hc₁_pos)).mono (fun _ h => h.le)
  have hev2 : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ)) ^ (R + 5) / (n : ℝ) ^ (δ * η') ≤ 1 :=
    (htend2.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)
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
  set F : ℝ → ℝ := fun t => ∑ r ∈ A, (h r : ℝ) * (n : ℝ) / ((h_mod : ℝ) * t ^ r)
  have hr₀_flt : r₀ ∈ A.filter (fun r => h r ≠ 0) := Finset.min'_mem _ hne_flt
  have hr₀_mem : r₀ ∈ A := (Finset.mem_filter.mp hr₀_flt).1
  have hr₀_ne : h r₀ ≠ 0 := (Finset.mem_filter.mp hr₀_flt).2
  have hP_ge1 : (1 : ℝ) ≤ P := by
    calc (1 : ℝ) ≤ (n : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) hδ0.le
      _ ≤ P := hP_lo
  have hP_pos : 0 < P := by linarith
  have hT₀_ge : (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ T₀ := by
    have hh1 : (1 : ℝ) ≤ |(h r₀ : ℝ)| := by exact_mod_cast Int.one_le_abs hr₀_ne
    calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R
        ≤ (n : ℝ) / P ^ r₀ := hPhase r₀ hr₀_mem
      _ = 1 * ((n : ℝ) / P ^ r₀) := (one_mul _).symm
      _ ≤ |(h r₀ : ℝ)| * ((n : ℝ) / P ^ r₀) :=
          mul_le_mul_of_nonneg_right hh1 (div_nonneg (Nat.cast_nonneg n) (pow_nonneg hP_pos.le _))
      _ = T₀ := by ring
  have hDeriv : ∀ (j : ℕ), 1 ≤ j → j ≤ 5 * R + 2 →
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
        ∀ t ∈ Set.Icc P (2 * P),
          c₁ * T₀ / P ^ j ≤ |iteratedDeriv j F t| ∧ |iteratedDeriv j F t| ≤ c₂ * T₀ / P ^ j := by
    intro j hj1 hj2
    have hc₁_pos : 0 < c₁_low := by
      unfold c₁_low
      exact mul_pos (by positivity) (zpow_pos (by norm_num) _)
    refine ⟨c₁_low, c₂_high, hc₁_pos, ?_, ?_⟩
    · unfold c₁_low c₂_high
      have hpow_le : (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ)) ≤ 1 :=
        zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
      have h1 : (1 / (2 * (h_mod : ℝ))) * (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ)) ≤ 1 / (2 * (h_mod : ℝ)) :=
        mul_le_of_le_one_right (by positivity) hpow_le
      have h2 : 1 / (2 * (h_mod : ℝ)) ≤ (2 / (h_mod : ℝ)) * Mmax := by
        calc 1 / (2 * (h_mod : ℝ)) ≤ 2 / (h_mod : ℝ) := by
              apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
              nlinarith
          _ ≤ (2 / (h_mod : ℝ)) * Mmax := le_mul_of_one_le_right (by positivity) hM1
      linarith
    · intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hP_pos ht.1
      have hF_eq : F = ∑ r ∈ A, fun x : ℝ => ((h r : ℝ) * (n : ℝ) / (h_mod : ℝ)) * x ^ (-(r : ℤ)) := by
        ext x
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [zpow_neg, zpow_natCast]
        ring
      have hIter : iteratedDeriv j F t =
          ∑ r ∈ A, ((h r : ℝ) * (n : ℝ) / (h_mod : ℝ)) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ)) := by
        rw [hF_eq]
        have hpow_cd : ∀ r : ℕ, ContDiffAt ℝ j (fun x : ℝ => x ^ (-(r : ℤ))) t := by
          intro r
          have hpow_eq : (fun x : ℝ => x ^ (-(r : ℤ))) = (fun x : ℝ => (x⁻¹) ^ r) := by
            ext x; rw [zpow_neg, zpow_natCast, inv_pow]
          rw [hpow_eq]
          exact (contDiffAt_id.inv ht_pos.ne').pow r
        have hcd : ∀ r ∈ A, ContDiffAt ℝ j
            (fun x : ℝ => ((h r : ℝ) * (n : ℝ) / (h_mod : ℝ)) * x ^ (-(r : ℤ))) t :=
          fun r _ => contDiffAt_const.mul (hpow_cd r)
        rw [iteratedDeriv_sum hcd]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [iteratedDeriv_const_mul _ (hpow_cd r), iteratedDeriv_neg_pow r j t ht_pos]
        ring
      rw [hIter]
      have hsplit := Finset.add_sum_erase A
        (fun r => ((h r : ℝ) * (n : ℝ) / (h_mod : ℝ)) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ))) hr₀_mem
      rw [← hsplit]
      have hterm0_lo : 2 * c₁_low * T₀ / P ^ j ≤
          |((h r₀ : ℝ) * (n : ℝ) / (h_mod : ℝ)) * negPowDerivCoeff r₀ j * t ^ (-((r₀ + j : ℕ) : ℤ))| := by
        rw [abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ)),
          abs_of_pos hh_pos,
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
          exact zpow_le_zpow_right₀ (by norm_num) (by have := (hA_range r₀ hr₀_mem).2; omega)
        have hP_eq : P ^ (-((r₀ + j : ℕ) : ℤ)) = (1 / P ^ r₀) / P ^ j := by
          rw [zpow_neg, zpow_natCast, pow_add]
          field_simp [hP_pos.ne']
        calc 2 * c₁_low * T₀ / P ^ j
            = (1 / (h_mod : ℝ)) * (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ)) *
                (|(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀) / P ^ j := by
              unfold c₁_low; field_simp [hh_pos.ne']
          _ = (|(h r₀ : ℝ)| * (n : ℝ) / (h_mod : ℝ)) * 1 *
                ((2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ)) * ((1 / P ^ r₀) / P ^ j)) := by ring
          _ ≤ (|(h r₀ : ℝ)| * (n : ℝ) / (h_mod : ℝ)) * |negPowDerivCoeff r₀ j| * t ^ (-((r₀ + j : ℕ) : ℤ)) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hcoeff_ge (by positivity)
              · rw [← hP_eq]; exact le_trans h2P ht_le
              · positivity
              · positivity
      have hterm0_hi : |((h r₀ : ℝ) * (n : ℝ) / (h_mod : ℝ)) * negPowDerivCoeff r₀ j * t ^ (-((r₀ + j : ℕ) : ℤ))| ≤
          (1 / (h_mod : ℝ)) * Mmax * T₀ / P ^ j := by
        rw [abs_mul, abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ)),
          abs_of_pos hh_pos,
          abs_of_pos (zpow_pos ht_pos (-((r₀ + j : ℕ) : ℤ)))]
        have hcoeff_le : |negPowDerivCoeff r₀ j| ≤ Mmax := by
          unfold negPowDerivCoeff Mmax
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_nonneg (Finset.prod_nonneg (fun k _ => by positivity))]
          have hr₀_le : r₀ ≤ R := (hA_range r₀ hr₀_mem).2
          have hN1 : ∏ k ∈ Finset.range j, (r₀ + k) ≤ ∏ k ∈ Finset.range j, (R + k) :=
            Finset.prod_le_prod' (fun k _ => by omega)
          have hN2 : ∏ k ∈ Finset.range j, (R + k) ≤ ∏ k ∈ Finset.range (5 * R + 2), (R + k) := by
            rw [← Finset.prod_sdiff (Finset.range_mono hj2)]
            exact Nat.le_mul_of_pos_left _ (Finset.prod_pos (fun k _ => by omega))
          exact_mod_cast le_trans hN1 hN2
        have ht_ge : t ^ (-((r₀ + j : ℕ) : ℤ)) ≤ P ^ (-((r₀ + j : ℕ) : ℤ)) := by
          rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
          exact inv_anti₀ (pow_pos hP_pos _) (pow_le_pow_left₀ hP_pos.le ht.1 _)
        have hP_eq : P ^ (-((r₀ + j : ℕ) : ℤ)) = (1 / P ^ r₀) / P ^ j := by
          rw [zpow_neg, zpow_natCast, pow_add]
          field_simp [hP_pos.ne']
        calc (|(h r₀ : ℝ)| * (n : ℝ) / (h_mod : ℝ)) * |negPowDerivCoeff r₀ j| * t ^ (-((r₀ + j : ℕ) : ℤ))
            ≤ (|(h r₀ : ℝ)| * (n : ℝ) / (h_mod : ℝ)) * Mmax * ((1 / P ^ r₀) / P ^ j) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hcoeff_le (by positivity)
              · rw [← hP_eq]; exact ht_ge
              · positivity
              · positivity
          _ = (1 / (h_mod : ℝ)) * Mmax * T₀ / P ^ j := by unfold T₀; ring
      have htail_hi : |∑ r ∈ A.erase r₀,
          ((h r : ℝ) * (n : ℝ) / (h_mod : ℝ)) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ))| ≤
          c₁_low * T₀ / P ^ j := by
        have h_each : ∀ r ∈ A.erase r₀,
            |((h r : ℝ) * (n : ℝ) / (h_mod : ℝ)) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ))| ≤
            ((Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ * (Mmax / (h_mod : ℝ))) * (T₀ / P ^ j) := by
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
              abs_of_pos hh_pos,
              abs_of_pos (zpow_pos ht_pos (-((r + j : ℕ) : ℤ)))]
            have hh_le : |(h r : ℝ)| ≤ (Real.log (n : ℝ)) ^ (R + 2) := by
              have hhZ : |(h r : ℝ)| ≤ (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) := by
                exact_mod_cast hh_bound r hrA
              have hfl : (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) :=
                Nat.floor_le (by positivity)
              linarith
            have hcoeff_le : |negPowDerivCoeff r j| ≤ Mmax := by
              unfold negPowDerivCoeff Mmax
              rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
                abs_of_nonneg (Finset.prod_nonneg (fun k _ => by positivity))]
              have hN1 : ∏ k ∈ Finset.range j, (r + k) ≤ ∏ k ∈ Finset.range j, (R + k) :=
                Finset.prod_le_prod' (fun k _ => by omega)
              have hN2 : ∏ k ∈ Finset.range j, (R + k) ≤ ∏ k ∈ Finset.range (5 * R + 2), (R + k) := by
                rw [← Finset.prod_sdiff (Finset.range_mono hj2)]
                exact Nat.le_mul_of_pos_left _ (Finset.prod_pos (fun k _ => by omega))
              exact_mod_cast le_trans hN1 hN2
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
            calc (|(h r : ℝ)| * (n : ℝ) / (h_mod : ℝ)) * |negPowDerivCoeff r j| * t ^ (-((r + j : ℕ) : ℤ))
                ≤ ((Real.log (n : ℝ)) ^ (R + 2) * (n : ℝ) / (h_mod : ℝ)) * Mmax *
                    ((1 / P) * ((1 / P ^ r₀) / P ^ j)) := by
                  apply mul_le_mul
                  · apply mul_le_mul
                    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh_le (by positivity)) hh_pos.le
                    · exact hcoeff_le
                    · positivity
                    · positivity
                  · rw [← hP_eq]; exact ht_le
                  · positivity
                  · positivity
              _ = ((Real.log (n : ℝ)) ^ (R + 2) / P * (Mmax / (h_mod : ℝ))) * ((n : ℝ) / P ^ r₀ / P ^ j) := by ring
              _ ≤ ((Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ * (Mmax / (h_mod : ℝ))) * (T₀ / P ^ j) := by
                  apply mul_le_mul
                  · apply mul_le_mul_of_nonneg_right _ (by unfold Mmax; positivity)
                    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hP_lo
                  · unfold T₀
                    calc (n : ℝ) / P ^ r₀ / P ^ j
                        = 1 * (n : ℝ) / P ^ r₀ / P ^ j := by ring
                      _ ≤ |(h r₀ : ℝ)| * (n : ℝ) / P ^ r₀ / P ^ j :=
                          div_le_div_of_nonneg_right
                            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh0 (by positivity)) (by positivity))
                            (by positivity)
                  · positivity
                  · positivity
        calc |∑ r ∈ A.erase r₀,
              ((h r : ℝ) * (n : ℝ) / (h_mod : ℝ)) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ))|
            ≤ ∑ r ∈ A.erase r₀,
                |((h r : ℝ) * (n : ℝ) / (h_mod : ℝ)) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _r ∈ A.erase r₀,
                ((Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ * (Mmax / (h_mod : ℝ))) * (T₀ / P ^ j) :=
              Finset.sum_le_sum h_each
          _ = (((A.erase r₀).card : ℝ)) *
                (((Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ * (Mmax / (h_mod : ℝ))) * (T₀ / P ^ j)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (R : ℝ) * (((Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ * (Mmax / (h_mod : ℝ))) * (T₀ / P ^ j)) := by
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
              calc (R : ℝ) * ((Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ * (Mmax / (h_mod : ℝ)))
                  ≤ ((Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ) * ((R : ℝ) * Mmax / (h_mod : ℝ) + 1) := by
                    have h1 : 0 ≤ (Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ := by positivity
                    have h_eq : (R : ℝ) * ((Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ * (Mmax / (h_mod : ℝ))) =
                        ((Real.log (n : ℝ)) ^ (R + 2) / (n : ℝ) ^ δ) * ((R : ℝ) * Mmax / (h_mod : ℝ)) := by ring
                    rw [h_eq]
                    exact mul_le_mul_of_nonneg_left (by linarith) h1
                _ ≤ c₁_low := hsmall1
          _ = c₁_low * T₀ / P ^ j := by ring
      constructor
      · have hrev := abs_sub_abs_le_abs_add
          (((h r₀ : ℝ) * (n : ℝ) / (h_mod : ℝ)) * negPowDerivCoeff r₀ j * t ^ (-((r₀ + j : ℕ) : ℤ)))
          (∑ r ∈ A.erase r₀, ((h r : ℝ) * (n : ℝ) / (h_mod : ℝ)) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ)))
        have h2c : 2 * c₁_low * T₀ / P ^ j = c₁_low * T₀ / P ^ j + c₁_low * T₀ / P ^ j := by ring
        linarith
      · have htri := abs_add_le
          (((h r₀ : ℝ) * (n : ℝ) / (h_mod : ℝ)) * negPowDerivCoeff r₀ j * t ^ (-((r₀ + j : ℕ) : ℤ)))
          (∑ r ∈ A.erase r₀, ((h r : ℝ) * (n : ℝ) / (h_mod : ℝ)) * negPowDerivCoeff r j * t ^ (-((r + j : ℕ) : ℤ)))
        have hc1_le : c₁_low ≤ (1 / (h_mod : ℝ)) * Mmax := by
          unfold c₁_low
          have hpow_le : (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ)) ≤ 1 :=
            zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
          have h1 : (1 / (2 * (h_mod : ℝ))) * (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ)) ≤ 1 / (2 * (h_mod : ℝ)) :=
            mul_le_of_le_one_right (by positivity) hpow_le
          have h2 : 1 / (2 * (h_mod : ℝ)) ≤ (1 / (h_mod : ℝ)) * Mmax := by
            calc 1 / (2 * (h_mod : ℝ)) ≤ 1 / (h_mod : ℝ) := by
                  apply div_le_div_of_nonneg_left (by norm_num) hh_pos (by linarith)
              _ ≤ (1 / (h_mod : ℝ)) * Mmax := le_mul_of_one_le_right (by positivity) hM1
          linarith
        have hc1_T : c₁_low * T₀ / P ^ j ≤ ((1 / (h_mod : ℝ)) * Mmax) * T₀ / P ^ j := by
          apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc1_le (by positivity)) (by positivity)
        have h2m : c₂_high * T₀ / P ^ j = (1 / (h_mod : ℝ)) * Mmax * T₀ / P ^ j + ((1 / (h_mod : ℝ)) * Mmax) * T₀ / P ^ j := by
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

/-! ### Additive Character Orthogonality and Vaaler Modulus-`h` Approximation -/


end GrasGreenbergBrocard
