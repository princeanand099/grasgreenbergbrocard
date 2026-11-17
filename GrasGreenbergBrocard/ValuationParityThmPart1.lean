import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.ValuationParityDigits
import GrasGreenbergBrocard.ValuationParityVaaler
import GrasGreenbergBrocard.ExpSumBounds
import GrasGreenbergBrocard.ValuationParityThmHelpers

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard

/-! ### Theorem 2.5(i): Second-Order Discrepancy Formula (eq. 2.15) -/

/-- **Theorem 2.5(i) (Second-Order Discrepancy Formula)**:
`Δ_parity(n) = (log 2 - 1 - Σ*_parity(n)) n + O(n / log n)` (eq. 2.15). -/
theorem Delta_parity_second_order :
    (fun n : ℕ => Delta_parity n - (Real.log 2 - 1 - Sigma_star_parity n) * (n : ℝ))
      =O[atTop] (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  obtain ⟨c₁, hc₁, hdlvp⟩ := de_la_vallee_poussin_theta
  obtain ⟨C₁, hC₁⟩ := hdlvp.bound
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp hC₁
  obtain ⟨Cθ, hCθ_pos, hCθ⟩ := thetaPrime_le_linear
  obtain ⟨Cm, hCm_pos, hCm⟩ := mertens_div_p_sum_le
  obtain ⟨η', η, hη', hη, C₁e, C₂e, C₃e, hC₁e, hC₂e, hC₃e, hExp⟩ :=
    prime_exp_sum_bounds (1 / 3 : ℝ) (by norm_num) (by norm_num)
  obtain ⟨C_ed, hC_ed⟩ := E_digit_isBigO_sqrt.bound
  have hlog_ge2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ Real.log (n : ℝ) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  have h_main_conds : ∀ᶠ n : ℕ in atTop,
      (Real.sqrt (n : ℝ) < (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)) ∧
      ((n : ℝ) ^ (1 / 3 : ℝ) ≤ (Nat.sqrt n : ℝ)) ∧
      ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12) ∧
      (4 ≤ Nat.floor ((Real.log (n : ℝ)) ^ 48)) ∧
      (1 ≤ Nat.floor ((Real.log (n : ℝ)) ^ 5)) ∧
      ((Real.log (n : ℝ)) ^ 48 ≤ 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)) ∧
      ((Real.log (n : ℝ)) ^ 5 ≤ 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ)) ∧
      (max X₁ 4 ≤ (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)) ∧
      ((Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ^ 2 *
        Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)))) *
          Real.log (n : ℝ) ≤ 1) ∧
      ((2 : ℝ) ^ (-(Nat.floor (1 / (1 / 3 : ℝ)) : ℕ) : ℤ) *
        (Real.log (n : ℝ)) ^ (6 * Nat.floor (1 / (1 / 3 : ℝ)) + 30) ≤
          (Real.log (n : ℝ)) ^ 48 / 2) ∧
      (2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1 ≤ (Real.log (n : ℝ)) ^ 12) ∧
      ((Real.log (2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1) + 1) *
        (Real.log (n : ℝ) / Real.log 2 + 2) ≤ (Real.log (n : ℝ)) ^ 4) := by
    have ht1 : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 48 / (n : ℝ) ^ (1 / 4 : ℝ)) atTop (nhds 0) :=
      log_pow_div_rpow_tendsto_zero 48 (by norm_num)
    have ht_exp : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 97 *
        Real.exp (-c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log (n : ℝ)))) atTop (nhds 0) := by
      have h_sqrt : Tendsto (fun t : ℝ => t ^ 194 * Real.exp (-(c₁ * Real.sqrt (1 / 2 : ℝ)) * t))
          atTop (nhds 0) := by
        have hpos : 0 < c₁ * Real.sqrt (1 / 2 : ℝ) := by positivity
        have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 194).comp (tendsto_id.const_mul_atTop hpos)
        have heq : (fun t : ℝ => t ^ 194 * Real.exp (-(c₁ * Real.sqrt (1 / 2 : ℝ)) * t)) =
            (fun t : ℝ => (1 / (c₁ * Real.sqrt (1 / 2 : ℝ)) ^ 194) *
              (((c₁ * Real.sqrt (1 / 2 : ℝ)) * t) ^ 194 *
                Real.exp (-((c₁ * Real.sqrt (1 / 2 : ℝ)) * t)))) := by
          ext t; field_simp [hpos.ne']
        rw [heq]
        have hmul := this.const_mul (1 / (c₁ * Real.sqrt (1 / 2 : ℝ)) ^ 194)
        rw [mul_zero] at hmul
        exact hmul
      have hcomp := h_sqrt.comp (Real.tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
      refine hcomp.congr' ?_
      filter_upwards [(tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 0)] with n hln
      dsimp only [Function.comp_def] at hln ⊢
      have hsq : (Real.sqrt (Real.log (n : ℝ))) ^ 194 = (Real.log (n : ℝ)) ^ 97 := by
        rw [show (194 : ℕ) = 2 * 97 from rfl, pow_mul, Real.sq_sqrt hln]
      rw [hsq, Real.sqrt_mul (by norm_num)]
      ring_nf
    have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [Filter.eventually_ge_atTop 16, hlog_ge2,
      (ht1.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono (fun _ h => h.le),
      hlog_inf.eventually (eventually_ge_atTop (max (max X₁ 4) 10000)),
      (ht_exp.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)] with
      n hn hln ht1_sm hlog_big htexp_sm
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hln_10000 : 10000 ≤ Real.log (n : ℝ) := le_trans (le_max_right _ _) hlog_big
    have hln_X1 : max X₁ 4 ≤ Real.log (n : ℝ) := le_trans (le_max_left _ _) hlog_big
    have h48_ge : max X₁ 4 ≤ (Real.log (n : ℝ)) ^ 48 := by
      have h1 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 48 :=
        le_self_pow₀ (by linarith) (by norm_num : 48 ≠ 0)
      linarith
    have h48_ge8 : 8 ≤ (Real.log (n : ℝ)) ^ 48 := by
      have : (10000 : ℝ) ^ 48 ≤ (Real.log (n : ℝ)) ^ 48 := pow_le_pow_left₀ (by norm_num) hln_10000 48
      linarith
    have hfl_ge4 : 4 ≤ Nat.floor ((Real.log (n : ℝ)) ^ 48) := by
      rw [Nat.le_floor_iff (by positivity)]; push_cast; linarith
    have hfl_le : (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ≤ (Real.log (n : ℝ)) ^ 48 :=
      Nat.floor_le (by positivity)
    have h48_le_2fl : (Real.log (n : ℝ)) ^ 48 ≤ 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
      linarith [Nat.lt_floor_add_one ((Real.log (n : ℝ)) ^ 48)]
    have hfl5_ge1 : 1 ≤ Nat.floor ((Real.log (n : ℝ)) ^ 5) := by
      rw [Nat.le_floor_iff (by positivity)]
      have : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 := one_le_pow₀ (by linarith)
      exact_mod_cast this
    have hfl5_le : (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 :=
      Nat.floor_le (by positivity)
    have h5_le_2fl5 : (Real.log (n : ℝ)) ^ 5 ≤ 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) := by
      linarith [Nat.lt_floor_add_one ((Real.log (n : ℝ)) ^ 5)]
    have h_r1_le_rpow : (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ≤ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) := by
      have h1 := (div_le_iff₀ (by positivity)).mp ht1_sm
      linarith
    have h_sqrt_lt : Real.sqrt (n : ℝ) < (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
      have hn14 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
      have hsq_eq : Real.sqrt (n : ℝ) * ((n : ℝ) ^ (1 / 4 : ℝ)) < (n : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn_pos]
        have : (1 / 2 : ℝ) + (1 / 4 : ℝ) = (3 / 4 : ℝ) := by norm_num
        rw [this]
        calc (n : ℝ) ^ (3 / 4 : ℝ) < (n : ℝ) ^ (1 : ℝ) :=
              Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < n)) (by norm_num)
          _ = (n : ℝ) := Real.rpow_one _
      rw [lt_div_iff₀ (by exact_mod_cast (by omega : 0 < Nat.floor ((Real.log (n : ℝ)) ^ 48)))]
      nlinarith
    have h_13_sqrtN : (n : ℝ) ^ (1 / 3 : ℝ) ≤ (Nat.sqrt n : ℝ) := by
      have h1 : (n : ℝ) ^ (1 / 3 : ℝ) + 1 ≤ Real.sqrt (n : ℝ) := by
        have h16 : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 6 : ℝ) := by
          have hn64 : (64 : ℝ) ≤ (n : ℝ) := by
            have h64_le_exp : (64 : ℝ) ≤ Real.exp 10000 := by
              have : (10001 : ℝ) ≤ Real.exp 10000 := by linarith [Real.add_one_le_exp (10000 : ℝ)]
              linarith
            have hexp_le : Real.exp 10000 ≤ (n : ℝ) := by
              calc Real.exp 10000 ≤ Real.exp (Real.log (n : ℝ)) := Real.exp_le_exp.mpr hln_10000
                _ = (n : ℝ) := Real.exp_log hn_pos
            linarith
          rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 6)]
          rw [← Real.rpow_mul hn_pos.le]
          norm_num
          linarith
        have hsq_eq : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn_pos]
          congr 1; norm_num
        have hn13_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
          Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
        rw [hsq_eq]
        nlinarith
      have hsq_lt : Real.sqrt (n : ℝ) < (Nat.sqrt n : ℝ) + 1 := by
        rw [Real.sqrt_lt' (by positivity)]
        exact_mod_cast Nat.lt_succ_sqrt' n
      linarith
    have h_div_r1_12 : (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := by
      apply div_le_div_of_nonneg_left hn_pos.le (by positivity)
      have h12_le_48 : 2 * (Real.log (n : ℝ)) ^ 12 ≤ (Real.log (n : ℝ)) ^ 48 := by
        have hpow : (Real.log (n : ℝ)) ^ 12 * 2 ≤ (Real.log (n : ℝ)) ^ 12 * (Real.log (n : ℝ)) ^ 36 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := one_le_pow₀ (by linarith : (1 : ℝ) ≤ Real.log (n : ℝ)) (n := 35)
          have : (Real.log (n : ℝ)) ^ 36 = Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 35 := by ring
          nlinarith
        linarith [show (Real.log (n : ℝ)) ^ 48 = (Real.log (n : ℝ)) ^ 12 * (Real.log (n : ℝ)) ^ 36 from by ring]
      linarith
    have h_n34_ge : max X₁ 4 ≤ (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
      have h14_ge : max X₁ 4 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by linarith
      have h14_le_34 : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
      have h_n_div_ge : (n : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
        calc (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) := by
              rw [show (3 / 4 : ℝ) = 1 - 1 / 4 from by norm_num, Real.rpow_sub hn_pos, Real.rpow_one]
          _ ≤ (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
              apply div_le_div_of_nonneg_left hn_pos.le (by exact_mod_cast (by omega : 0 < Nat.floor ((Real.log (n : ℝ)) ^ 48)))
              have hn14 : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
              linarith
      linarith
    have h_log_div_ge : (1 / 2 : ℝ) * Real.log (n : ℝ) ≤
        Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)) := by
      have h_le_sqrt : (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        have h_14_12 : (n : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt (n : ℝ) := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
        linarith
      calc (1 / 2 : ℝ) * Real.log (n : ℝ) = Real.log (n : ℝ) - (1 / 2 : ℝ) * Real.log (n : ℝ) := by ring
        _ = Real.log (n : ℝ) - Real.log ((n : ℝ) ^ (1 / 2 : ℝ)) := by rw [Real.log_rpow hn_pos]
        _ ≤ Real.log (n : ℝ) - Real.log (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
            linarith [Real.log_le_log (by exact_mod_cast (by omega : 0 < Nat.floor ((Real.log (n : ℝ)) ^ 48))) h_le_sqrt]
        _ = Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)) :=
            (Real.log_div hn_pos.ne' (by exact_mod_cast (by omega : Nat.floor ((Real.log (n : ℝ)) ^ 48) ≠ 0))).symm
    have h_exp_last : (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ^ 2 *
        Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)))) *
          Real.log (n : ℝ) ≤ 1 := by
      have hexp_le : Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)))) ≤
          Real.exp (-c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log (n : ℝ))) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt h_log_div_ge) (by linarith))
      calc (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ^ 2 *
            Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)))) *
            Real.log (n : ℝ)
          ≤ ((Real.log (n : ℝ)) ^ 48) ^ 2 *
              Real.exp (-c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log (n : ℝ))) * Real.log (n : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact mul_le_mul (pow_le_pow_left₀ (by positivity) hfl_le 2) hexp_le (by positivity) (by positivity)
        _ = (Real.log (n : ℝ)) ^ 97 * Real.exp (-c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log (n : ℝ))) := by ring
        _ ≤ 1 := htexp_sm
    have h_R3 : Nat.floor (1 / (1 / 3 : ℝ)) = 3 := by norm_num
    have h_pow_48 : (2 : ℝ) ^ (-(Nat.floor (1 / (1 / 3 : ℝ)) : ℕ) : ℤ) *
        (Real.log (n : ℝ)) ^ (6 * Nat.floor (1 / (1 / 3 : ℝ)) + 30) ≤ (Real.log (n : ℝ)) ^ 48 / 2 := by
      rw [h_R3]; norm_num; positivity
    have h_2H1_12 : 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1 ≤ (Real.log (n : ℝ)) ^ 12 := by
      have : 2 * (Real.log (n : ℝ)) ^ 5 + 1 ≤ (Real.log (n : ℝ)) ^ 6 := by nlinarith
      have h6_12 : (Real.log (n : ℝ)) ^ 6 ≤ (Real.log (n : ℝ)) ^ 12 :=
        pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith
    have h_loglog_4 : (Real.log (2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1) + 1) *
        (Real.log (n : ℝ) / Real.log 2 + 2) ≤ (Real.log (n : ℝ)) ^ 4 := by
      have hle6 : 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1 ≤ (Real.log (n : ℝ)) ^ 6 := by nlinarith
      have hlog6 : Real.log (2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1) ≤ 6 * Real.log (Real.log (n : ℝ)) := by
        calc Real.log (2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1)
            ≤ Real.log ((Real.log (n : ℝ)) ^ 6) := Real.log_le_log (by positivity) hle6
          _ = 6 * Real.log (Real.log (n : ℝ)) := by rw [Real.log_pow]; norm_num
      have hsqrt_y : Real.log (Real.log (n : ℝ)) ≤ 2 * Real.sqrt (Real.log (n : ℝ)) := by
        have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith : 0 < Real.log (n : ℝ)))
        have h2 : Real.log (Real.log (n : ℝ)) = 2 * Real.log (Real.sqrt (Real.log (n : ℝ))) := by
          rw [Real.log_sqrt (by linarith)]; ring
        linarith
      have hsq_le_y : 12 * Real.sqrt (Real.log (n : ℝ)) + 1 ≤ Real.log (n : ℝ) := by
        have : 100 ≤ Real.sqrt (Real.log (n : ℝ)) := by
          rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
        nlinarith [Real.sq_sqrt (by linarith : 0 ≤ Real.log (n : ℝ))]
      have h_f1 : Real.log (2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1) + 1 ≤ Real.log (n : ℝ) := by linarith
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have h := Real.log_two_gt_d9
        linarith
      have h_f2 : Real.log (n : ℝ) / Real.log 2 + 2 ≤ 3 * Real.log (n : ℝ) := by
        have : Real.log (n : ℝ) / Real.log 2 ≤ 2 * Real.log (n : ℝ) := by
          rw [div_le_iff₀ hlog2_pos]; nlinarith
        linarith
      have : 3 * (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 4 := by nlinarith
      nlinarith
    exact ⟨h_sqrt_lt, h_13_sqrtN, h_div_r1_12, hfl_ge4, hfl5_ge1, h48_le_2fl, h5_le_2fl5,
      h_n34_ge, h_exp_last, h_pow_48, h_2H1_12, h_loglog_4⟩
  let M : ℝ := |C_ed| + (4 * |C₁| + 2) +
    (Cθ * 2 + (2 + 4 * C₁e * (1 + Real.log 2) + (2 + 2 * Cm + 36 * C₁e)))
  refine Asymptotics.IsBigO.of_bound M ?_
  filter_upwards [Filter.eventually_ge_atTop 16, hlog_ge2, h_main_conds, hExp, hC_ed] with
    n hn hln hconds hexp_n hed_n
  rcases hconds with ⟨hsqrt_lt, h13_sqrtN, hdiv_r1_12, hR1_ge4, hH_ge1, h48_le_2fl, h5_le_2fl5,
    hnX1, hexp_last, hpow48, h2H1_12, hloglog4⟩
  set R₁ := Nat.floor ((Real.log (n : ℝ)) ^ 48)
  set H := Nat.floor ((Real.log (n : ℝ)) ^ 5)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hR1_pos : (0 : ℝ) < (R₁ : ℝ) := by exact_mod_cast (by omega : 0 < R₁)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let S_all := (Finset.Icc 3 n).filter Nat.Prime
  let S_low := (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime
  let S_mid := S_all.filter (fun p : ℕ => Nat.sqrt n < p ∧ (p : ℝ) ≤ (n : ℝ) / (R₁ : ℝ))
  let S_hi := S_all.filter (fun p : ℕ => (n : ℝ) / (R₁ : ℝ) < (p : ℝ))
  have hS_part : S_all = S_low ∪ S_mid ∪ S_hi := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, S_all, S_low, S_mid, S_hi]
    constructor
    · rintro ⟨⟨hp3, hpn⟩, hp_pr⟩
      by_cases hsq : p ≤ Nat.sqrt n
      · left; left; exact ⟨⟨hp3, hsq⟩, hp_pr⟩
      · by_cases hhi : (p : ℝ) ≤ (n : ℝ) / (R₁ : ℝ)
        · left; right; exact ⟨⟨⟨hp3, hpn⟩, hp_pr⟩, by omega, hhi⟩
        · right; push Not at hhi; exact ⟨⟨⟨hp3, hpn⟩, hp_pr⟩, hhi⟩
    · rintro ((⟨⟨hp3, hsq⟩, hp_pr⟩ | ⟨⟨⟨hp3, hpn⟩, hp_pr⟩, _⟩) | ⟨⟨⟨hp3, hpn⟩, hp_pr⟩, _⟩)
      · exact ⟨⟨hp3, le_trans hsq (Nat.sqrt_le_self n)⟩, hp_pr⟩
      · exact ⟨⟨hp3, hpn⟩, hp_pr⟩
      · exact ⟨⟨hp3, hpn⟩, hp_pr⟩
  have hdisj_lm : Disjoint S_low S_mid := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [S_low, S_mid, Finset.mem_filter, Finset.mem_Icc] at h1 h2
    omega
  have hdisj_lm_h : Disjoint (S_low ∪ S_mid) S_hi := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [Finset.mem_union, S_low, S_mid, S_hi, Finset.mem_filter, Finset.mem_Icc] at h1 h2
    rcases h1 with h1 | h1
    · have hp_le_sq : (p : ℝ) ≤ Real.sqrt (n : ℝ) := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        exact_mod_cast le_trans (Nat.pow_le_pow_left h1.1.2 2) (Nat.sqrt_le' n)
      linarith [h2.2, hsqrt_lt]
    · linarith [h1.2.2, h2.2]
  let f_term : ℕ → ℝ := fun p =>
    (-1 : ℝ) ^ (padicValNat p (Nat.factorial n)) * (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
  have hDelta_split : Delta_parity n =
      (∑ p ∈ S_low, f_term p) + (∑ p ∈ S_mid, f_term p) + (∑ p ∈ S_hi, f_term p) := by
    rw [Delta_parity_eq_sum]
    change ∑ p ∈ S_all, f_term p = _
    rw [hS_part, Finset.sum_union hdisj_lm_h, Finset.sum_union hdisj_lm]
  have hlow_eq : ∑ p ∈ S_low, f_term p = -(n : ℝ) * Sigma_star_parity n + E_digit n :=
    exact_legendre_base_p_reduction n
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hed_n
  have hed_bound : |E_digit n| ≤ |C_ed| * ((n : ℝ) / Real.log (n : ℝ)) := by
    have h1 : Real.sqrt (n : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) := by
      rw [le_div_iff₀ hlogn_pos]
      have hln_le_sqrt : Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
        have hx14 : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
        have hlog14 : Real.log ((n : ℝ) ^ (1 / 4 : ℝ)) ≤ (n : ℝ) ^ (1 / 4 : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos hx14
        have hlog_eq4 : Real.log (n : ℝ) = 4 * Real.log ((n : ℝ) ^ (1 / 4 : ℝ)) := by
          rw [Real.log_rpow hn_pos]; ring
        have hsq14 : Real.sqrt (n : ℝ) = ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]
          congr 1; norm_num
        nlinarith [sq_nonneg ((n : ℝ) ^ (1 / 4 : ℝ) - 2)]
      calc Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
            mul_le_mul_of_nonneg_left hln_le_sqrt (Real.sqrt_nonneg _)
        _ = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
    calc |E_digit n| ≤ C_ed * Real.sqrt (n : ℝ) := hed_n
      _ ≤ |C_ed| * Real.sqrt (n : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
      _ ≤ |C_ed| * ((n : ℝ) / Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hhi_bound : |∑ p ∈ S_hi, f_term p - (Real.log 2 - 1) * (n : ℝ)| ≤
      (4 * |C₁| + 2) * ((n : ℝ) / Real.log (n : ℝ)) := by
    let Hr : ℕ → Finset ℕ := fun r =>
      ((Finset.Icc 2 (Nat.floor ((n : ℝ) / (r : ℝ)))).filter Nat.Prime).filter
        (fun p : ℕ => (n : ℝ) / ((r : ℝ) + 1) < (p : ℝ))
    have hS_hi_part : S_hi = (Finset.Icc 1 (R₁ - 1)).biUnion Hr := by
      ext p
      simp only [S_hi, S_all, Hr, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hp3, hpn⟩, hp_pr⟩, hp_gt⟩
        have hn_lt_psq : n < p ^ 2 := by
          have h1 : Real.sqrt (n : ℝ) < (p : ℝ) := lt_trans hsqrt_lt hp_gt
          rw [Real.sqrt_lt' (by exact_mod_cast hp_pr.pos)] at h1
          exact_mod_cast h1
        have hv : padicValNat p (Nat.factorial n) = n / p :=
          padicValNat_factorial_eq_div_of_lt_sq hp_pr hn_lt_psq
        have hdiv_ge : 1 ≤ n / p := Nat.div_pos hpn hp_pr.pos
        have hdiv_lt : n / p < R₁ := by
          rw [Nat.div_lt_iff_lt_mul hp_pr.pos]
          rw [div_lt_iff₀ hR1_pos] at hp_gt
          exact_mod_cast hp_gt
        let r := n / p
        refine ⟨r, ⟨hdiv_ge, by omega⟩, ⟨⟨hp_pr.two_le, ?_⟩, hp_pr⟩, ?_⟩
        · rw [Nat.le_floor_iff (by positivity), le_div_iff₀ (by exact_mod_cast hdiv_ge)]
          exact_mod_cast Nat.div_mul_le_self n p
        · rw [div_lt_iff₀ (by positivity)]
          have : n < (r + 1) * p := (Nat.div_lt_iff_lt_mul hp_pr.pos).mp (by omega : n / p < r + 1)
          have hR : (n : ℝ) < ((r + 1 : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast this
          push_cast at hR; linarith
      · rintro ⟨r, ⟨hr1, hrR⟩, ⟨⟨hp2, hp_hi⟩, hp_pr⟩, hp_lo⟩
        have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
        have hp_gt_r1 : (n : ℝ) / (R₁ : ℝ) < (p : ℝ) := by
          calc (n : ℝ) / (R₁ : ℝ) ≤ (n : ℝ) / ((r : ℝ) + 1) := by
                apply div_le_div_of_nonneg_left hn_pos.le (by positivity)
                exact_mod_cast (by omega : r + 1 ≤ R₁)
            _ < (p : ℝ) := hp_lo
        have hn_lt_psq : n < p ^ 2 := by
          have h1 : Real.sqrt (n : ℝ) < (p : ℝ) := lt_trans hsqrt_lt hp_gt_r1
          rw [Real.sqrt_lt' (by exact_mod_cast hp_pr.pos)] at h1
          exact_mod_cast h1
        have hp3 : 3 ≤ p := by
          have : (3 : ℝ) < Real.sqrt (n : ℝ) := by
            rw [Real.lt_sqrt (by norm_num)]; exact_mod_cast (by omega : 9 < n)
          have : (3 : ℝ) < (p : ℝ) := lt_trans this (lt_trans hsqrt_lt hp_gt_r1)
          exact_mod_cast this.le
        have hpn : p ≤ n := by
          rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hr_pos] at hp_hi
          have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
          exact_mod_cast (by nlinarith : (p : ℝ) ≤ (n : ℝ))
        exact ⟨⟨⟨hp3, hpn⟩, hp_pr⟩, hp_gt_r1⟩
    have hdisj_Hr : (Finset.Icc 1 (R₁ - 1) : Set ℕ).PairwiseDisjoint Hr := by
      intro r₁ hr₁ r₂ hr₂ hne
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_coe, Finset.mem_Icc] at hr₁ hr₂
      simp only [Hr, Finset.mem_filter, Finset.mem_Icc] at hp1 hp2
      have hr₁_pos : (0 : ℝ) < (r₁ : ℝ) := by exact_mod_cast hr₁.1
      have hr₂_pos : (0 : ℝ) < (r₂ : ℝ) := by exact_mod_cast hr₂.1
      have hhi1 := hp1.1.1.2
      have hhi2 := hp2.1.1.2
      rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hr₁_pos] at hhi1
      rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hr₂_pos] at hhi2
      have hlo1 := hp1.2; have hlo2 := hp2.2
      rw [div_lt_iff₀ (by positivity)] at hlo1 hlo2
      have h12 : (p : ℝ) * (r₁ : ℝ) < ((r₂ : ℝ) + 1) * (p : ℝ) := lt_of_le_of_lt hhi1 hlo2
      have h21 : (p : ℝ) * (r₂ : ℝ) < ((r₁ : ℝ) + 1) * (p : ℝ) := lt_of_le_of_lt hhi2 hlo1
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp1.1.2.pos
      have : r₁ < r₂ + 1 := by exact_mod_cast (by nlinarith : (r₁ : ℝ) < (r₂ : ℝ) + 1)
      have : r₂ < r₁ + 1 := by exact_mod_cast (by nlinarith : (r₂ : ℝ) < (r₁ : ℝ) + 1)
      omega
    have hr_val : ∀ r ∈ Finset.Icc 1 (R₁ - 1), ∀ p ∈ Hr r,
        f_term p = (-1 : ℝ) ^ r * (r : ℝ) * Real.log (p : ℝ) := by
      intro r hr p hp
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrR : r ≤ R₁ - 1 := (Finset.mem_Icc.mp hr).2
      simp only [Hr, Finset.mem_filter, Finset.mem_Icc] at hp
      have hp_pr : p.Prime := hp.1.2
      have hp_gt : (n : ℝ) / (R₁ : ℝ) < (p : ℝ) := by
        calc (n : ℝ) / (R₁ : ℝ) ≤ (n : ℝ) / ((r : ℝ) + 1) :=
              div_le_div_of_nonneg_left hn_pos.le (by positivity) (by exact_mod_cast (by omega : r + 1 ≤ R₁))
          _ < (p : ℝ) := hp.2
      have hn_lt_psq : n < p ^ 2 := by
        have h1 : Real.sqrt (n : ℝ) < (p : ℝ) := lt_trans hsqrt_lt hp_gt
        rw [Real.sqrt_lt' (by exact_mod_cast hp_pr.pos)] at h1
        exact_mod_cast h1
      have hv : padicValNat p (Nat.factorial n) = n / p :=
        padicValNat_factorial_eq_div_of_lt_sq hp_pr hn_lt_psq
      have hdiv_ge : r ≤ n / p := by
        rw [Nat.le_div_iff_mul_le hp_pr.pos]
        have := hp.1.1.2
        rw [Nat.le_floor_iff (by positivity), le_div_iff₀ (by exact_mod_cast hr1)] at this
        exact_mod_cast (by linarith : ((r * p : ℕ) : ℝ) ≤ (n : ℝ))
      have hdiv_lt : n / p < r + 1 := by
        rw [Nat.div_lt_iff_lt_mul hp_pr.pos]
        have := hp.2
        rw [div_lt_iff₀ (by positivity)] at this
        exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((p * (r + 1) : ℕ) : ℝ))
      have hvr : padicValNat p (Nat.factorial n) = r := by omega
      simp only [f_term, hvr]
    have hHr_sum : ∀ r ∈ Finset.Icc 1 (R₁ - 1),
        ∑ p ∈ Hr r, f_term p =
          (-1 : ℝ) ^ r * (r : ℝ) * (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) := by
      intro r hr
      rw [Finset.sum_congr rfl (hr_val r hr), ← Finset.mul_sum]
      congr 1
      have hsub : (Finset.Icc 2 (Nat.floor ((n : ℝ) / ((r : ℝ) + 1)))).filter Nat.Prime ⊆
          (Finset.Icc 2 (Nat.floor ((n : ℝ) / (r : ℝ)))).filter Nat.Prime := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
        exact ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_mono (div_le_div_of_nonneg_left hn_pos.le hr_pos (by linarith)))⟩, hp.2⟩
      have hsdiff : Hr r = (Finset.Icc 2 (Nat.floor ((n : ℝ) / (r : ℝ)))).filter Nat.Prime \
          (Finset.Icc 2 (Nat.floor ((n : ℝ) / ((r : ℝ) + 1)))).filter Nat.Prime := by
        ext p; simp only [Hr, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; refine ⟨⟨h1, h2⟩, fun ⟨h4, _⟩ => ?_⟩
          rw [Nat.le_floor_iff (by positivity)] at h4; linarith
        · rintro ⟨⟨h1, h2⟩, hnot⟩; refine ⟨⟨h1, h2⟩, ?_⟩
          by_contra hle; push Not at hle; apply hnot
          exact ⟨⟨h1.1, (Nat.le_floor_iff (by positivity)).mpr hle⟩, h2⟩
      rw [hsdiff]
      unfold thetaPrime
      have hs := Finset.sum_sdiff hsub (f := fun p => Real.log (p : ℝ))
      linarith
    rw [hS_hi_part, Finset.sum_biUnion hdisj_Hr, Finset.sum_congr rfl hHr_sum]
    have h_theta_err : ∑ r ∈ Finset.Icc 1 (R₁ - 1),
        |(-1 : ℝ) ^ r * (r : ℝ) * (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
          (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ)| ≤
        2 * |C₁| * ((n : ℝ) / Real.log (n : ℝ)) := by
      have hr_each : ∀ r ∈ Finset.Icc 1 (R₁ - 1),
          |(-1 : ℝ) ^ r * (r : ℝ) * (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
            (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ)| ≤
          2 * |C₁| * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) := by
        intro r hr
        have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        have hrR : r ≤ R₁ - 1 := (Finset.mem_Icc.mp hr).2
        have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
        have h_ge_R1 : (n : ℝ) / (R₁ : ℝ) ≤ (n : ℝ) / ((r : ℝ) + 1) :=
          div_le_div_of_nonneg_left hn_pos.le (by positivity) (by exact_mod_cast (by omega : r + 1 ≤ R₁))
        have h_ge_r : (n : ℝ) / ((r : ℝ) + 1) ≤ (n : ℝ) / (r : ℝ) :=
          div_le_div_of_nonneg_left hn_pos.le hr_pos (by linarith)
        have hb1 := hX₁ ((n : ℝ) / (r : ℝ)) (le_trans (le_max_left _ _) (le_trans hnX1 (le_trans h_ge_R1 h_ge_r)))
        have hb2 := hX₁ ((n : ℝ) / ((r : ℝ) + 1)) (le_trans (le_max_left _ _) (le_trans hnX1 h_ge_R1))
        rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)] at hb1 hb2
        have hexp1 : Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (r : ℝ)))) ≤
            Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) := by
          apply Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt _) (by linarith))
          exact Real.log_le_log (by positivity) (le_trans h_ge_R1 h_ge_r)
        have hexp2 : Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / ((r : ℝ) + 1)))) ≤
            Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) := by
          apply Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt _) (by linarith))
          exact Real.log_le_log (by positivity) h_ge_R1
        have hid : (-1 : ℝ) ^ r * (r : ℝ) * (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
            (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ) =
            (-1 : ℝ) ^ r * (r : ℝ) *
              ((thetaPrime ((n : ℝ) / (r : ℝ)) - (n : ℝ) / (r : ℝ)) -
                (thetaPrime ((n : ℝ) / ((r : ℝ) + 1)) - (n : ℝ) / ((r : ℝ) + 1))) := by
          field_simp [hr_pos.ne', by positivity : (r : ℝ) + 1 ≠ 0]; ring
        rw [hid, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hr_pos]
        have htri := abs_sub
          (thetaPrime ((n : ℝ) / (r : ℝ)) - (n : ℝ) / (r : ℝ))
          (thetaPrime ((n : ℝ) / ((r : ℝ) + 1)) - (n : ℝ) / ((r : ℝ) + 1))
        have he1 : |thetaPrime ((n : ℝ) / (r : ℝ)) - (n : ℝ) / (r : ℝ)| ≤
            |C₁| * ((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) :=
          calc |thetaPrime ((n : ℝ) / (r : ℝ)) - (n : ℝ) / (r : ℝ)|
              ≤ C₁ * (((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (r : ℝ))))) := hb1
            _ ≤ |C₁| * (((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ))))) :=
                mul_le_mul (le_abs_self _) (mul_le_mul_of_nonneg_left hexp1 (by positivity)) (by positivity) (abs_nonneg _)
            _ = |C₁| * ((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) := by ring
        have he2 : |thetaPrime ((n : ℝ) / ((r : ℝ) + 1)) - (n : ℝ) / ((r : ℝ) + 1)| ≤
            |C₁| * ((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) :=
          calc |thetaPrime ((n : ℝ) / ((r : ℝ) + 1)) - (n : ℝ) / ((r : ℝ) + 1)|
              ≤ C₁ * (((n : ℝ) / ((r : ℝ) + 1)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / ((r : ℝ) + 1))))) := hb2
            _ ≤ |C₁| * (((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ))))) :=
                mul_le_mul (le_abs_self _) (mul_le_mul h_ge_r hexp2 (by positivity) (by positivity)) (by positivity) (abs_nonneg _)
            _ = |C₁| * ((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) := by ring
        calc (r : ℝ) * |(thetaPrime ((n : ℝ) / (r : ℝ)) - (n : ℝ) / (r : ℝ)) -
              (thetaPrime ((n : ℝ) / ((r : ℝ) + 1)) - (n : ℝ) / ((r : ℝ) + 1))|
            ≤ (r : ℝ) * (2 * |C₁| * ((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ))))) :=
              mul_le_mul_of_nonneg_left (by linarith) hr_pos.le
          _ = 2 * |C₁| * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) := by
              field_simp [hr_pos.ne']
      calc ∑ r ∈ Finset.Icc 1 (R₁ - 1),
              |(-1 : ℝ) ^ r * (r : ℝ) * (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
                (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ)|
          ≤ ∑ _r ∈ Finset.Icc 1 (R₁ - 1),
              2 * |C₁| * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) :=
            Finset.sum_le_sum hr_each
        _ = ((R₁ - 1 : ℕ) : ℝ) * (2 * |C₁| * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ))))) := by
            simp [Finset.sum_const, Nat.card_Icc]; ring_nf
        _ ≤ 2 * |C₁| * ((n : ℝ) / Real.log (n : ℝ)) *
              ((R₁ : ℝ) ^ 2 * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) * Real.log (n : ℝ)) := by
            have hR1_ge1 : (1 : ℝ) ≤ (R₁ : ℝ) := by exact_mod_cast (by omega : 1 ≤ R₁)
            have hR1_sub : ((R₁ - 1 : ℕ) : ℝ) ≤ (R₁ : ℝ) ^ 2 := by
              have : ((R₁ - 1 : ℕ) : ℝ) ≤ (R₁ : ℝ) := by exact_mod_cast (by omega : R₁ - 1 ≤ R₁)
              nlinarith
            have h_eq : 2 * |C₁| * ((n : ℝ) / Real.log (n : ℝ)) *
                  ((R₁ : ℝ) ^ 2 * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) * Real.log (n : ℝ)) =
                (R₁ : ℝ) ^ 2 * (2 * |C₁| * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ))))) := by
              field_simp [hlogn_pos.ne']
            rw [h_eq]
            exact mul_le_mul_of_nonneg_right hR1_sub (by positivity)
        _ ≤ 2 * |C₁| * ((n : ℝ) / Real.log (n : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hexp_last (by positivity)
        _ = 2 * |C₁| * ((n : ℝ) / Real.log (n : ℝ)) := by ring
    have h_alt_err : |∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ) -
          (Real.log 2 - 1) * (n : ℝ)| ≤ 2 * ((n : ℝ) / Real.log (n : ℝ)) := by
      rw [← Finset.sum_mul, ← sub_mul, abs_mul, abs_of_pos hn_pos]
      have h_b := alt_harmonic_shifted_bound (by omega : 3 ≤ R₁)
      have h3_le : 3 / (R₁ : ℝ) ≤ 2 / Real.log (n : ℝ) := by
        rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < R₁)) hlogn_pos]
        by_cases hlog2 : Real.log (n : ℝ) ≤ 2
        · have hR1_ge3 : (3 : ℝ) ≤ (R₁ : ℝ) := by exact_mod_cast (by omega : 3 ≤ R₁)
          linarith
        · push_neg at hlog2
          have hpow47 : (4 : ℝ) ≤ (Real.log (n : ℝ)) ^ 47 := by
            have : (2 : ℝ) ^ 47 ≤ (Real.log (n : ℝ)) ^ 47 :=
              pow_le_pow_left₀ (by norm_num) hlog2.le 47
            linarith [show (4 : ℝ) ≤ (2 : ℝ) ^ 47 by norm_num]
          have hpow48 : 4 * Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 48 := by
            rw [show (Real.log (n : ℝ)) ^ 48 = Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 47 from by ring]
            nlinarith
          have hR1_lb : (Real.log (n : ℝ)) ^ 48 - 1 < (R₁ : ℝ) :=
            Nat.sub_one_lt_floor ((Real.log (n : ℝ)) ^ 48)
          linarith
      calc |∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) - (Real.log 2 - 1)| * (n : ℝ)
          ≤ (3 / (R₁ : ℝ)) * (n : ℝ) := mul_le_mul_of_nonneg_right h_b hn_pos.le
        _ ≤ (2 / Real.log (n : ℝ)) * (n : ℝ) := mul_le_mul_of_nonneg_right h3_le hn_pos.le
        _ = 2 * ((n : ℝ) / Real.log (n : ℝ)) := by ring
    have htri := abs_add_le
      (∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r * (r : ℝ) *
          (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
        ∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ))
      (∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ) - (Real.log 2 - 1) * (n : ℝ))
    have hsum_tri : |∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r * (r : ℝ) *
          (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
        ∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ)| ≤
        2 * |C₁| * ((n : ℝ) / Real.log (n : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) h_theta_err
    linarith [show (∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r * (r : ℝ) *
          (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) - (Real.log 2 - 1) * (n : ℝ)) =
        (∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r * (r : ℝ) *
          (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
          ∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ)) +
        (∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ) - (Real.log 2 - 1) * (n : ℝ)) from by ring]
  have hmid_bound : |∑ p ∈ S_mid, f_term p| ≤
      (Cθ * 2 + (2 + 4 * C₁e * (1 + Real.log 2) + (2 + 2 * Cm + 36 * C₁e))) * ((n : ℝ) / Real.log (n : ℝ)) := by
    have hp_val_mid : ∀ p ∈ S_mid, padicValNat p (Nat.factorial n) = n / p := by
      intro p hp
      simp only [S_mid, S_all, Finset.mem_filter, Finset.mem_Icc] at hp
      have hn_lt_psq : n < p ^ 2 := by
        have h1 : Nat.sqrt n + 1 ≤ p := hp.2.1
        calc n < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
          _ ≤ p ^ 2 := Nat.pow_le_pow_left h1 2
      exact padicValNat_factorial_eq_div_of_lt_sq hp.1.2 hn_lt_psq
    have hsplit_mid : ∑ p ∈ S_mid, f_term p =
        (∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ)) * Real.log (p : ℝ)) -
        (∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      simp only [f_term, hp_val_mid p hp]
      ring
    have hfrac_bound : |∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)| ≤
        Cθ * 2 * ((n : ℝ) / Real.log (n : ℝ)) := by
      have hsub : S_mid ⊆ (Finset.Icc 2 (Nat.floor ((n : ℝ) / (R₁ : ℝ)))).filter Nat.Prime := by
        intro p hp
        simp only [S_mid, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        exact ⟨⟨hp.1.2.two_le, (Nat.le_floor_iff (by positivity)).mpr hp.2.2⟩, hp.1.2⟩
      calc |∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)|
          ≤ ∑ p ∈ S_mid, |(-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ S_mid, Real.log (p : ℝ) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            simp only [S_mid, S_all, Finset.mem_filter, Finset.mem_Icc] at hp
            have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.1.2.pos
            have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
            have hfl_ge : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / (p : ℝ) := by
              rw [le_div_iff₀ hp_pos]; exact_mod_cast Nat.div_mul_le_self n p
            have hfl_lt : (n : ℝ) / (p : ℝ) < ((n / p : ℕ) : ℝ) + 1 := by
              rw [div_lt_iff₀ hp_pos]
              exact_mod_cast (by push_cast; linarith [Nat.lt_div_mul_add hp.1.2.pos (a := n)] :
                (n : ℝ) < (((n / p + 1 : ℕ) : ℝ) * (p : ℝ)))
            rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
              abs_of_nonneg (by linarith), abs_of_nonneg hlogp]
            nlinarith
        _ ≤ thetaPrime ((n : ℝ) / (R₁ : ℝ)) := by
            unfold thetaPrime
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_)
            have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
            exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
        _ ≤ Cθ * ((n : ℝ) / (R₁ : ℝ)) := by
            apply hCθ
            rw [le_div_iff₀ hR1_pos, one_mul]
            have : (Nat.sqrt n : ℝ) < (n : ℝ) / (R₁ : ℝ) := by
              have : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
                rw [Real.le_sqrt (by positivity) (by positivity)]
                exact_mod_cast Nat.sqrt_le' n
              linarith [hsqrt_lt]
            rw [lt_div_iff₀ hR1_pos] at this
            linarith
        _ ≤ Cθ * (2 * ((n : ℝ) / Real.log (n : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ hCθ_pos.le
            have h1 : (n : ℝ) / (R₁ : ℝ) ≤ 2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 48 := by
              rw [div_le_div_iff₀ hR1_pos (by positivity)]
              nlinarith [h48_le_2fl]
            have h2 : (Real.log (n : ℝ)) ≤ (Real.log (n : ℝ)) ^ 48 :=
              le_self_pow₀ (by linarith) (by norm_num : 48 ≠ 0)
            have h3 : (n : ℝ) / (Real.log (n : ℝ)) ^ 48 ≤ (n : ℝ) / Real.log (n : ℝ) :=
              div_le_div_of_nonneg_left hn_pos.le hlogn_pos h2
            linarith
        _ = Cθ * 2 * ((n : ℝ) / Real.log (n : ℝ)) := by ring
    have hmain_mid : |∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ)) * Real.log (p : ℝ)| ≤
        (2 + 4 * C₁e * (1 + Real.log 2) + (2 + 2 * Cm + 36 * C₁e)) * ((n : ℝ) / Real.log (n : ℝ)) := by
      rcases eq_or_ne S_mid ∅ with h_empty | h_ne
      · rw [h_empty, Finset.sum_empty, abs_zero]; positivity
      · have hA_ge1 : (1 : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast (by omega : 1 ≤ Nat.sqrt n)
        have hAB : (Nat.sqrt n : ℝ) ≤ (n : ℝ) / (R₁ : ℝ) := by
          obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr h_ne
          simp only [S_mid, Finset.mem_filter] at hp0
          have : ((Nat.sqrt n : ℝ)) < (p0 : ℝ) := by exact_mod_cast hp0.2.1
          linarith [hp0.2.2]
        have hI_mem : ∀ p ∈ S_mid, (Nat.sqrt n : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) / (R₁ : ℝ) := by
          intro p hp
          simp only [S_mid, Finset.mem_filter] at hp
          exact ⟨by exact_mod_cast hp.2.1, hp.2.2⟩
        obtain ⟨hpart_mid, hdisj_mid⟩ := dyadic_partition_finset hA_ge1 hAB S_mid hI_mem
        obtain ⟨c_tilde, b_tilde, h_supp, h_ctilde_b, h_btilde0, h_btilde_b, h_vaaler_pw, h_L1⟩ :=
          vaaler_parity_approx H hH_ge1
        have hfloor_eq : ∀ p ∈ S_mid, (-1 : ℝ) ^ (n / p) = (-1 : ℝ) ^ (Int.floor ((n : ℝ) / (p : ℝ))) := by
          intro p hp
          simp only [S_mid, S_all, Finset.mem_filter] at hp
          have hfl : Int.floor ((n : ℝ) / (p : ℝ)) = ((n / p : ℕ) : ℤ) := by
            rw [Int.floor_eq_iff]
            have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.1.2.pos
            constructor
            · rw [Int.cast_natCast, le_div_iff₀ hp_pos]; exact_mod_cast Nat.div_mul_le_self n p
            · rw [Int.cast_natCast, div_lt_iff₀ hp_pos]
              exact_mod_cast (by push_cast; linarith [Nat.lt_div_mul_add hp.1.2.pos (a := n)] :
                (n : ℝ) < (((n / p + 1 : ℕ) : ℝ) * (p : ℝ)))
          rw [hfl, zpow_natCast]
        let mainSum : ℂ := ∑ p ∈ S_mid,
          (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
            ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
              c_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)
        have h_diff_bound :
            |∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ)) * Real.log (p : ℝ)| ≤
            ‖mainSum‖ + ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) *
              (b_tilde 0 + ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re := by
          have h_re : (∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ)) * Real.log (p : ℝ)) =
              (mainSum + ∑ p ∈ S_mid, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
                ((((-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) : ℂ) -
                  ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
                    c_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2))).re := by
            rw [Complex.add_re, Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun p hp => ?_)
            rw [← mul_add, add_sub_cancel, hfloor_eq p hp]
            norm_cast
          rw [h_re]
          calc |(mainSum + _).re| ≤ ‖mainSum + _‖ := Complex.abs_re_le_norm _
            _ ≤ ‖mainSum‖ + ‖∑ p ∈ S_mid, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) * _‖ := norm_add_le _ _
            _ ≤ ‖mainSum‖ + ∑ p ∈ S_mid, ‖(((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) * _‖ :=
                add_le_add le_rfl (norm_sum_le _ _)
            _ ≤ ‖mainSum‖ + ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) * _ := by
                apply add_le_add le_rfl
                refine Finset.sum_le_sum (fun p hp => ?_)
                simp only [S_mid, S_all, Finset.mem_filter] at hp
                have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp.1.2.pos
                have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
                have hcoeff_nn : 0 ≤ (n : ℝ) / (p : ℝ) * Real.log (p : ℝ) := by positivity
                rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcoeff_nn]
                apply mul_le_mul_of_nonneg_left _ hcoeff_nn
                have hpw := (h_vaaler_pw ((n : ℝ) / (p : ℝ))).2
                have hsplit0 : ∑ h ∈ Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1),
                    b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2) =
                    b_tilde 0 + ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                      b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2) := by
                  have h0_mem : (0 : ℤ) ∈ Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1) := by
                    simp only [Finset.mem_Icc]; omega
                  rw [← Finset.add_sum_erase _ _ h0_mem]
                  congr 1
                  · simp [eExp]
                  · congr 1; ext h; simp [Finset.mem_erase, Finset.mem_filter]; tauto
                rwa [hsplit0] at hpw
        have h_block_exp : ∀ (k : ℕ) (hk : k ∈ dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ)))
            (h : ℤ) (hh0 : h ≠ 0) (hh_le : |h| ≤ 2 * (H : ℤ) + 1),
            ‖∑ p ∈ S_mid.filter (fun p : ℕ => (Nat.sqrt n : ℝ) * (2 : ℝ) ^ k < (p : ℝ) ∧
                (p : ℝ) ≤ 2 * ((Nat.sqrt n : ℝ) * (2 : ℝ) ^ k)),
              (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)‖ ≤
            C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ) := by
          intro k hk h hh0 hh_le
          let P := (Nat.sqrt n : ℝ) * (2 : ℝ) ^ k
          let Ik := S_mid.filter (fun p : ℕ => P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P)
          have hP_ge_sqrt : (Nat.sqrt n : ℝ) ≤ P :=
            le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
          have hP_lo : (n : ℝ) ^ (1 / 3 : ℝ) ≤ P := le_trans h13_sqrtN hP_ge_sqrt
          have hP_lt_B : P < (n : ℝ) / (R₁ : ℝ) := (Finset.mem_filter.mp hk).2
          have hP_hi : P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := le_trans hP_lt_B.le hdiv_r1_12
          have hIk_pr : ∀ p ∈ Ik, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P := by
            intro p hp
            simp only [Ik, Finset.mem_filter, S_mid, S_all] at hp
            exact ⟨hp.1.1.2, hp.2⟩
          have hexp_app := hexp_n P Ik {1} (fun _ => h) (fun t => (n : ℝ) / t) ((n : ℝ) / P)
            ⟨1, Finset.mem_singleton_self _, hh0⟩
            hP_lo hP_hi hIk_pr (fun r hr => by rw [Finset.mem_singleton.mp hr]; omega)
            (fun r hr => by
              rw [Finset.mem_singleton.mp hr]
              have h5_eq : Nat.floor (1 / (1 / 3 : ℝ)) + 2 = 5 := by norm_num
              rw [h5_eq]
              exact hh_le)
            (fun r hr => by
              rw [Finset.mem_singleton.mp hr, pow_one]
              have h1 : (R₁ : ℝ) ≤ (n : ℝ) / P := (le_div_iff₀ (by positivity)).mpr (by
                rw [mul_comm, ← le_div_iff₀ hR1_pos]; exact hP_lt_B.le)
              calc (2 : ℝ) ^ (-(Nat.floor (1 / (1 / 3 : ℝ)) : ℕ) : ℤ) *
                    (Real.log (n : ℝ)) ^ (6 * Nat.floor (1 / (1 / 3 : ℝ)) + 30)
                  ≤ (Real.log (n : ℝ)) ^ 48 / 2 := hpow48
                _ ≤ (R₁ : ℝ) := by linarith
                _ ≤ (n : ℝ) / P := h1)
            (fun t ht => by
              rw [abs_of_nonneg (div_nonneg hn_pos.le (by linarith [ht.1, hP_lo, hn_pos]))]
              exact div_le_div_of_nonneg_left hn_pos.le (by positivity) ht.1)
            (by positivity)
          dsimp only at hexp_app
          have h_rhs : C₁e * ((n : ℝ) / P) * P * (Real.log (n : ℝ)) ^ (-((Nat.floor (1 / (1 / 3 : ℝ)) : ℝ) + 2)) =
              C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ) := by
            have hP_pos : P ≠ 0 := by positivity
            have hR3 : (Nat.floor (1 / (1 / 3 : ℝ)) : ℝ) + 2 = 5 := by norm_num
            rw [hR3]
            field_simp [hP_pos]
          rw [← h_rhs]
          have h_sum_eq : ∑ p ∈ Ik, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2) =
              ∑ p ∈ Ik, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
                eExp (∑ r ∈ ({1} : Finset ℕ), (h : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ r)) := by
            refine Finset.sum_congr rfl (fun p _ => ?_)
            congr 2; simp [Finset.sum_singleton]; ring
          rw [h_sum_eq]
          exact hexp_app.1.2
        have hdy_card_le : ((dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ))).card : ℝ) ≤
            Real.log (n : ℝ) / Real.log 2 + 2 := by
          calc ((dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ))).card : ℝ)
              ≤ Real.log (((n : ℝ) / (R₁ : ℝ)) / (Nat.sqrt n : ℝ)) / Real.log 2 + 2 :=
                dyadicBlocks_card_le hA_ge1 hAB
            _ ≤ Real.log (n : ℝ) / Real.log 2 + 2 := by
                apply add_le_add_right
                apply div_le_div_of_nonneg_right _ hlog2_pos.le
                apply Real.log_le_log (by positivity)
                rw [div_le_iff₀ (by positivity)]
                calc (n : ℝ) / (R₁ : ℝ) ≤ (n : ℝ) / 1 :=
                      div_le_div_of_nonneg_left hn_pos.le (by norm_num) (by exact_mod_cast (by omega : 1 ≤ R₁))
                  _ ≤ (n : ℝ) * (Nat.sqrt n : ℝ) := by rw [div_one]; exact le_mul_of_one_le_right hn_pos.le hA_ge1
        have hmain_le : ‖mainSum‖ ≤ (2 + 4 * C₁e * (1 + Real.log 2)) * ((n : ℝ) / Real.log (n : ℝ)) := by
          let oddH := (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h)
          have h_swap : mainSum = ∑ h ∈ oddH, c_tilde h * ∑ k ∈ dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ)),
              ∑ p ∈ S_mid.filter (fun p : ℕ => (Nat.sqrt n : ℝ) * (2 : ℝ) ^ k < (p : ℝ) ∧
                  (p : ℝ) ≤ 2 * ((Nat.sqrt n : ℝ) * (2 : ℝ) ^ k)),
                (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2) := by
            unfold mainSum
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun h _ => ?_)
            rw [← Finset.mul_sum]
            congr 1
            conv_lhs => rw [hpart_mid]
            rw [Finset.sum_biUnion hdisj_mid]
          rw [h_swap]
          calc ‖∑ h ∈ oddH, c_tilde h * ∑ k ∈ dyadicBlocks _ _, _‖
              ≤ ∑ h ∈ oddH, ‖c_tilde h‖ * ‖∑ k ∈ dyadicBlocks _ _, _‖ := by
                refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun h _ => by rw [norm_mul]))
            _ ≤ ∑ h ∈ oddH, ‖c_tilde h‖ *
                  (((dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ))).card : ℝ) *
                    (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ))) := by
                refine Finset.sum_le_sum (fun h hh => ?_)
                apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                calc ‖∑ k ∈ dyadicBlocks _ _, _‖
                    ≤ ∑ k ∈ dyadicBlocks _ _, ‖∑ p ∈ _, _‖ := norm_sum_le _ _
                  _ ≤ ∑ _k ∈ dyadicBlocks _ _, (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ)) := by
                      refine Finset.sum_le_sum (fun k hk => h_block_exp k hk h
                        (Finset.mem_filter.mp hh).2.1
                        (by have := Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1; rw [abs_le]; omega))
                  _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
            _ = (∑ h ∈ oddH, ‖c_tilde h‖) *
                  (((dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ))).card : ℝ) *
                    (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ))) := by rw [← Finset.sum_mul]
            _ ≤ ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) *
                  ((Real.log (n : ℝ) / Real.log 2 + 2) * (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ))) :=
                mul_le_mul h_L1 (mul_le_mul_of_nonneg_right hdy_card_le (by positivity)) (by positivity) (by positivity)
            _ = (4 / Real.pi) * C₁e * (n : ℝ) *
                  (((Real.log (2 * (H : ℝ) + 1) + 1) * (Real.log (n : ℝ) / Real.log 2 + 2)) *
                    (Real.log (n : ℝ)) ^ (-5 : ℝ)) := by ring
            _ ≤ (4 / Real.pi) * C₁e * (n : ℝ) * ((Real.log (n : ℝ)) ^ 4 * (Real.log (n : ℝ)) ^ (-5 : ℝ)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_right hloglog4 (by positivity)
            _ ≤ (2 + 4 * C₁e * (1 + Real.log 2)) * ((n : ℝ) / Real.log (n : ℝ)) := by
                have hrp : (Real.log (n : ℝ)) ^ 4 * (Real.log (n : ℝ)) ^ (-5 : ℝ) = 1 / Real.log (n : ℝ) := by
                  rw [← Real.rpow_natCast (Real.log (n : ℝ)) 4, ← Real.rpow_add hlogn_pos]
                  norm_num [Real.rpow_neg_one]
                rw [hrp]
                have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
                have h4pi : 4 / Real.pi ≤ 4 := div_le_self (by norm_num) hpi
                calc (4 / Real.pi) * C₁e * (n : ℝ) * (1 / Real.log (n : ℝ))
                    = ((4 / Real.pi) * C₁e) * ((n : ℝ) / Real.log (n : ℝ)) := by ring
                  _ ≤ (4 * C₁e) * ((n : ℝ) / Real.log (n : ℝ)) :=
                      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4pi hC₁e.le) (by positivity)
                  _ ≤ (2 + 4 * C₁e * (1 + Real.log 2)) * ((n : ℝ) / Real.log (n : ℝ)) := by
                      apply mul_le_mul_of_nonneg_right _ (by positivity)
                      nlinarith [hlog2_pos]
        have hB_err_le : ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) *
            (b_tilde 0 + ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
              b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re ≤
            (2 + 2 * Cm + 36 * C₁e) * ((n : ℝ) / Real.log (n : ℝ)) := by
          have h_split_re : ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) *
              (b_tilde 0 + ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re =
              (b_tilde 0).re * ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) +
              (∑ p ∈ S_mid, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
                ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                  b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re := by
            rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun p _ => ?_)
            rw [Complex.add_re, mul_add]
            congr 1
            · ring
            · simp [Complex.mul_re]
          rw [h_split_re]
          have h0_bound : (b_tilde 0).re * ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) ≤
              (2 + 2 * Cm) * ((n : ℝ) / Real.log (n : ℝ)) := by
            rw [h_btilde0]
            have hb0_re : ((2 / ((H : ℂ) + 1)).re) = 2 / ((H : ℝ) + 1) := by
              have : (2 : ℂ) / ((H : ℂ) + 1) = ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
              rw [this, Complex.ofReal_re]
            rw [hb0_re]
            have hsub : S_mid ⊆ (Finset.Icc 3 (Nat.floor (n : ℝ))).filter Nat.Prime := by
              intro p hp; simp only [S_mid, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
              exact ⟨⟨hp.1.1.1, (Nat.le_floor_iff hn_pos.le).mpr (by exact_mod_cast hp.1.1.2)⟩, hp.1.2⟩
            have hmert : ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) ≤
                (n : ℝ) * (Real.log (n : ℝ) + Cm) := by
              calc ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ))
                  = (n : ℝ) * ∑ p ∈ S_mid, Real.log (p : ℝ) / (p : ℝ) := by
                    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun _ _ => by ring)
                _ ≤ (n : ℝ) * ∑ p ∈ (Finset.Icc 3 (Nat.floor (n : ℝ))).filter Nat.Prime,
                      Real.log (p : ℝ) / (p : ℝ) := by
                    apply mul_le_mul_of_nonneg_left _ hn_pos.le
                    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by
                      have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
                      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
                      positivity)
                _ ≤ (n : ℝ) * (Real.log (n : ℝ) + Cm) := mul_le_mul_of_nonneg_left (hCm n (by exact_mod_cast (by omega : 3 ≤ n))) hn_pos.le
            have h_sum_le : 2 * (Real.log (n : ℝ) + Cm) / ((H : ℝ) + 1) ≤ (2 + 2 * Cm) / Real.log (n : ℝ) := by
              have h_2H : (Real.log (n : ℝ)) ^ 2 ≤ (H : ℝ) + 1 := by
                have h2_le_5 : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 5 :=
                  pow_le_pow_right₀ (by linarith) (by norm_num)
                linarith
              have h1 : 2 * (Real.log (n : ℝ) + Cm) / ((H : ℝ) + 1) ≤
                  2 * (Real.log (n : ℝ) + Cm) / (Real.log (n : ℝ)) ^ 2 :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) h_2H
              have h2 : 2 * (Real.log (n : ℝ) + Cm) / (Real.log (n : ℝ)) ^ 2 ≤ (2 + 2 * Cm) / Real.log (n : ℝ) := by
                rw [div_le_div_iff₀ (by positivity) hlogn_pos]
                nlinarith [hln]
              exact le_trans h1 h2
            calc (2 / ((H : ℝ) + 1)) * ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ))
                ≤ (2 / ((H : ℝ) + 1)) * ((n : ℝ) * (Real.log (n : ℝ) + Cm)) :=
                  mul_le_mul_of_nonneg_left hmert (by positivity)
              _ = (n : ℝ) * (2 * (Real.log (n : ℝ) + Cm) / ((H : ℝ) + 1)) := by ring
              _ ≤ (n : ℝ) * ((2 + 2 * Cm) / Real.log (n : ℝ)) :=
                  mul_le_mul_of_nonneg_left h_sum_le hn_pos.le
              _ = (2 + 2 * Cm) * ((n : ℝ) / Real.log (n : ℝ)) := by ring
          have hnz_bound : (∑ p ∈ S_mid, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
                ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                  b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re ≤
              36 * C₁e * ((n : ℝ) / Real.log (n : ℝ)) := by
            let nzH := (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0)
            have h_swap : ∑ p ∈ S_mid, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
                  ∑ h ∈ nzH, b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2) =
                ∑ h ∈ nzH, b_tilde h * ∑ k ∈ dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ)),
                  ∑ p ∈ S_mid.filter (fun p : ℕ => (Nat.sqrt n : ℝ) * (2 : ℝ) ^ k < (p : ℝ) ∧
                      (p : ℝ) ≤ 2 * ((Nat.sqrt n : ℝ) * (2 : ℝ) ^ k)),
                    (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2) := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun h _ => ?_)
              rw [← Finset.mul_sum]
              congr 1
              conv_lhs => rw [hpart_mid]
              rw [Finset.sum_biUnion hdisj_mid]
            refine le_trans (Complex.re_le_abs _) ?_
            rw [← Complex.norm_eq_abs, h_swap]
            have hnz_card : (nzH.card : ℝ) ≤ 4 * (H : ℝ) + 3 := by
              have h1 : nzH.card ≤ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).card :=
                Finset.card_filter_le _ _
              have h2 : (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).card = 4 * H + 3 := by
                rw [Int.card_Icc]; omega
              exact_mod_cast le_trans h1 h2.le
            have hdy_le_3log : ((dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ))).card : ℝ) ≤ 3 * Real.log (n : ℝ) := by
              have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
              have : Real.log (n : ℝ) / Real.log 2 ≤ 2 * Real.log (n : ℝ) := by
                rw [div_le_iff₀ hlog2_pos]; nlinarith
              linarith
            calc ‖∑ h ∈ nzH, b_tilde h * ∑ k ∈ dyadicBlocks _ _, _‖
                ≤ ∑ h ∈ nzH, ‖b_tilde h‖ * ‖∑ k ∈ dyadicBlocks _ _, _‖ := by
                  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun h _ => by rw [norm_mul]))
              _ ≤ ∑ _h ∈ nzH, (3 / ((H : ℝ) + 1)) *
                    ((3 * Real.log (n : ℝ)) * (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ))) := by
                  refine Finset.sum_le_sum (fun h hh => ?_)
                  refine mul_le_mul (h_btilde_b h).le ?_ (norm_nonneg _) (by positivity)
                  calc ‖∑ k ∈ dyadicBlocks _ _, _‖
                      ≤ ∑ k ∈ dyadicBlocks _ _, ‖∑ p ∈ _, _‖ := norm_sum_le _ _
                    _ ≤ ∑ _k ∈ dyadicBlocks _ _, (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ)) := by
                        refine Finset.sum_le_sum (fun k hk => h_block_exp k hk h
                          (Finset.mem_filter.mp hh).2
                          (by have := Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1; rw [abs_le]; omega))
                    _ = ((dyadicBlocks _ _).card : ℝ) * (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ)) := by
                        simp [Finset.sum_const, nsmul_eq_mul]
                    _ ≤ (3 * Real.log (n : ℝ)) * (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ)) :=
                        mul_le_mul_of_nonneg_right hdy_le_3log (by positivity)
              _ = (nzH.card : ℝ) * (3 / ((H : ℝ) + 1)) *
                    (3 * Real.log (n : ℝ) * (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ))) := by
                  simp [Finset.sum_const, nsmul_eq_mul]; ring
              _ ≤ 12 * (3 * Real.log (n : ℝ) * (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ))) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
                  linarith
              _ = 36 * C₁e * (n : ℝ) * (Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ)) := by ring
              _ ≤ 36 * C₁e * ((n : ℝ) / Real.log (n : ℝ)) := by
                  have h_rpow : Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ) = (Real.log (n : ℝ)) ^ (-4 : ℝ) := by
                    conv_lhs => rw [← Real.rpow_one (Real.log (n : ℝ)), ← Real.rpow_add hlogn_pos]
                    congr 1; norm_num
                  have h_le_inv : (Real.log (n : ℝ)) ^ (-4 : ℝ) ≤ 1 / Real.log (n : ℝ) := by
                    rw [show (-4 : ℝ) = -(4 : ℕ) from by norm_num, Real.rpow_neg hlogn_pos.le,
                      Real.rpow_natCast, one_div]
                    exact inv_anti₀ hlogn_pos (le_self_pow₀ (by linarith) (by norm_num : 4 ≠ 0))
                  rw [h_rpow]
                  calc 36 * C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-4 : ℝ)
                      ≤ 36 * C₁e * (n : ℝ) * (1 / Real.log (n : ℝ)) :=
                        mul_le_mul_of_nonneg_left h_le_inv (by positivity)
                    _ = 36 * C₁e * ((n : ℝ) / Real.log (n : ℝ)) := by ring
          linarith
        linarith [h_diff_bound, hmain_le, hB_err_le]
      have htri := abs_sub
        (∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ)) * Real.log (p : ℝ))
        (∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ))
      linarith [hsplit_mid, hfrac_bound, hmain_mid]
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ) / Real.log (n : ℝ))]
  have hid : Delta_parity n - (Real.log 2 - 1 - Sigma_star_parity n) * (n : ℝ) =
      E_digit n + ∑ p ∈ S_mid, f_term p + (∑ p ∈ S_hi, f_term p - (Real.log 2 - 1) * (n : ℝ)) := by
    rw [hDelta_split, hlow_eq]
    ring
  rw [hid]
  have h1 := abs_add_le (E_digit n + ∑ p ∈ S_mid, f_term p) (∑ p ∈ S_hi, f_term p - (Real.log 2 - 1) * (n : ℝ))
  have h2 := abs_add_le (E_digit n) (∑ p ∈ S_mid, f_term p)
  linarith [hed_bound, hmid_bound, hhi_bound, h1, h2]


end GrasGreenbergBrocard
