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
set_option maxHeartbeats 400000

noncomputable section

open Real Finset BigOperators Asymptotics Filter Classical

namespace GrasGreenbergBrocard

theorem interCollar_band_isBigO (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3)
    (r : ℕ) (hr2 : 2 ≤ r) (hrR : r ≤ Nat.floor (1 / δ)) :
    (fun n : ℕ => ∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
        p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧
        (p : ℝ) ∈ interCollar n r (6 * Nat.floor (1 / δ) + 30))),
      ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1)))
      =O[atTop] (fun n : ℕ => 1 / Real.log (n : ℝ)) := by
  set R := Nat.floor (1 / δ)
  set A_R := 6 * R + 30
  have hR3 : 3 ≤ R := by
    rw [Nat.le_floor_iff (by positivity)]
    have h3 : (3 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
    exact_mod_cast h3
  obtain ⟨η', η, hη', hη, C₁e, C₂e, C₃e, hC₁e, hC₂e, hC₃e, hExp⟩ :=
    prime_exp_sum_bounds δ hδ0 hδ1
  obtain ⟨Cm, hCm_pos, hCm⟩ := mertens_sum_le
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_rpow_div : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ A_R / (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))))
      atTop (nhds 0) :=
    log_pow_div_rpow_tendsto_zero A_R (by positivity)
  have ht_nδ : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ (n : ℝ) ^ δ :=
    ((tendsto_rpow_atTop hδ0).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  have h_sqrt_12 : ∀ᶠ n : ℕ in atTop,
      (Nat.sqrt n : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := by
    have ht := log_pow_div_rpow_tendsto_zero 12 (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [Filter.eventually_ge_atTop 4,
      (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)] with n hn hsm
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h1 := (div_le_iff₀ (by positivity)).mp hsm
    rw [← Real.sqrt_eq_rpow] at h1
    have h2 : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]; exact_mod_cast Nat.sqrt_le' n
    rw [le_div_iff₀ (pow_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < n))) 12)]
    calc (Nat.sqrt n : ℝ) * (Real.log (n : ℝ)) ^ 12 ≤ Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 12 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          linarith
      _ = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
  have h_log_pow_R : ∀ᶠ n : ℕ in atTop,
      (Real.log (2 * (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) + 1) + 1) ≤ Real.log (n : ℝ) := by
    have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop := hlog_inf
    filter_upwards [ht.eventually (eventually_ge_atTop ((R + 4 : ℝ) ^ 4 + 10000))] with n hn
    have hln_ge10000 : 10000 ≤ Real.log (n : ℝ) := by
      have : 0 ≤ (R + 4 : ℝ) ^ 4 := by positivity
      linarith
    have hfl_le : 2 * (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) + 1 ≤ (Real.log (n : ℝ)) ^ (R + 3) := by
      have h1 : (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) :=
        Nat.floor_le (by positivity)
      have h2 : (Real.log (n : ℝ)) ^ (R + 2) * 3 ≤ (Real.log (n : ℝ)) ^ (R + 3) := by
        rw [show R + 3 = R + 2 + 1 from rfl, pow_succ]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h3 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) := one_le_pow₀ (by linarith)
      linarith
    have hlog_le : Real.log (2 * (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) + 1) ≤
        ((R : ℝ) + 3) * Real.log (Real.log (n : ℝ)) := by
      calc Real.log (2 * (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) + 1)
          ≤ Real.log ((Real.log (n : ℝ)) ^ (R + 3)) := Real.log_le_log (by positivity) hfl_le
        _ = ((R : ℝ) + 3) * Real.log (Real.log (n : ℝ)) := by rw [Real.log_pow]; push_cast; ring
    have hsqrt_y : Real.log (Real.log (n : ℝ)) ≤ 2 * Real.sqrt (Real.log (n : ℝ)) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith : 0 < Real.log (n : ℝ)))
      have h2 : Real.log (Real.log (n : ℝ)) = 2 * Real.log (Real.sqrt (Real.log (n : ℝ))) := by
        rw [Real.log_sqrt (by linarith)]; ring
      linarith
    have hR4_sq : 2 * ((R : ℝ) + 3) + 1 ≤ Real.sqrt (Real.log (n : ℝ)) := by
      have h1 : (2 * ((R : ℝ) + 3) + 1) ^ 2 ≤ (R + 4 : ℝ) ^ 4 := by
        have : 2 * ((R : ℝ) + 3) + 1 ≤ (R + 4 : ℝ) ^ 2 := by nlinarith
        calc (2 * ((R : ℝ) + 3) + 1) ^ 2 ≤ ((R + 4 : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
          _ = (R + 4 : ℝ) ^ 4 := by ring
      rw [Real.le_sqrt (by positivity) (by linarith)]
      linarith
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ Real.log (n : ℝ))]
  let M_inter : ℝ := 2 ^ R * (2 + 2 * Cm) + 96 ^ R * (3 * 4 * C₂e)
  refine Asymptotics.IsBigO.of_bound M_inter ?_
  filter_upwards [Filter.eventually_ge_atTop 16, hExp, h_sqrt_12,
    hlog_inf.eventually (eventually_ge_atTop 100),
    h_log_pow_R,
    (h_rpow_div.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le),
    ht_nδ] with
    n hn hexp_n hsq12 hln100 hlog_pR hdiv_sm hnδ_ge2
  set H := Nat.floor ((Real.log (n : ℝ)) ^ (R + 2))
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH_ge1 : 1 ≤ H := by
    rw [Nat.le_floor_iff (by positivity)]
    exact_mod_cast one_le_pow₀ (by linarith : (1 : ℝ) ≤ Real.log (n : ℝ)) (n := R + 2)
  let D_r := (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
    p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ∈ interCollar n r A_R)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / Real.log (n : ℝ))]
  rcases eq_or_ne D_r ∅ with h_emp | h_ne
  · rw [h_emp, Finset.sum_empty, abs_zero]; positivity
  · have h_pow_R1 : ∀ p ∈ D_r, n < p ^ (R + 1) := by
      intro p hp
      have hp_gt : (n : ℝ) ^ δ < (p : ℝ) := (Finset.mem_filter.mp hp).2.2.1
      have h1_lt_R1 : 1 < δ * ((R : ℝ) + 1) := by
        have : 1 / δ < (R : ℝ) + 1 := Nat.lt_floor_add_one (1 / δ)
        nlinarith [(div_lt_iff₀ hδ0).mp this]
      have h_lt : (n : ℝ) < (p : ℝ) ^ (R + 1) := by
        calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ < (n : ℝ) ^ (δ * ((R : ℝ) + 1)) :=
              Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < n)) h1_lt_R1
          _ = ((n : ℝ) ^ δ) ^ (R + 1) := by
              rw [← Real.rpow_natCast ((n : ℝ) ^ δ) (R + 1), ← Real.rpow_mul hn_pos.le]
          _ < (p : ℝ) ^ (R + 1) := pow_lt_pow_left₀ hp_gt (by positivity) (by omega)
      exact_mod_cast h_lt
    have hv_on_D : ∀ p ∈ D_r,
        (-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1) =
          -∏ s ∈ Finset.Icc 1 r, (-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ) ^ s) := by
      intro p hp
      have hp_pr := (Finset.mem_filter.mp hp).2.1
      have hp_ic := (Finset.mem_filter.mp hp).2.2.2
      have h_v : padicValNat p (Nat.factorial n) = ∑ s ∈ Finset.Icc 1 R, n / p ^ s :=
        padicValNat_factorial_eq_sum_Icc hp_pr (h_pow_R1 p hp)
      have h_gt_r_zero : ∀ s ∈ Finset.Icc (r + 1) R, n / p ^ s = 0 := by
        intro s hs
        have hs1 : r + 1 ≤ s := (Finset.mem_Icc.mp hs).1
        apply Nat.div_eq_of_lt
        have h_lt_n : (n : ℝ) < (p : ℝ) ^ (r + 1) := by
          have := Real.rpow_lt_rpow (by positivity) hp_ic.1 (by positivity : (0 : ℝ) < (r : ℝ) + 1)
          rw [← Real.rpow_mul hn_pos.le, one_div_mul_cancel (by positivity : (r : ℝ) + 1 ≠ 0), Real.rpow_one,
            ← Real.rpow_natCast (p : ℝ) (r + 1)] at this
          exact this
        have h_le_s : (p : ℝ) ^ (r + 1) ≤ (p : ℝ) ^ s := pow_le_pow_right₀ (by exact_mod_cast hp_pr.one_lt.le) hs1
        exact_mod_cast lt_of_lt_of_le h_lt_n h_le_s
      have h_sum_split : ∑ s ∈ Finset.Icc 1 R, n / p ^ s = ∑ s ∈ Finset.Icc 1 r, n / p ^ s := by
        have h1 : Finset.Icc 1 R = Finset.Icc 1 r ∪ Finset.Icc (r + 1) R := by
          ext s; simp only [Finset.mem_union, Finset.mem_Icc]; omega
        have h2 : Disjoint (Finset.Icc 1 r) (Finset.Icc (r + 1) R) := by
          rw [Finset.disjoint_left]; intro s hs1 hs2
          simp only [Finset.mem_Icc] at hs1 hs2; omega
        rw [h1, Finset.sum_union h2, Finset.sum_eq_zero h_gt_r_zero, add_zero]
      have hv_pos : 1 ≤ padicValNat p (Nat.factorial n) := by
        have hpn : p ≤ n := le_trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2 (Nat.sqrt_le_self n)
        have hdvd : p ∣ Nat.factorial n := hp_pr.dvd_factorial.mpr hpn
        exact one_le_padicValNat_of_dvd (Nat.factorial_ne_zero n) hdvd
      have hpow_neg : (-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1) =
          -((-1 : ℝ) ^ padicValNat p (Nat.factorial n)) := by
        have : padicValNat p (Nat.factorial n) = (padicValNat p (Nat.factorial n) - 1) + 1 := by omega
        conv_rhs => rw [this, pow_succ]
        ring
      rw [hpow_neg, h_v, h_sum_split, ← Finset.prod_pow_eq_pow_sum]
      congr 1
      refine Finset.prod_congr rfl (fun s _ => ?_)
      have hps_pos : (0 : ℝ) < (p : ℝ) ^ s := by positivity
      have hfl : Int.floor ((n : ℝ) / (p : ℝ) ^ s) = ((n / p ^ s : ℕ) : ℤ) := by
        rw [Int.floor_eq_iff]
        constructor
        · rw [Int.cast_natCast, le_div_iff₀ hps_pos]; exact_mod_cast Nat.div_mul_le_self n (p ^ s)
        · rw [Int.cast_natCast, div_lt_iff₀ hps_pos]
          have h_nat : n < (n / p ^ s + 1) * p ^ s := Nat.lt_div_mul_add (pow_pos hp_pr.pos s)
          exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((n / p ^ s + 1 : ℕ) : ℝ) * ((p ^ s : ℕ) : ℝ))
      rw [hfl, zpow_natCast]
    let A_lo := max ((n : ℝ) ^ δ) ((n : ℝ) ^ (1 / ((r : ℝ) + 1)))
    let B_hi := (n : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ))
    have hA_ge1 : 1 ≤ A_lo := le_max_of_le_left (Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) hδ0.le)
    have hAB : A_lo ≤ B_hi := by
      obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr h_ne
      have hp0_d := (Finset.mem_filter.mp hp0).2.2.1
      have hp0_ic := (Finset.mem_filter.mp hp0).2.2.2
      exact le_trans (max_lt hp0_d hp0_ic.1).le hp0_ic.2
    have hI_mem : ∀ p ∈ D_r, A_lo < (p : ℝ) ∧ (p : ℝ) ≤ B_hi := by
      intro p hp
      have hp_d := (Finset.mem_filter.mp hp).2.2.1
      have hp_ic := (Finset.mem_filter.mp hp).2.2.2
      exact ⟨max_lt hp_d hp_ic.1, hp_ic.2⟩
    obtain ⟨hpart_D, hdisj_D⟩ := dyadic_partition_finset hA_ge1 hAB D_r hI_mem
    obtain ⟨c_tilde, b_tilde, h_supp, h_ctilde_b, h_btilde0, h_btilde_b, h_vaaler_pw, h_L1⟩ :=
      vaaler_parity_approx H hH_ge1
    let allH := Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)
    let oddH := allH.filter (fun h => h ≠ 0 ∧ Odd h)
    let nzH := allH.filter (· ≠ 0)
    let b_real : ℤ → ℂ := fun h => (1 / 2 : ℂ) * (b_tilde h + star (b_tilde (-h)))
    have hb_real_0 : b_real 0 = ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) := by
      dsimp only [b_real]
      have hbt : b_tilde 0 = ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) := by rw [h_btilde0]; push_cast; rfl
      rw [neg_zero, hbt, Complex.conj_ofReal]
      push_cast; ring
    have hb_real_norm : ∀ h : ℤ, ‖b_real h‖ ≤ 3 / ((H : ℝ) + 1) := by
      intro h; dsimp only [b_real]
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 from by norm_num]
      have h1 := h_btilde_b h
      have h2 : ‖star (b_tilde (-h))‖ ≤ 3 / ((H : ℝ) + 1) := by rw [norm_star]; exact (h_btilde_b (-h)).le
      linarith [norm_add_le (b_tilde h) (star (b_tilde (-h)))]
    have h_D_block_exp : ∀ (k : ℕ) (hk : k ∈ dyadicBlocks A_lo B_hi) (A : Finset ℕ) (hA_sub : A ⊆ Finset.Icc 1 r)
        (h_fn : ℕ → ℤ) (hA_nz : ∃ s ∈ A, h_fn s ≠ 0) (hh_le : ∀ s ∈ A, |h_fn s| ≤ 2 * (H : ℤ) + 1),
        ‖∑ p ∈ D_r.filter (fun p : ℕ => A_lo * (2 : ℝ) ^ k < (p : ℝ) ∧ (p : ℝ) ≤ 2 * (A_lo * (2 : ℝ) ^ k)),
            ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
              eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s))‖ ≤
          4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by
      intro k hk A hA_sub h_fn hA_nz hh_le
      let P := A_lo * (2 : ℝ) ^ k
      let Ik := D_r.filter (fun p : ℕ => P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P)
      rcases eq_or_ne Ik ∅ with h_emp | h_Ik_ne
      · change ‖∑ p ∈ Ik, _‖ ≤ _; rw [h_emp, Finset.sum_empty, norm_zero]; positivity
      · have hP_lo : (n : ℝ) ^ δ ≤ P :=
          le_trans (le_max_left _ _) (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num)))
        have hP_pos : 0 < P := lt_of_lt_of_le (by positivity) hP_lo
        have hP_lt_B : P < B_hi := (Finset.mem_filter.mp hk).2
        have hP_hi : P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := by
          obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr h_Ik_ne
          have hp0_D := (Finset.mem_filter.mp hp0).1
          have hp0_le_sq : (p0 : ℝ) ≤ (Nat.sqrt n : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp0_D).1).2
          have hp0_gt : P < (p0 : ℝ) := (Finset.mem_filter.mp hp0).2.1
          linarith [hsq12]
        have hIk_pr : ∀ p ∈ Ik, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P := by
          intro p hp
          exact ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1, (Finset.mem_filter.mp hp).2⟩
        have hA_range : ∀ s ∈ A, 1 ≤ s ∧ s ≤ R := by
          intro s hs; have := Finset.mem_Icc.mp (hA_sub hs); omega
        have hPhase : ∀ s ∈ A, (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) / P ^ s := by
          intro s hs
          have hs_mem := Finset.mem_Icc.mp (hA_sub hs)
          have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
          have hB_ge1 : 1 ≤ B_hi := le_trans hA_ge1 hAB
          have hPs_le : P ^ s ≤ B_hi ^ r := by
            calc P ^ s ≤ B_hi ^ s := pow_le_pow_left₀ hP_pos.le hP_lt_B.le s
              _ ≤ B_hi ^ r := pow_le_pow_right₀ hB_ge1 hs_mem.2
          have hBr_eq : B_hi ^ r = (n : ℝ) / (Real.log (n : ℝ)) ^ A_R := by
            dsimp only [B_hi]
            rw [div_pow, ← Real.rpow_natCast _ r, ← Real.rpow_mul hn_pos.le,
              ← Real.rpow_natCast ((Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ))) r, ← Real.rpow_mul (by positivity)]
            rw [one_div_mul_cancel hr_pos.ne', div_mul_cancel₀ _ hr_pos.ne', Real.rpow_one, Real.rpow_natCast]
          have h2R_le1 : (2 : ℝ) ^ (-(R : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
          calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ (Real.log (n : ℝ)) ^ A_R :=
                mul_le_of_le_one_left (by positivity) h2R_le1
            _ = (n : ℝ) / B_hi ^ r := by rw [hBr_eq, div_div_cancel₀ (by positivity)]
            _ ≤ (n : ℝ) / P ^ s := div_le_div_of_nonneg_left hn_pos.le (by positivity) hPs_le
        have hP_ge2 : 2 ≤ P := by linarith [hnδ_ge2, hP_lo]
        have hW_b : ∀ t ∈ Set.Icc P (2 * P), |1 / (t - 1)| ≤ 2 / P := by
          intro t ht
          have ht1 : 0 < t - 1 := by linarith [ht.1]
          rw [abs_of_pos (one_div_pos.mpr ht1)]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith [ht.1, hP_ge2]
        have hexp_app := hexp_n P Ik A h_fn (fun t => 1 / (t - 1)) (2 / P)
          hA_nz hP_lo hP_hi hIk_pr hA_range hh_le hPhase hW_b (by positivity)
        dsimp only at hexp_app
        have hP_cancel : C₂e * (2 / P) * P * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) ≤
            4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by
          have hP_ne : P ≠ 0 := hP_pos.ne'
          calc C₂e * (2 / P) * P * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))
              = 2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by field_simp [hP_ne]
            _ ≤ 4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                linarith [hC₂e]
        have hsum_eq : ∑ p ∈ Ik, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
              eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s)) =
            ∑ p ∈ Ik, ((1 / ((p : ℝ) - 1) : ℝ) * Real.log (p : ℝ) : ℂ) *
              eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          push_cast; ring
        rw [hsum_eq]
        exact le_trans hexp_app.1.2 hP_cancel
    have hdy_card_le : ((dyadicBlocks A_lo B_hi).card : ℝ) ≤ 3 * Real.log (n : ℝ) := by
      have h1 := dyadicBlocks_card_le hA_ge1 hAB
      have hlog_BA : Real.log (B_hi / A_lo) ≤ Real.log (n : ℝ) := by
        apply Real.log_le_log (div_pos (by positivity) (by linarith))
        have hB_le_n : B_hi ≤ (n : ℝ) := by
          have h_le1 : B_hi ≤ (n : ℝ) ^ (1 / (r : ℝ)) := by
            apply div_le_self (by positivity)
            exact Real.one_le_rpow (by linarith) (by positivity)
          have h_le2 : (n : ℝ) ^ (1 / (r : ℝ)) ≤ (n : ℝ) := by
            calc (n : ℝ) ^ (1 / (r : ℝ)) ≤ (n : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
                    (div_le_self (by norm_num) (by exact_mod_cast (by omega : 1 ≤ r)))
              _ = (n : ℝ) := Real.rpow_one _
          exact le_trans h_le1 h_le2
        exact div_le_self hn_pos.le hA_ge1 |> fun h => le_trans (div_le_div_of_nonneg_right hB_le_n (by positivity)) h
      have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      have : Real.log (B_hi / A_lo) / Real.log 2 ≤ 2 * Real.log (n : ℝ) := by
        rw [div_le_iff₀ hlog2_pos]; nlinarith
      linarith
    let a_fn : ℕ → ℕ → ℂ := fun s p => (((-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) : ℂ)
    let b_fn : ℕ → ℕ → ℂ := fun s p =>
      ∑ h ∈ oddH, c_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / 2)
    let B_fn : ℕ → ℕ → ℝ := fun s p =>
      (∑ h ∈ allH, b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / 2)).re
    have ha_norm : ∀ s p, ‖a_fn s p‖ = 1 := fun s p => by
      dsimp only [a_fn]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_zpow, abs_neg, abs_one, one_zpow]
    have hB_pw : ∀ s p, ‖a_fn s p - b_fn s p‖ ≤ B_fn s p := fun s p => by
      simpa only [a_fn, b_fn, B_fn] using h_vaaler_pw ((n : ℝ) / (p : ℝ) ^ s)
    let S_idx := Finset.Icc 1 r
    have hS_idx_ne : S_idx.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
    have hS_idx_card : S_idx.card ≤ R := by rw [Nat.card_Icc]; omega
    let w_p : ℕ → ℝ := fun p => Real.log (p : ℝ) / ((p : ℝ) - 1)
    have hw_nn : ∀ p ∈ D_r, 0 ≤ w_p p := fun p hp => by
      dsimp only [D_r] at hp
      have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
      exact div_nonneg hlogp hp1.le
    have hsum_re : ∑ p ∈ D_r, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * w_p p =
        -(∑ p ∈ D_r, (w_p p : ℂ) * ∏ s ∈ S_idx, a_fn s p).re := by
      rw [Complex.re_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [hv_on_D p hp]
      have hprod_re : (((w_p p : ℂ) * ∏ s ∈ S_idx, a_fn s p)).re =
          w_p p * ∏ s ∈ S_idx, (-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ) ^ s) := by
        have hcast : ∏ s ∈ S_idx, a_fn s p = ((∏ s ∈ S_idx, (-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) : ℂ) := by
          dsimp only [a_fn]; rw [Complex.ofReal_prod]
        rw [hcast, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [hprod_re]; ring
    rw [hsum_re, abs_neg]
    have h_abs_le : |(∑ p ∈ D_r, (w_p p : ℂ) * ∏ s ∈ S_idx, a_fn s p).re| ≤
        ‖∑ p ∈ D_r, (w_p p : ℂ) * ∏ s ∈ S_idx, a_fn s p‖ := Complex.abs_re_le_norm _
    have h_split : ‖∑ p ∈ D_r, (w_p p : ℂ) * ∏ s ∈ S_idx, a_fn s p‖ ≤
        ‖∑ p ∈ D_r, (w_p p : ℂ) * ∏ s ∈ S_idx, b_fn s p‖ +
        ∑ p ∈ D_r, w_p p * ∑ T ∈ S_idx.powerset.filter (·.Nonempty), ∏ s ∈ T, B_fn s p := by
      have hid : ∑ p ∈ D_r, (w_p p : ℂ) * ∏ s ∈ S_idx, a_fn s p =
          (∑ p ∈ D_r, (w_p p : ℂ) * ∏ s ∈ S_idx, b_fn s p) +
          ∑ p ∈ D_r, (w_p p : ℂ) * (∏ s ∈ S_idx, a_fn s p - ∏ s ∈ S_idx, b_fn s p) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun p _ => by ring)
      rw [hid]
      refine le_trans (norm_add_le _ _) (add_le_add le_rfl ?_)
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun p hp => ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw_nn p hp)]
      exact mul_le_mul_of_nonneg_left
        (prod_sub_prod_le_powerset _ (fun s => a_fn s p) (fun s => b_fn s p) (fun s => B_fn s p)
          (fun s _ => ha_norm s p) (fun s _ => hB_pw s p))
        (hw_nn p hp)
    have h_main_b : ‖∑ p ∈ D_r, (w_p p : ℂ) * ∏ s ∈ S_idx, b_fn s p‖ ≤
        6 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ)) := by
      have h_prod_exp : ∀ p ∈ D_r,
          ∏ s ∈ S_idx, b_fn s p =
            ∑ g ∈ S_idx.pi (fun _ => oddH),
              (∏ s ∈ S_idx, c_tilde (g s.1 s.2)) *
                eExp (∑ s ∈ S_idx, ((if hs : s ∈ S_idx then g s hs else 0 : ℤ) : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
        intro p _
        dsimp only [b_fn]
        rw [Finset.prod_sum]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [Finset.prod_mul_distrib, eExp_sum]
        congr 2
        refine Finset.sum_congr rfl (fun s hs => ?_)
        simp only [dif_pos hs]; ring
      rw [Finset.sum_congr rfl (fun p hp => by rw [h_prod_exp p hp, Finset.mul_sum])]
      rw [Finset.sum_comm]
      have h_each_g : ∀ g ∈ S_idx.pi (fun _ => oddH),
          ‖∑ p ∈ D_r, (w_p p : ℂ) * ((∏ s ∈ S_idx, c_tilde (g s.1 s.2)) *
            eExp (∑ s ∈ S_idx, ((if hs : s ∈ S_idx then g s hs else 0 : ℤ) : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s)))‖ ≤
          (∏ s ∈ S_idx, ‖c_tilde (g s.1 s.2)‖) * (3 * Real.log (n : ℝ) * (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) := by
        intro g hg
        have hpull : ∑ p ∈ D_r, (w_p p : ℂ) * ((∏ s ∈ S_idx, c_tilde (g s.1 s.2)) *
              eExp (∑ s ∈ S_idx, ((if hs : s ∈ S_idx then g s hs else 0 : ℤ) : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s))) =
            (∏ s ∈ S_idx, c_tilde (g s.1 s.2)) * ∑ k ∈ dyadicBlocks A_lo B_hi,
              ∑ p ∈ D_r.filter (fun p : ℕ => A_lo * (2 : ℝ) ^ k < (p : ℝ) ∧ (p : ℝ) ≤ 2 * (A_lo * (2 : ℝ) ^ k)),
                (w_p p : ℂ) * eExp (∑ s ∈ S_idx, ((if hs : s ∈ S_idx then g s hs else 0 : ℤ) : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
          rw [← Finset.sum_biUnion hdisj_D, ← hpart_D, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p _ => by ring)
        rw [hpull, norm_mul, norm_prod]
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
        obtain ⟨s0, hs0⟩ := hS_idx_ne
        have hnz : ∃ s ∈ S_idx, (if hs : s ∈ S_idx then g s hs else 0) ≠ 0 := by
          refine ⟨s0, hs0, ?_⟩; rw [dif_pos hs0]
          exact (Finset.mem_filter.mp (Finset.mem_pi.mp hg s0 hs0)).2.1
        have hle : ∀ s ∈ S_idx, |if hs : s ∈ S_idx then g s hs else 0| ≤ 2 * (H : ℤ) + 1 := by
          intro s hs; rw [dif_pos hs]
          have := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_pi.mp hg s hs)).1
          rw [abs_le]; omega
        calc ‖∑ k ∈ dyadicBlocks A_lo B_hi, ∑ p ∈ _, _‖
            ≤ ∑ k ∈ dyadicBlocks A_lo B_hi, ‖∑ p ∈ _, _‖ := norm_sum_le _ _
          _ ≤ ∑ _k ∈ dyadicBlocks A_lo B_hi, (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) :=
              Finset.sum_le_sum (fun k hk => h_D_block_exp k hk S_idx le_rfl
                (fun s => if hs : s ∈ S_idx then g s hs else 0) hnz hle)
          _ = ((dyadicBlocks A_lo B_hi).card : ℝ) * (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
              simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (3 * Real.log (n : ℝ)) * (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) :=
              mul_le_mul_of_nonneg_right hdy_card_le (by positivity)
      calc ‖∑ g ∈ S_idx.pi (fun _ => oddH), ∑ p ∈ D_r, _‖
          ≤ ∑ g ∈ S_idx.pi (fun _ => oddH), ‖∑ p ∈ D_r, _‖ := norm_sum_le _ _
        _ ≤ ∑ g ∈ S_idx.pi (fun _ => oddH),
              (∏ s ∈ S_idx, ‖c_tilde (g s.1 s.2)‖) * (3 * Real.log (n : ℝ) * (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) :=
            Finset.sum_le_sum h_each_g
        _ = (∏ _s ∈ S_idx, ∑ h ∈ oddH, ‖c_tilde h‖) *
              (3 * Real.log (n : ℝ) * (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) := by
            rw [← Finset.sum_mul]; congr 1; rw [Finset.prod_sum]
        _ ≤ (6 * Real.log (n : ℝ)) ^ R *
              (3 * Real.log (n : ℝ) * (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hL1_le : (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1) ≤ 6 * Real.log (n : ℝ) := by
              have h4pi : 4 / Real.pi ≤ 2 := by rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
              nlinarith [hlog_pR]
            have h6_ge1 : (1 : ℝ) ≤ 6 * Real.log (n : ℝ) := by linarith
            calc (∏ _s ∈ S_idx, ∑ h ∈ oddH, ‖c_tilde h‖)
                = (∑ h ∈ oddH, ‖c_tilde h‖) ^ S_idx.card := by rw [Finset.prod_const]
              _ ≤ ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ S_idx.card :=
                  pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) h_L1 _
              _ ≤ (6 * Real.log (n : ℝ)) ^ S_idx.card :=
                  pow_le_pow_left₀ (by positivity) hL1_le _
              _ ≤ (6 * Real.log (n : ℝ)) ^ R := pow_le_pow_right₀ h6_ge1 hS_idx_card
        _ = 6 ^ R * (3 * 4 * C₂e) * ((Real.log (n : ℝ)) ^ (R + 1) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
            rw [mul_pow, pow_succ]; ring
        _ = 6 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ)) := by
            congr 1
            rw [← Real.rpow_natCast (Real.log (n : ℝ)) (R + 1), ← Real.rpow_add hlogn_pos]
            have hexp : ((R + 1 : ℕ) : ℝ) + (-((R : ℝ) + 2)) = -1 := by push_cast; ring
            rw [hexp, Real.rpow_neg_one, one_div]
    have h_B_err : ∑ p ∈ D_r, w_p p * ∑ T ∈ S_idx.powerset.filter (·.Nonempty), ∏ s ∈ T, B_fn s p ≤
        (2 ^ R * (2 + 2 * Cm) + 48 ^ R * (3 * 4 * C₂e)) * (1 / Real.log (n : ℝ)) := by
      rw [Finset.sum_congr rfl (fun p _ => Finset.mul_sum _ _ _)]
      rw [Finset.sum_comm]
      have hmert_Dr : ∑ p ∈ D_r, w_p p ≤ Real.log (n : ℝ) + Cm := by
        have hsub : D_r ⊆ (Finset.Icc 3 (Nat.floor (n : ℝ))).filter Nat.Prime := by
          intro p hp; simp only [D_r, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨⟨hp.1.1, (Nat.le_floor_iff hn_pos.le).mpr (by exact_mod_cast le_trans hp.1.2 (Nat.sqrt_le_self n))⟩, hp.2.1⟩
        exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by
          have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
          have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
          have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
          exact div_nonneg hlogp hp1.le)) (hCm n (by exact_mod_cast (by omega : 3 ≤ n)))
      have h_each_T : ∀ T ∈ S_idx.powerset.filter (·.Nonempty),
          ∑ p ∈ D_r, w_p p * ∏ s ∈ T, B_fn s p ≤
            (2 + 2 * Cm) * (1 / Real.log (n : ℝ)) + 24 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ)) := by
        intro T hT
        have hT_sub : T ⊆ S_idx := (Finset.mem_filter.mp hT).1
        let Z : ℕ → ℕ → ℂ := fun s p =>
          ∑ h ∈ nzH, b_real h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / 2)
        have hB_eq_C : ∀ s p, (B_fn s p : ℂ) = Z s p + ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) := by
          intro s p; dsimp only [B_fn]
          have hrep := vaaler_B_real_rep b_tilde (2 * (H : ℤ) + 1) (by positivity) (((n : ℝ) / (p : ℝ) ^ s) / 2)
          dsimp only at hrep
          have h_arg : ∀ h : ℤ, (h : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / 2 = (h : ℝ) * (((n : ℝ) / (p : ℝ) ^ s) / 2) := by
            intro h; ring
          simp_rw [h_arg]
          rw [hrep]
          have h0_mem : (0 : ℤ) ∈ allH := by simp only [allH, Finset.mem_Icc]; omega
          rw [← Finset.add_sum_erase _ _ h0_mem]
          have h0_term : b_real 0 * eExp ((0 : ℝ) * (((n : ℝ) / (p : ℝ) ^ s) / 2)) = ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) := by
            rw [hb_real_0, zero_mul, show eExp 0 = 1 from by unfold eExp; simp, mul_one]
          have h_nz_eq : allH.erase 0 = nzH := by
            ext h; simp [nzH, allH, Finset.mem_erase, Finset.mem_filter]; tauto
          rw [h0_term, h_nz_eq, add_comm]; rfl
        have h_re_eq : ∑ p ∈ D_r, w_p p * ∏ s ∈ T, B_fn s p =
            (∑ p ∈ D_r, (w_p p : ℂ) * ∏ s ∈ T, (Z s p + ((2 / ((H : ℝ) + 1) : ℝ) : ℂ))).re := by
          rw [Complex.re_sum]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          have hprod_C : ∏ s ∈ T, (Z s p + ((2 / ((H : ℝ) + 1) : ℝ) : ℂ)) =
              ((∏ s ∈ T, B_fn s p : ℝ) : ℂ) := by
            push_cast; exact Finset.prod_congr rfl (fun s _ => (hB_eq_C s p).symm)
          rw [hprod_C, ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [h_re_eq]
        refine le_trans (Complex.re_le_abs _) ?_
        rw [← Complex.norm_eq_abs]
        have h_prod_T : ∀ p ∈ D_r,
            ∏ s ∈ T, (Z s p + ((2 / ((H : ℝ) + 1) : ℝ) : ℂ)) =
              ∑ U ∈ T.powerset, (∏ s ∈ U, Z s p) * ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ U).card := by
          intro p _; rw [Finset.prod_add]; refine Finset.sum_congr rfl (fun U _ => by rw [Finset.prod_const])
        rw [Finset.sum_congr rfl (fun p hp => by rw [h_prod_T p hp, Finset.mul_sum]), Finset.sum_comm]
        have hU_split : T.powerset = insert ∅ (T.powerset.filter (·.Nonempty)) := by
          ext U; simp only [Finset.mem_insert, Finset.mem_powerset, Finset.mem_filter]
          constructor
          · intro hU; rcases Finset.eq_empty_or_nonempty U with rfl | hne
            · left; rfl
            · right; exact ⟨hU, hne⟩
          · rintro (rfl | ⟨hU, _⟩); exact Finset.empty_subset _; exact hU
        have hnot_emp : (∅ : Finset ℕ) ∉ T.powerset.filter (·.Nonempty) := by simp [Finset.not_nonempty_empty]
        rw [hU_split, Finset.sum_insert hnot_emp]
        refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
        · have h_emp_eq : ∑ p ∈ D_r, (w_p p : ℂ) * ((∏ s ∈ (∅ : Finset ℕ), Z s p) *
                ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ ∅).card) =
              (((2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ D_r, w_p p : ℝ) : ℂ) := by
            simp only [Finset.prod_empty, one_mul, Finset.sdiff_empty]; push_cast
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun p _ => by ring)
          rw [h_emp_eq, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg hw_nn))]
          have hT_card1 : 1 ≤ T.card := Finset.Nonempty.card_pos (Finset.mem_filter.mp hT).2
          have hpow_le : (2 / ((H : ℝ) + 1)) ^ T.card ≤ 2 / ((H : ℝ) + 1) := by
            have hbase : 2 / ((H : ℝ) + 1) ≤ 1 := by
              rw [div_le_one (by positivity)]; have : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH_ge1; linarith
            exact pow_le_of_le_one (by positivity) hbase hT_card1.ne'
          have h2_H : (Real.log (n : ℝ)) ^ 2 ≤ (H : ℝ) + 1 := by
            have : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ (R + 2) :=
              pow_le_pow_right₀ (by linarith) (by omega)
            linarith [Nat.lt_floor_add_one ((Real.log (n : ℝ)) ^ (R + 2))]
          calc (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ D_r, w_p p
              ≤ (2 / ((H : ℝ) + 1)) * (Real.log (n : ℝ) + Cm) :=
                mul_le_mul hpow_le hmert_Dr (Finset.sum_nonneg hw_nn) (by positivity)
            _ ≤ (2 / (Real.log (n : ℝ)) ^ 2) * (Real.log (n : ℝ) + Cm) := by
                apply mul_le_mul_of_nonneg_right _ (by linarith)
                exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h2_H
            _ ≤ (2 + 2 * Cm) * (1 / Real.log (n : ℝ)) := by
                rw [div_mul_eq_mul_div, mul_one_div, div_le_div_iff₀ (by positivity) hlogn_pos]
                nlinarith [hln100]
        · have h_each_U : ∀ U ∈ T.powerset.filter (·.Nonempty),
              ‖∑ p ∈ D_r, (w_p p : ℂ) * ((∏ s ∈ U, Z s p) *
                ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ U).card)‖ ≤
              12 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ)) := by
            intro U hU
            have hU_sub : U ⊆ S_idx := Finset.Subset.trans (Finset.mem_filter.mp hU).1 hT_sub
            have hU_ne : U.Nonempty := (Finset.mem_filter.mp hU).2
            have hU_card : U.card ≤ R := le_trans (Finset.card_le_card hU_sub) hS_idx_card
            have hpull : ∑ p ∈ D_r, (w_p p : ℂ) * ((∏ s ∈ U, Z s p) *
                  ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ U).card) =
                ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ U).card *
                  ∑ p ∈ D_r, (w_p p : ℂ) * ∏ s ∈ U, Z s p := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun p _ => by ring)
            rw [hpull, norm_mul, norm_pow, Complex.norm_real,
              Real.norm_of_nonneg (by positivity : 0 ≤ 2 / ((H : ℝ) + 1))]
            have h_pow_le1 : (2 / ((H : ℝ) + 1)) ^ (T \ U).card ≤ 1 := by
              apply pow_le_one₀ (by positivity); rw [div_le_one (by positivity)]
              have : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH_ge1; linarith
            refine le_trans (mul_le_mul_of_nonneg_right h_pow_le1 (norm_nonneg _)) ?_
            rw [one_mul]
            have hZ_exp : ∀ p ∈ D_r, ∏ s ∈ U, Z s p =
                  ∑ g ∈ U.pi (fun _ => nzH),
                    (∏ s ∈ U, b_real (g s.1 s.2)) *
                      eExp (∑ s ∈ U, ((if hs : s ∈ U then g s hs else 0 : ℤ) : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
              intro p _; dsimp only [Z]; rw [Finset.prod_sum]
              refine Finset.sum_congr rfl (fun g _ => ?_)
              rw [Finset.prod_mul_distrib, eExp_sum]; congr 2
              refine Finset.sum_congr rfl (fun s hs => by simp only [dif_pos hs]; ring)
            rw [Finset.sum_congr rfl (fun p hp => by rw [hZ_exp p hp, Finset.mul_sum]), Finset.sum_comm]
            have h_each_g : ∀ g ∈ U.pi (fun _ => nzH),
                ‖∑ p ∈ D_r, (w_p p : ℂ) * ((∏ s ∈ U, b_real (g s.1 s.2)) *
                  eExp (∑ s ∈ U, ((if hs : s ∈ U then g s hs else 0 : ℤ) : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s)))‖ ≤
                (∏ s ∈ U, ‖b_real (g s.1 s.2)‖) * (3 * Real.log (n : ℝ) * (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) := by
              intro g hg
              have hpull_g : ∑ p ∈ D_r, (w_p p : ℂ) * ((∏ s ∈ U, b_real (g s.1 s.2)) *
                    eExp (∑ s ∈ U, ((if hs : s ∈ U then g s hs else 0 : ℤ) : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s))) =
                  (∏ s ∈ U, b_real (g s.1 s.2)) * ∑ k ∈ dyadicBlocks A_lo B_hi,
                    ∑ p ∈ D_r.filter (fun p : ℕ => A_lo * (2 : ℝ) ^ k < (p : ℝ) ∧ (p : ℝ) ≤ 2 * (A_lo * (2 : ℝ) ^ k)),
                      (w_p p : ℂ) * eExp (∑ s ∈ U, ((if hs : s ∈ U then g s hs else 0 : ℤ) : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
                rw [← Finset.sum_biUnion hdisj_D, ← hpart_D, Finset.mul_sum]
                refine Finset.sum_congr rfl (fun p _ => by ring)
              rw [hpull_g, norm_mul, norm_prod]
              apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
              obtain ⟨s0, hs0⟩ := hU_ne
              have hnz : ∃ s ∈ U, (if hs : s ∈ U then g s hs else 0) ≠ 0 := by
                refine ⟨s0, hs0, ?_⟩; rw [dif_pos hs0]
                exact (Finset.mem_filter.mp (Finset.mem_pi.mp hg s0 hs0)).2
              have hle : ∀ s ∈ U, |if hs : s ∈ U then g s hs else 0| ≤ 2 * (H : ℤ) + 1 := by
                intro s hs; rw [dif_pos hs]
                have := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_pi.mp hg s hs)).1
                rw [abs_le]; omega
              calc ‖∑ k ∈ dyadicBlocks A_lo B_hi, ∑ p ∈ _, _‖
                  ≤ ∑ k ∈ dyadicBlocks A_lo B_hi, ‖∑ p ∈ _, _‖ := norm_sum_le _ _
                _ ≤ ∑ _k ∈ dyadicBlocks A_lo B_hi, (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) :=
                    Finset.sum_le_sum (fun k hk => h_D_block_exp k hk U hU_sub
                      (fun s => if hs : s ∈ U then g s hs else 0) hnz hle)
                _ = ((dyadicBlocks A_lo B_hi).card : ℝ) * (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
                    simp [Finset.sum_const, nsmul_eq_mul]
                _ ≤ (3 * Real.log (n : ℝ)) * (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) :=
                    mul_le_mul_of_nonneg_right hdy_card_le (by positivity)
            have h_nz_sum_le : ∑ h ∈ nzH, ‖b_real h‖ ≤ 12 := by
              have hnz_card : (nzH.card : ℝ) ≤ 4 * (H : ℝ) + 3 := by
                have h1 : nzH.card ≤ allH.card := Finset.card_filter_le _ _
                have h2 : allH.card = 4 * H + 3 := by dsimp only [allH]; rw [Int.card_Icc]; omega
                exact_mod_cast le_trans h1 h2.le
              calc ∑ h ∈ nzH, ‖b_real h‖ ≤ ∑ _h ∈ nzH, (3 / ((H : ℝ) + 1)) := Finset.sum_le_sum (fun h _ => hb_real_norm h)
                _ = (nzH.card : ℝ) * (3 / ((H : ℝ) + 1)) := by simp [Finset.sum_const, nsmul_eq_mul]
                _ ≤ (4 * (H : ℝ) + 3) * (3 / ((H : ℝ) + 1)) := mul_le_mul_of_nonneg_right hnz_card (by positivity)
                _ ≤ 12 := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; linarith
            have h_rpow_le_inv : Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) ≤ 1 / Real.log (n : ℝ) := by
              have h1 : Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) = (Real.log (n : ℝ)) ^ (-((R : ℝ) + 1)) := by
                conv_lhs => rw [← Real.rpow_one (Real.log (n : ℝ)), ← Real.rpow_add hlogn_pos]
                congr 1; ring
              rw [h1, show -((R : ℝ) + 1) = -((R + 1 : ℕ) : ℝ) from by push_cast; ring,
                Real.rpow_neg hlogn_pos.le, Real.rpow_natCast, one_div]
              exact inv_anti₀ hlogn_pos (le_self_pow₀ (by linarith) (by omega))
            calc ‖∑ g ∈ U.pi (fun _ => nzH), ∑ p ∈ D_r, _‖
                ≤ ∑ g ∈ U.pi (fun _ => nzH), ‖∑ p ∈ D_r, _‖ := norm_sum_le _ _
              _ ≤ ∑ g ∈ U.pi (fun _ => nzH),
                    (∏ s ∈ U, ‖b_real (g s.1 s.2)‖) * (3 * Real.log (n : ℝ) * (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) :=
                  Finset.sum_le_sum h_each_g
              _ = (∏ _s ∈ U, ∑ h ∈ nzH, ‖b_real h‖) *
                    (3 * Real.log (n : ℝ) * (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) := by
                  rw [← Finset.sum_mul]; congr 1; rw [Finset.prod_sum]
              _ ≤ 12 ^ R * (3 * 4 * C₂e) * (Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
                  have hprod_le : (∏ _s ∈ U, ∑ h ∈ nzH, ‖b_real h‖) ≤ 12 ^ R := by
                    rw [Finset.prod_const]
                    calc (∑ h ∈ nzH, ‖b_real h‖) ^ U.card ≤ 12 ^ U.card :=
                          pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) h_nz_sum_le _
                      _ ≤ 12 ^ R := pow_le_pow_right₀ (by norm_num) hU_card
                  calc (∏ _s ∈ U, ∑ h ∈ nzH, ‖b_real h‖) * (3 * Real.log (n : ℝ) * (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))))
                      ≤ 12 ^ R * (3 * Real.log (n : ℝ) * (4 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) :=
                        mul_le_mul_of_nonneg_right hprod_le (by positivity)
                    _ = 12 ^ R * (3 * 4 * C₂e) * (Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by ring
              _ ≤ 12 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ)) :=
                  mul_le_mul_of_nonneg_left h_rpow_le_inv (by positivity)
          calc ‖∑ U ∈ T.powerset.filter (·.Nonempty), ∑ p ∈ D_r, _‖
              ≤ ∑ U ∈ T.powerset.filter (·.Nonempty), ‖∑ p ∈ D_r, _‖ := norm_sum_le _ _
            _ ≤ ∑ _U ∈ T.powerset.filter (·.Nonempty), 12 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ)) :=
                Finset.sum_le_sum h_each_U
            _ = ((T.powerset.filter (·.Nonempty)).card : ℝ) * (12 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ))) := by
                simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 2 ^ R * (12 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ))) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                have h1 : (T.powerset.filter (·.Nonempty)).card ≤ T.powerset.card := Finset.card_filter_le _ _
                have h2 : T.powerset.card = 2 ^ T.card := Finset.card_powerset T
                have h3 : T.card ≤ R := le_trans (Finset.card_le_card hT_sub) hS_idx_card
                exact_mod_cast le_trans h1 (by rw [h2]; exact Nat.pow_le_pow_right (by norm_num) h3)
            _ = 24 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ)) := by rw [← mul_assoc, ← mul_pow]; norm_num; ring
      have hcard_S : ((S_idx.powerset.filter (·.Nonempty)).card : ℝ) ≤ 2 ^ R := by
        have h1 : (S_idx.powerset.filter (·.Nonempty)).card ≤ S_idx.powerset.card := Finset.card_filter_le _ _
        have h2 : S_idx.powerset.card = 2 ^ S_idx.card := Finset.card_powerset S_idx
        exact_mod_cast le_trans h1 (by rw [h2]; exact Nat.pow_le_pow_right (by norm_num) hS_idx_card)
      calc ∑ T ∈ S_idx.powerset.filter (·.Nonempty), ∑ p ∈ D_r, w_p p * ∏ s ∈ T, B_fn s p
          ≤ ∑ _T ∈ S_idx.powerset.filter (·.Nonempty),
              ((2 + 2 * Cm) * (1 / Real.log (n : ℝ)) + 24 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ))) :=
            Finset.sum_le_sum h_each_T
        _ = ((S_idx.powerset.filter (·.Nonempty)).card : ℝ) *
              ((2 + 2 * Cm) * (1 / Real.log (n : ℝ)) + 24 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ))) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 ^ R * ((2 + 2 * Cm) * (1 / Real.log (n : ℝ)) + 24 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ))) :=
            mul_le_mul_of_nonneg_right hcard_S (by positivity)
        _ = (2 ^ R * (2 + 2 * Cm) + 48 ^ R * (3 * 4 * C₂e)) * (1 / Real.log (n : ℝ)) := by
            have h2_24 : (2 : ℝ) ^ R * 24 ^ R = 48 ^ R := by rw [← mul_pow]; norm_num
            calc 2 ^ R * ((2 + 2 * Cm) * (1 / Real.log (n : ℝ)) + 24 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ)))
                = (2 ^ R * (2 + 2 * Cm) + (2 ^ R * 24 ^ R) * (3 * 4 * C₂e)) * (1 / Real.log (n : ℝ)) := by ring
              _ = (2 ^ R * (2 + 2 * Cm) + 48 ^ R * (3 * 4 * C₂e)) * (1 / Real.log (n : ℝ)) := by rw [h2_24]
    have h96 : (6 : ℝ) ^ R + 48 ^ R ≤ 96 ^ R := by
      have h6_48 : (6 : ℝ) ^ R ≤ 48 ^ R := pow_le_pow_left₀ (by norm_num) (by norm_num) R
      have h2_96 : 2 * (48 : ℝ) ^ R ≤ 96 ^ R := by
        rw [show R = 1 + (R - 1) from by omega, pow_add, pow_add, pow_one, pow_one]
        have h48_96 : (48 : ℝ) ^ (R - 1) ≤ 96 ^ (R - 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        nlinarith
      linarith
    calc |(∑ p ∈ D_r, (w_p p : ℂ) * ∏ s ∈ S_idx, a_fn s p).re|
        ≤ ‖∑ p ∈ D_r, (w_p p : ℂ) * ∏ s ∈ S_idx, a_fn s p‖ := h_abs_le
      _ ≤ 6 ^ R * (3 * 4 * C₂e) * (1 / Real.log (n : ℝ)) +
            (2 ^ R * (2 + 2 * Cm) + 48 ^ R * (3 * 4 * C₂e)) * (1 / Real.log (n : ℝ)) := by
          linarith [h_split, h_main_b, h_B_err]
      _ = (2 ^ R * (2 + 2 * Cm) + (6 ^ R + 48 ^ R) * (3 * 4 * C₂e)) * (1 / Real.log (n : ℝ)) := by ring
      _ ≤ M_inter * (1 / Real.log (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp only [M_inter]
          nlinarith


end GrasGreenbergBrocard
