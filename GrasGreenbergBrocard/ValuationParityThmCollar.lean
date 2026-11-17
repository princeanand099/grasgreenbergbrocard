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

/-! ### Theorem 2.5(ii): Collar-Decomposed Cancellation and 50–50 Split (eq. 2.16–2.17) -/

theorem collar_band_isBigO (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3)
    (r : ℕ) (hr2 : 2 ≤ r) (hrR : r ≤ Nat.floor (1 / δ)) :
    (fun n : ℕ => ∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
        p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧
        (p : ℝ) ∈ collar n r (6 * Nat.floor (1 / δ) + 30))),
      ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1)))
      =O[atTop] (fun n : ℕ => 1 / Real.log (n : ℝ)) := by
  set R := Nat.floor (1 / δ)
  set A_R := 6 * R + 30
  have hR3 : 3 ≤ R := by
    rw [Nat.le_floor_iff (by positivity)]
    rw [le_div_iff₀ hδ0]
    linarith
  obtain ⟨η', η, hη', hη, C₁e, C₂e, C₃e, hC₁e, hC₂e, hC₃e, hExp⟩ :=
    prime_exp_sum_bounds δ hδ0 hδ1
  obtain ⟨Cm, hCm_pos, hCm⟩ := mertens_sum_le
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_rpow_poly : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ (A_R + R * (R + 2) + 1) / (n : ℝ) ^ η)
      atTop (nhds 0) :=
    log_pow_div_rpow_tendsto_zero (A_R + R * (R + 2) + 1) hη
  have h_rpow_div : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ A_R / (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))))
      atTop (nhds 0) :=
    log_pow_div_rpow_tendsto_zero A_R (by positivity)
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
    rw [le_div_iff₀ (by positivity)]
    calc (Nat.sqrt n : ℝ) * (Real.log (n : ℝ)) ^ 12 ≤ Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 12 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          linarith
      _ = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
  let M_clean : ℝ := 2 ^ R * (2 + 2 * Cm) + 96 ^ R * (4 * C₃e)
  refine Asymptotics.IsBigO.of_bound M_clean ?_
  filter_upwards [Filter.eventually_ge_atTop 16, hExp, h_sqrt_12,
    hlog_inf.eventually (eventually_ge_atTop 100),
    (h_rpow_poly.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le),
    (h_rpow_div.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le)] with
    n hn hexp_n hsq12 hln100 hpoly_sm hdiv_sm
  set H := Nat.floor ((Real.log (n : ℝ)) ^ (R + 2))
  set M_r := Nat.floor ((Real.log (n : ℝ)) ^ A_R)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hH_ge1 : 1 ≤ H := by
    rw [Nat.le_floor_iff (by positivity)]
    exact_mod_cast one_le_pow₀ (by linarith : (1 : ℝ) ≤ Real.log (n : ℝ)) (n := R + 2)
  have hH_le : (H : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) := Nat.floor_le (by positivity)
  let S_r := (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
    p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ∈ collar n r A_R)
  have h_pow_R1 : ∀ p ∈ S_r, n < p ^ (R + 1) := by
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
  let J : ℕ → Finset ℕ := fun m_r =>
    S_r.filter (fun p : ℕ => (p : ℝ) ∈ collarSubinterval n r m_r A_R)
  have hS_r_part : S_r = (Finset.Icc 1 M_r).biUnion J := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_Icc, J, Finset.mem_filter]
    constructor
    · intro hp
      have hp_col := (Finset.mem_filter.mp hp).2.2.2
      obtain ⟨hp_lo, hp_hi⟩ := hp_col
      have hp_pos : (0 : ℝ) < (p : ℝ) := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; positivity
      have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
      have hpr_le_n : (p : ℝ) ^ r ≤ (n : ℝ) := by
        have := Real.rpow_le_rpow hp_pos.le hp_hi hr_pos.le
        rw [← Real.rpow_mul hn_pos.le, one_div_mul_cancel hr_pos.ne', Real.rpow_one, Real.rpow_natCast] at this
        exact this
      have hpr_gt : (n : ℝ) / (Real.log (n : ℝ)) ^ A_R < (p : ℝ) ^ r := by
        have := Real.rpow_lt_rpow (by positivity) hp_lo hr_pos
        rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hn_pos.le,
          ← Real.rpow_mul (by positivity), one_div_mul_cancel hr_pos.ne',
          div_mul_cancel₀ _ hr_pos.ne', Real.rpow_one, Real.rpow_natCast, Real.rpow_natCast] at this
        exact this
      have hdiv_ge1 : 1 ≤ n / p ^ r := by
        rw [Nat.le_div_iff_mul_le (pow_pos (Finset.mem_filter.mp hp).2.1.pos r), one_mul]
        exact_mod_cast hpr_le_n
      have hdiv_le_Mr : n / p ^ r ≤ M_r := by
        rw [Nat.le_floor_iff (by positivity)]
        have h1 : ((n / p ^ r : ℕ) : ℝ) ≤ (n : ℝ) / (p : ℝ) ^ r := by
          rw [le_div_iff₀ (by positivity)]
          exact_mod_cast Nat.div_mul_le_self n (p ^ r)
        have h2 : (n : ℝ) / (p : ℝ) ^ r < (Real.log (n : ℝ)) ^ A_R := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ (by positivity)] at hpr_gt
          linarith
        linarith
      refine ⟨n / p ^ r, ⟨hdiv_ge1, hdiv_le_Mr⟩, hp, ⟨?_, hp_col⟩⟩
      constructor
      · have h_nat : n < (n / p ^ r + 1) * p ^ r := (Nat.div_lt_iff_lt_mul (pow_pos (Finset.mem_filter.mp hp).2.1.pos r)).mp (by omega)
        have h_real : (n : ℝ) / ((n / p ^ r : ℕ) + 1 : ℝ) < (p : ℝ) ^ r := by
          rw [div_lt_iff₀ (by positivity)]
          exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((n / p ^ r + 1 : ℕ) : ℝ) * ((p ^ r : ℕ) : ℝ))
        have := Real.rpow_lt_rpow (by positivity) h_real (by positivity : 0 < 1 / (r : ℝ))
        rwa [← Real.rpow_natCast (p : ℝ) r, ← Real.rpow_mul hp_pos.le, mul_one_div_cancel hr_pos.ne', Real.rpow_one] at this
      · have h_nat : (n / p ^ r) * p ^ r ≤ n := Nat.div_mul_le_self n (p ^ r)
        have h_real : (p : ℝ) ^ r ≤ (n : ℝ) / ((n / p ^ r : ℕ) : ℝ) := by
          rw [le_div_iff₀ (by exact_mod_cast hdiv_ge1)]
          exact_mod_cast (by linarith : ((p ^ r * (n / p ^ r) : ℕ) : ℝ) ≤ (n : ℝ))
        have := Real.rpow_le_rpow (by positivity) h_real (by positivity : 0 ≤ 1 / (r : ℝ))
        rwa [← Real.rpow_natCast (p : ℝ) r, ← Real.rpow_mul hp_pos.le, mul_one_div_cancel hr_pos.ne', Real.rpow_one] at this
    · rintro ⟨m_r, _, hp, _⟩; exact hp
  have hdisj_J : (Finset.Icc 1 M_r : Set ℕ).PairwiseDisjoint J := by
    intro m₁ hm₁ m₂ hm₂ hne
    dsimp only [Function.onFun]; rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_coe, Finset.mem_Icc] at hm₁ hm₂
    simp only [J, Finset.mem_filter, collarSubinterval] at hp1 hp2
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp1.1).2.1.pos
    have h1 := Real.rpow_lt_rpow (by positivity) hp1.2.1.1 hr_pos
    have h2 := Real.rpow_le_rpow (by positivity) hp2.2.1.2 hr_pos.le
    have h3 := Real.rpow_lt_rpow (by positivity) hp2.2.1.1 hr_pos
    have h4 := Real.rpow_le_rpow (by positivity) hp1.2.1.2 hr_pos.le
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hr_pos.ne', Real.rpow_one] at h1 h2 h3 h4
    rw [← Real.rpow_natCast (p : ℝ) r, ← Real.rpow_mul hp_pos.le, mul_one_div_cancel hr_pos.ne', Real.rpow_one] at h1 h2 h3 h4
    have hm₁_pos : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast hm₁.1
    have hm₂_pos : (0 : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm₂.1
    have h12 : (n : ℝ) / ((m₁ : ℝ) + 1) < (n : ℝ) / (m₂ : ℝ) := lt_of_lt_of_le h1 h2
    have h21 : (n : ℝ) / ((m₂ : ℝ) + 1) < (n : ℝ) / (m₁ : ℝ) := lt_of_lt_of_le h3 h4
    have : m₂ < m₁ + 1 := by exact_mod_cast (by rw [div_lt_div_iff₀ (by positivity) hm₂_pos] at h12; nlinarith : (m₂ : ℝ) < (m₁ : ℝ) + 1)
    have : m₁ < m₂ + 1 := by exact_mod_cast (by rw [div_lt_div_iff₀ (by positivity) hm₁_pos] at h21; nlinarith : (m₁ : ℝ) < (m₂ : ℝ) + 1)
    omega
  have hv_on_J : ∀ m_r ∈ Finset.Icc 1 M_r, ∀ p ∈ J m_r,
      (-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1) =
        -(-1 : ℝ) ^ m_r * ∏ s ∈ Finset.Icc 1 (r - 1), (-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ) ^ s) := by
    intro m_r hm_r p hp
    have hpS := (Finset.mem_filter.mp hp).1
    have hp_pr := (Finset.mem_filter.mp hpS).2.1
    have hp_col := (Finset.mem_filter.mp hp).2
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pr.pos
    have h_v : padicValNat p (Nat.factorial n) = ∑ s ∈ Finset.Icc 1 R, n / p ^ s :=
      padicValNat_factorial_eq_sum_Icc hp_pr (h_pow_R1 p hpS)
    have h_div_mr : n / p ^ r = m_r := by
      have h1 := Real.rpow_lt_rpow (by positivity) hp_col.1.1 hr_pos
      have h2 := Real.rpow_le_rpow (by positivity) hp_col.1.2 hr_pos.le
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hr_pos.ne', Real.rpow_one] at h1 h2
      rw [← Real.rpow_natCast (p : ℝ) r, ← Real.rpow_mul hp_pos.le, mul_one_div_cancel hr_pos.ne', Real.rpow_one] at h1 h2
      have hm_pos : (0 : ℝ) < (m_r : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm_r).1
      rw [div_lt_iff₀ (by positivity)] at h1
      rw [le_div_iff₀ hm_pos] at h2
      have h_ltN : n < (m_r + 1) * p ^ r := by exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((m_r + 1 : ℕ) : ℝ) * ((p ^ r : ℕ) : ℝ))
      have h_leN : m_r * p ^ r ≤ n := by exact_mod_cast (by linarith : ((m_r * p ^ r : ℕ) : ℝ) ≤ (n : ℝ))
      have := (Nat.le_div_iff_mul_le (pow_pos hp_pr.pos r)).mpr h_leN
      have := (Nat.div_lt_iff_lt_mul (pow_pos hp_pr.pos r)).mpr h_ltN
      omega
    have h_gt_r_zero : ∀ s ∈ Finset.Icc (r + 1) R, n / p ^ s = 0 := by
      intro s hs
      have hs1 : r + 1 ≤ s := (Finset.mem_Icc.mp hs).1
      apply Nat.div_eq_of_lt
      have h_lt_n : (n : ℝ) < (p : ℝ) ^ (r + 1) := by
        have h_col_lo := hp_col.2.1
        have h_gap : (n : ℝ) ^ (1 / ((r : ℝ) + 1)) < (n : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)) := by
          rw [lt_div_iff₀ (by positivity)]
          have hpow_gt : (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)) ≤ (Real.log (n : ℝ)) ^ A_R := by
            rw [← Real.rpow_natCast (Real.log (n : ℝ)) A_R]
            apply Real.rpow_le_rpow_of_exponent_le (by linarith)
            exact div_le_self (by positivity) (by exact_mod_cast (by omega : 1 ≤ r))
          have h1 : (Real.log (n : ℝ)) ^ A_R < (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) := by
            have := (div_lt_iff₀ (by positivity)).mp hdiv_sm
            linarith
          have h2 : (n : ℝ) ^ (1 / ((r : ℝ) + 1)) * (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) = (n : ℝ) ^ (1 / (r : ℝ)) := by
            rw [← Real.rpow_add hn_pos]
            congr 1; field_simp [hr_pos.ne', by positivity : (r : ℝ) + 1 ≠ 0]; ring
          nlinarith [Real.rpow_pos_of_pos hn_pos (1 / ((r : ℝ) + 1))]
        have hlt_p := lt_trans h_gap h_col_lo
        have := Real.rpow_lt_rpow (by positivity) hlt_p (by positivity : (0 : ℝ) < (r : ℝ) + 1)
        rw [← Real.rpow_mul hn_pos.le, one_div_mul_cancel (by positivity : (r : ℝ) + 1 ≠ 0), Real.rpow_one,
          ← Real.rpow_natCast (p : ℝ) (r + 1)] at this
        exact this
      have h_le_s : (p : ℝ) ^ (r + 1) ≤ (p : ℝ) ^ s := pow_le_pow_right₀ (by exact_mod_cast hp_pr.one_lt.le) hs1
      exact_mod_cast lt_of_lt_of_le h_lt_n h_le_s
    have h_sum_split : ∑ s ∈ Finset.Icc 1 R, n / p ^ s =
        (∑ s ∈ Finset.Icc 1 (r - 1), n / p ^ s) + m_r := by
      have h1 : Finset.Icc 1 R = Finset.Icc 1 r ∪ Finset.Icc (r + 1) R := by
        ext s; simp only [Finset.mem_union, Finset.mem_Icc]; omega
      have h2 : Disjoint (Finset.Icc 1 r) (Finset.Icc (r + 1) R) := by
        rw [Finset.disjoint_left]; intro s hs1 hs2
        simp only [Finset.mem_Icc] at hs1 hs2; omega
      rw [h1, Finset.sum_union h2, Finset.sum_eq_zero h_gt_r_zero, add_zero]
      rw [show r = (r - 1) + 1 from by omega, Finset.sum_Icc_succ_top (by omega : 1 ≤ r), h_div_mr]
    have hv_pos : 1 ≤ padicValNat p (Nat.factorial n) := by rw [h_v, h_sum_split]; omega
    have hpow_neg : (-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1) =
        -((-1 : ℝ) ^ padicValNat p (Nat.factorial n)) := by
      have : padicValNat p (Nat.factorial n) = (padicValNat p (Nat.factorial n) - 1) + 1 := by omega
      conv_rhs => rw [this, pow_succ]
      ring
    rw [hpow_neg, h_v, h_sum_split, pow_add, ← Finset.prod_pow_eq_pow_sum]
    have h_fl_eq : ∏ s ∈ Finset.Icc 1 (r - 1), (-1 : ℝ) ^ (n / p ^ s) =
        ∏ s ∈ Finset.Icc 1 (r - 1), (-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ) ^ s) := by
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
    rw [h_fl_eq]
    ring
  obtain ⟨c_tilde, b_tilde, h_supp, h_ctilde_b, h_btilde0, h_btilde_b, h_vaaler_pw, h_L1⟩ :=
    vaaler_parity_approx H hH_ge1
  let allH := Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)
  let oddH := allH.filter (fun h => h ≠ 0 ∧ Odd h)
  let nzH := allH.filter (· ≠ 0)
  let b_real : ℤ → ℂ := fun h => (1 / 2 : ℂ) * (b_tilde h + star (b_tilde (-h)))
  have hb_real_0 : b_real 0 = ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) := by
    dsimp only [b_real]
    rw [neg_zero, h_btilde0]
    apply Complex.ext <;> simp <;> norm_cast
  have hb_real_norm : ∀ h : ℤ, ‖b_real h‖ ≤ 3 / ((H : ℝ) + 1) := by
    intro h
    dsimp only [b_real]
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 from by norm_num]
    have h1 := h_btilde_b h
    have h2 : ‖star (b_tilde (-h))‖ ≤ 3 / ((H : ℝ) + 1) := by
      rw [norm_star]; exact (h_btilde_b (-h)).le
    linarith [norm_add_le (b_tilde h) (star (b_tilde (-h)))]
  have h_J_exp : ∀ (m_r : ℕ) (hm_r : m_r ∈ Finset.Icc 1 M_r) (A : Finset ℕ) (hA_sub : A ⊆ Finset.Icc 1 (r - 1))
      (h_fn : ℕ → ℤ) (hA_nz : ∃ s ∈ A, h_fn s ≠ 0) (hh_le : ∀ s ∈ A, |h_fn s| ≤ 2 * (H : ℤ) + 1),
      ‖∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
          eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s))‖ ≤
        4 * C₃e * (n : ℝ) ^ (-η) := by
    intro m_r hm_r A hA_sub h_fn hA_nz hh_le
    rcases eq_or_ne (J m_r) ∅ with h_emp | h_ne
    · rw [h_emp, Finset.sum_empty, norm_zero]; positivity
    · let P := max ((n : ℝ) ^ δ) (((n : ℝ) / ((m_r : ℝ) + 1)) ^ (1 / (r : ℝ)))
      have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
      have hm_pos : (0 : ℝ) < (m_r : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm_r).1
      have hP_lo : (n : ℝ) ^ δ ≤ P := le_max_left _ _
      have hP_pos : 0 < P := lt_of_lt_of_le (by positivity) hP_lo
      have hP_le_n1r : P ≤ (n : ℝ) ^ (1 / (r : ℝ)) := by
        apply max_le
        · apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
          rw [le_div_iff₀ hr_pos]
          have : (r : ℝ) ≤ 1 / δ := (Nat.le_floor_iff (by positivity)).mp hrR
          nlinarith [(div_le_iff₀ hδ0).mp this]
        · apply Real.rpow_le_rpow (by positivity) _ (by positivity)
          exact div_le_self hn_pos.le (by linarith)
      have hP_hi : P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := by
        obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr h_ne
        have hp0_S := (Finset.mem_filter.mp hp0).1
        have hp0_col := (Finset.mem_filter.mp hp0).2
        have hp0_le_sq : (p0 : ℝ) ≤ (Nat.sqrt n : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp0_S).1).2
        have hp0_gt_lo : ((n : ℝ) / ((m_r : ℝ) + 1)) ^ (1 / (r : ℝ)) < (p0 : ℝ) := hp0_col.1.1
        have hp0_gt_d : (n : ℝ) ^ δ < (p0 : ℝ) := (Finset.mem_filter.mp hp0_S).2.2.1
        have hP_lt_p0 : P < (p0 : ℝ) := max_lt hp0_gt_d hp0_gt_lo
        linarith [hsq12]
      have hJ_pr : ∀ p ∈ J m_r, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P := by
        intro p hp
        have hpS := (Finset.mem_filter.mp hp).1
        have hp_col := (Finset.mem_filter.mp hp).2
        refine ⟨(Finset.mem_filter.mp hpS).2.1, max_lt (Finset.mem_filter.mp hpS).2.2.1 hp_col.1.1, ?_⟩
        calc (p : ℝ) ≤ ((n : ℝ) / (m_r : ℝ)) ^ (1 / (r : ℝ)) := hp_col.1.2
          _ = (((m_r : ℝ) + 1) / (m_r : ℝ)) ^ (1 / (r : ℝ)) *
                (((n : ℝ) / ((m_r : ℝ) + 1)) ^ (1 / (r : ℝ))) := by
              rw [← Real.mul_rpow (by positivity) (by positivity)]
              congr 1; field_simp [hm_pos.ne']
          _ ≤ 2 * (((n : ℝ) / ((m_r : ℝ) + 1)) ^ (1 / (r : ℝ))) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              calc (((m_r : ℝ) + 1) / (m_r : ℝ)) ^ (1 / (r : ℝ))
                  ≤ (2 : ℝ) ^ (1 / (r : ℝ)) := by
                    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
                    rw [div_le_iff₀ hm_pos]
                    have : (1 : ℝ) ≤ (m_r : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm_r).1
                    linarith
                _ ≤ 2 := by
                    calc (2 : ℝ) ^ (1 / (r : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                          Real.rpow_le_rpow_of_exponent_le (by norm_num) (div_le_self (by norm_num) (by exact_mod_cast (by omega : 1 ≤ r)))
                      _ = 2 := Real.rpow_one _
          _ ≤ 2 * P := mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
      have hA_range : ∀ s ∈ A, 1 ≤ s ∧ s ≤ R := by
        intro s hs
        have := Finset.mem_Icc.mp (hA_sub hs)
        omega
      have h_log_nδ : (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) ^ δ := by
        have h1 : (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) := by
          have := (div_lt_iff₀ (by positivity)).mp hdiv_sm
          linarith
        have h2 : 1 / ((r : ℝ) * ((r : ℝ) + 1)) ≤ δ := by
          have h_1R1_d : 1 / ((R : ℝ) + 1) < δ := by
            rw [div_lt_iff₀ (by positivity)]
            have := Nat.lt_floor_add_one (1 / δ)
            nlinarith [(div_lt_iff₀ hδ0).mp this]
          have h_rr1 : 1 / ((r : ℝ) * ((r : ℝ) + 1)) ≤ 1 / ((R : ℝ) + 1) := by
            apply one_div_le_one_div_of_le (by positivity)
            have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
            have hrR' : (r : ℝ) ≤ (R : ℝ) := by exact_mod_cast hrR
            nlinarith
          linarith
        exact le_trans h1 (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) h2)
      have hPhase : ∀ s ∈ A, (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) / P ^ s := by
        intro s hs
        have hs_mem := Finset.mem_Icc.mp (hA_sub hs)
        have hPs_le : P ^ s ≤ (n : ℝ) ^ ((s : ℝ) / (r : ℝ)) := by
          calc P ^ s ≤ ((n : ℝ) ^ (1 / (r : ℝ))) ^ s := pow_le_pow_left₀ hP_pos.le hP_le_n1r s
            _ = (n : ℝ) ^ ((s : ℝ) / (r : ℝ)) := by
                rw [← Real.rpow_natCast _ s, ← Real.rpow_mul hn_pos.le]; congr 1; ring
        have h_n_div : (n : ℝ) ^ (1 - (s : ℝ) / (r : ℝ)) ≤ (n : ℝ) / P ^ s := by
          calc (n : ℝ) ^ (1 - (s : ℝ) / (r : ℝ)) = (n : ℝ) / (n : ℝ) ^ ((s : ℝ) / (r : ℝ)) := by
                rw [Real.rpow_sub hn_pos, Real.rpow_one]
            _ ≤ (n : ℝ) / P ^ s := div_le_div_of_nonneg_left hn_pos.le (by positivity) hPs_le
        have h_exp_ge : (n : ℝ) ^ δ ≤ (n : ℝ) ^ (1 - (s : ℝ) / (r : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
          have hs_le : (s : ℝ) ≤ (r : ℝ) - 1 := by exact_mod_cast (by omega : s ≤ r - 1)
          have h1 : 1 / (r : ℝ) ≤ 1 - (s : ℝ) / (r : ℝ) := by
            rw [le_sub_iff_add_le, ← add_div, div_le_one hr_pos]
            linarith
          have h_d_1r : δ ≤ 1 / (r : ℝ) := by
            rw [le_div_iff₀ hr_pos]
            have : (r : ℝ) ≤ 1 / δ := (Nat.le_floor_iff (by positivity)).mp hrR
            nlinarith [(div_le_iff₀ hδ0).mp this]
          linarith
        have h2R_le1 : (2 : ℝ) ^ (-(R : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
        calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ 1 * (Real.log (n : ℝ)) ^ A_R :=
              mul_le_mul_of_nonneg_right h2R_le1 (by positivity)
          _ = (Real.log (n : ℝ)) ^ A_R := one_mul _
          _ ≤ (n : ℝ) ^ δ := h_log_nδ
          _ ≤ (n : ℝ) ^ (1 - (s : ℝ) / (r : ℝ)) := h_exp_ge
          _ ≤ (n : ℝ) / P ^ s := h_n_div
      have hP_ge2 : 2 ≤ P := by
        have : (2 : ℝ) ≤ (Real.log (n : ℝ)) ^ A_R := by
          have := one_le_pow₀ (by linarith : (1 : ℝ) ≤ Real.log (n : ℝ)) (n := A_R - 1)
          have hA1 : 1 ≤ A_R := by omega
          have hpow : (Real.log (n : ℝ)) ^ A_R = Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (A_R - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel hA1]
          nlinarith
        linarith
      have hW_b : ∀ t ∈ Set.Icc P (2 * P), |1 / (t - 1)| ≤ 2 / P := by
        intro t ht
        have ht1 : 0 < t - 1 := by linarith [ht.1]
        rw [abs_of_pos (one_div_pos.mpr ht1)]
        exact one_div_le_div_of_le (by positivity) (by linarith [ht.1])
      have hexp_app := hexp_n P (J m_r) A h_fn (fun t => 1 / (t - 1)) (2 / P)
        hA_nz hP_lo hP_hi hJ_pr hA_range hh_le hPhase hW_b (by positivity)
      dsimp only at hexp_app
      have hT₀_ge : (n : ℝ) ^ (δ / 2) ≤ |(h_fn ((A.filter (fun s => h_fn s ≠ 0)).min' _ : ℕ) : ℝ)| * (n : ℝ) /
          P ^ ((A.filter (fun s => h_fn s ≠ 0)).min' _) := by
        set r₀ := (A.filter (fun s => h_fn s ≠ 0)).min' (by
          obtain ⟨s, hsA, hs0⟩ := hA_nz; exact ⟨s, Finset.mem_filter.mpr ⟨hsA, hs0⟩⟩)
        have hr₀_flt := Finset.min'_mem (A.filter (fun s => h_fn s ≠ 0)) _
        have hr₀_mem : r₀ ∈ A := (Finset.mem_filter.mp hr₀_flt).1
        have hr₀_ne : h_fn r₀ ≠ 0 := (Finset.mem_filter.mp hr₀_flt).2
        have hh1 : (1 : ℝ) ≤ |(h_fn r₀ : ℝ)| := by exact_mod_cast Int.one_le_abs hr₀_ne
        have hr₀_le : r₀ ≤ r - 1 := (Finset.mem_Icc.mp (hA_sub hr₀_mem)).2
        have hPr₀ : P ^ r₀ ≤ (n : ℝ) ^ ((r₀ : ℝ) / (r : ℝ)) := by
          calc P ^ r₀ ≤ ((n : ℝ) ^ (1 / (r : ℝ))) ^ r₀ := pow_le_pow_left₀ hP_pos.le hP_le_n1r r₀
            _ = (n : ℝ) ^ ((r₀ : ℝ) / (r : ℝ)) := by
                rw [← Real.rpow_natCast _ r₀, ← Real.rpow_mul hn_pos.le]; congr 1; ring
        have h_n_div : (n : ℝ) ^ δ ≤ (n : ℝ) / P ^ r₀ := by
          have h1 : 1 - (r₀ : ℝ) / (r : ℝ) ≥ 1 / (r : ℝ) := by
            have : (r₀ : ℝ) ≤ (r : ℝ) - 1 := by exact_mod_cast hr₀_le
            rw [ge_iff_le, le_sub_iff_add_le, ← add_div, div_le_one hr_pos]; linarith
          have h2 : δ ≤ 1 / (r : ℝ) := by
            rw [le_div_iff₀ hr_pos]
            have : (r : ℝ) ≤ 1 / δ := (Nat.le_floor_iff (by positivity)).mp hrR
            nlinarith [(div_le_iff₀ hδ0).mp this]
          calc (n : ℝ) ^ δ ≤ (n : ℝ) ^ (1 - (r₀ : ℝ) / (r : ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (le_trans h2 h1)
            _ = (n : ℝ) / (n : ℝ) ^ ((r₀ : ℝ) / (r : ℝ)) := by rw [Real.rpow_sub hn_pos, Real.rpow_one]
            _ ≤ (n : ℝ) / P ^ r₀ := div_le_div_of_nonneg_left hn_pos.le (by positivity) hPr₀
        have h_nδ_half : (n : ℝ) ^ (δ / 2) ≤ (n : ℝ) ^ δ :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
        calc (n : ℝ) ^ (δ / 2) ≤ (n : ℝ) ^ δ := h_nδ_half
          _ ≤ (n : ℝ) / P ^ r₀ := h_n_div
          _ = 1 * ((n : ℝ) / P ^ r₀) := (one_mul _).symm
          _ ≤ |(h_fn r₀ : ℝ)| * ((n : ℝ) / P ^ r₀) := mul_le_mul_of_nonneg_right hh1 (by positivity)
          _ = |(h_fn r₀ : ℝ)| * (n : ℝ) / P ^ r₀ := by ring
      have h_app2 := hexp_app.2 hT₀_ge
      have hP_cancel : C₃e * (2 / P) * P * (n : ℝ) ^ (-η) ≤ 4 * C₃e * (n : ℝ) ^ (-η) := by
        have hP_ne : P ≠ 0 := hP_pos.ne'
        calc C₃e * (2 / P) * P * (n : ℝ) ^ (-η) = 2 * C₃e * (n : ℝ) ^ (-η) := by field_simp [hP_ne]
          _ ≤ 4 * C₃e * (n : ℝ) ^ (-η) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              linarith [hC₃e]
      have hsum_eq : ∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
            eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s)) =
          ∑ p ∈ J m_r, ((1 / ((p : ℝ) - 1) * Real.log (p : ℝ) : ℝ) : ℂ) *
            eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        congr 2; ring
      rw [hsum_eq]
      exact le_trans h_app2 hP_cancel
  let a_fn : ℕ → ℕ → ℂ := fun s p => (((-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) : ℂ)
  let b_fn : ℕ → ℕ → ℂ := fun s p =>
    ∑ h ∈ oddH, c_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / 2)
  let B_fn : ℕ → ℕ → ℝ := fun s p =>
    (∑ h ∈ allH, b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / 2)).re
  have ha_norm : ∀ s p, ‖a_fn s p‖ = 1 := fun s p => by
    dsimp only [a_fn]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_zpow, abs_neg, abs_one, one_zpow]
  have hB_pw : ∀ s p, ‖a_fn s p - b_fn s p‖ ≤ B_fn s p := fun s p => by
    dsimp only [a_fn, b_fn, B_fn]
    exact (h_vaaler_pw ((n : ℝ) / (p : ℝ) ^ s)).2
  let S_idx := Finset.Icc 1 (r - 1)
  have hS_idx_ne : S_idx.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hS_idx_card : S_idx.card ≤ R := by
    rw [Nat.card_Icc]; omega
  have h_prod_J : ∀ m_r ∈ Finset.Icc 1 M_r,
      ‖∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) * ∏ s ∈ S_idx, a_fn s p‖ ≤
      (∑ T ∈ S_idx.powerset.filter (·.Nonempty),
        (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, Real.log (p : ℝ) / ((p : ℝ) - 1)) +
      96 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) := by
    intro m_r hm_r
    let w_p : ℕ → ℝ := fun p => Real.log (p : ℝ) / ((p : ℝ) - 1)
    have hw_nn : ∀ p ∈ J m_r, 0 ≤ w_p p := fun p hp => by
      have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
      exact div_nonneg hlogp hp1.le
    have h_split : ‖∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ S_idx, a_fn s p‖ ≤
        ‖∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ S_idx, b_fn s p‖ +
        ∑ p ∈ J m_r, w_p p * ∑ T ∈ S_idx.powerset.filter (·.Nonempty), ∏ s ∈ T, B_fn s p := by
      have hid : ∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ S_idx, a_fn s p =
          (∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ S_idx, b_fn s p) +
          ∑ p ∈ J m_r, (w_p p : ℂ) * (∏ s ∈ S_idx, a_fn s p - ∏ s ∈ S_idx, b_fn s p) := by
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
    have h_main_b : ‖∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ S_idx, b_fn s p‖ ≤
        6 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) := by
      have h_prod_exp : ∀ p ∈ J m_r,
          ∏ s ∈ S_idx, b_fn s p =
            ∑ g ∈ Fintype.piFinset (fun _ : S_idx => oddH),
              (∏ s : S_idx, c_tilde (g s)) *
                eExp (∑ s ∈ S_idx, (if hs : s ∈ S_idx then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
        intro p _
        dsimp only [b_fn]
        rw [← Finset.prod_coe_sort S_idx]
        rw [Fintype.prod_sum (fun (s : S_idx) (h : ℤ) => c_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ) ^ (s : ℕ)) / 2)) (fun _ => oddH)]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [Finset.prod_mul_distrib, eExp_sum]
        congr 2
        rw [← Finset.sum_coe_sort S_idx]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        simp only [s.2, ↓reduceDIte]
        ring
      rw [Finset.sum_congr rfl (fun p hp => by rw [h_prod_exp p hp, Finset.mul_sum])]
      rw [Finset.sum_comm]
      have h_each_g : ∀ g ∈ Fintype.piFinset (fun _ : S_idx => oddH),
          ‖∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s : S_idx, c_tilde (g s)) *
            eExp (∑ s ∈ S_idx, (if hs : s ∈ S_idx then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s)))‖ ≤
          (∏ s : S_idx, ‖c_tilde (g s)‖) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
        intro g hg
        have hpull : ∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s : S_idx, c_tilde (g s)) *
              eExp (∑ s ∈ S_idx, (if hs : s ∈ S_idx then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s))) =
            (∏ s : S_idx, c_tilde (g s)) * ∑ p ∈ J m_r, (w_p p : ℂ) *
              eExp (∑ s ∈ S_idx, (if hs : s ∈ S_idx then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p _ => by ring)
        rw [hpull, norm_mul, norm_prod]
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
        have hg_mem : ∀ s : S_idx, g s ∈ oddH := fun s => Fintype.mem_piFinset.mp hg s
        obtain ⟨s0, hs0⟩ := hS_idx_ne
        have hnz : ∃ s ∈ S_idx, (if hs : s ∈ S_idx then g ⟨s, hs⟩ else 0) ≠ 0 := by
          refine ⟨s0, hs0, ?_⟩
          simp only [hs0, ↓reduceDIte]
          exact (Finset.mem_filter.mp (hg_mem ⟨s0, hs0⟩)).2.1
        have hle : ∀ s ∈ S_idx, |if hs : s ∈ S_idx then g ⟨s, hs⟩ else 0| ≤ 2 * (H : ℤ) + 1 := by
          intro s hs
          simp only [hs, ↓reduceDIte]
          have := Finset.mem_Icc.mp (Finset.mem_filter.mp (hg_mem ⟨s, hs⟩)).1
          rw [abs_le]; omega
        exact h_J_exp m_r hm_r S_idx le_rfl (fun s => if hs : s ∈ S_idx then g ⟨s, hs⟩ else 0) hnz hle
      calc ‖∑ g ∈ Fintype.piFinset (fun _ : S_idx => oddH), ∑ p ∈ J m_r, _‖
          ≤ ∑ g ∈ Fintype.piFinset (fun _ : S_idx => oddH), ‖∑ p ∈ J m_r, _‖ := norm_sum_le _ _
        _ ≤ ∑ g ∈ Fintype.piFinset (fun _ : S_idx => oddH),
              (∏ s : S_idx, ‖c_tilde (g s)‖) * (4 * C₃e * (n : ℝ) ^ (-η)) :=
            Finset.sum_le_sum h_each_g
        _ = (∑ g ∈ Fintype.piFinset (fun _ : S_idx => oddH), ∏ s : S_idx, ‖c_tilde (g s)‖) *
              (4 * C₃e * (n : ℝ) ^ (-η)) := by rw [← Finset.sum_mul]
        _ = (∏ _s : S_idx, ∑ h ∈ oddH, ‖c_tilde h‖) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
            congr 1
            exact (Fintype.prod_sum (fun (_s : S_idx) (h : ℤ) => ‖c_tilde h‖) (fun _ => oddH)).symm
        _ ≤ ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ S_idx.card * (4 * C₃e * (n : ℝ) ^ (-η)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
            exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) h_L1 _
        _ ≤ (6 * (Real.log (n : ℝ)) ^ (R + 2)) ^ R * (4 * C₃e * (n : ℝ) ^ (-η)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hL1_le : (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1) ≤ 6 * (Real.log (n : ℝ)) ^ (R + 2) := by
              have h4pi : 4 / Real.pi ≤ 2 := by
                rw [div_le_iff₀ Real.pi_pos]
                linarith [Real.pi_gt_three]
              have hlog_le : Real.log (2 * (H : ℝ) + 1) + 1 ≤ 3 * (Real.log (n : ℝ)) ^ (R + 2) := by
                have h1 : Real.log (2 * (H : ℝ) + 1) ≤ 2 * (H : ℝ) := by
                  linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * (H : ℝ) + 1)]
                have h2 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) := one_le_pow₀ (by linarith)
                linarith
              nlinarith
            have h6_ge1 : (1 : ℝ) ≤ 6 * (Real.log (n : ℝ)) ^ (R + 2) := by
              have : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) := one_le_pow₀ (by linarith)
              linarith
            calc ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ S_idx.card
                ≤ (6 * (Real.log (n : ℝ)) ^ (R + 2)) ^ S_idx.card :=
                  pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hL1_le _
              _ ≤ (6 * (Real.log (n : ℝ)) ^ (R + 2)) ^ R :=
                  pow_le_pow_right₀ h6_ge1 hS_idx_card
        _ = 6 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) := by
            rw [mul_pow, ← pow_mul]
            ring
    have h_B_err : ∑ p ∈ J m_r, w_p p * ∑ T ∈ S_idx.powerset.filter (·.Nonempty), ∏ s ∈ T, B_fn s p ≤
        (∑ T ∈ S_idx.powerset.filter (·.Nonempty),
          (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p) +
        48 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) := by
      rw [Finset.sum_congr rfl (fun p _ => Finset.mul_sum _ _ _)]
      rw [Finset.sum_comm]
      have h_each_T : ∀ T ∈ S_idx.powerset.filter (·.Nonempty),
          ∑ p ∈ J m_r, w_p p * ∏ s ∈ T, B_fn s p ≤
            (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p +
            24 ^ R * (4 * C₃e * (n : ℝ) ^ (-η)) := by
        intro T hT
        have hT_sub : T ⊆ S_idx := (Finset.mem_filter.mp hT).1
        let Z : ℕ → ℕ → ℂ := fun s p =>
          ∑ h ∈ nzH, b_real h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / 2)
        have hB_eq_C : ∀ s p, (B_fn s p : ℂ) = Z s p + ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) := by
          intro s p
          dsimp only [B_fn]
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
          rw [h0_term, h_nz_eq, add_comm]
          rfl
        have h_re_eq : ∑ p ∈ J m_r, w_p p * ∏ s ∈ T, B_fn s p =
            (∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ T, (Z s p + ((2 / ((H : ℝ) + 1) : ℝ) : ℂ))).re := by
          rw [Complex.re_sum]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          have hprod_C : ∏ s ∈ T, (Z s p + ((2 / ((H : ℝ) + 1) : ℝ) : ℂ)) =
              ((∏ s ∈ T, B_fn s p : ℝ) : ℂ) := by
            push_cast
            exact Finset.prod_congr rfl (fun s _ => (hB_eq_C s p).symm)
          rw [hprod_C, ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [h_re_eq]
        refine le_trans (Complex.re_le_abs _) ?_
        rw [← Complex.norm_eq_abs]
        have h_prod_T : ∀ p ∈ J m_r,
            ∏ s ∈ T, (Z s p + ((2 / ((H : ℝ) + 1) : ℝ) : ℂ)) =
              ∑ U ∈ T.powerset, (∏ s ∈ U, Z s p) * ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ U).card := by
          intro p _
          rw [Finset.prod_add]
          refine Finset.sum_congr rfl (fun U _ => ?_)
          rw [Finset.prod_const]
        rw [Finset.sum_congr rfl (fun p hp => by rw [h_prod_T p hp, Finset.mul_sum])]
        rw [Finset.sum_comm]
        have hU_split : T.powerset = insert ∅ (T.powerset.filter (·.Nonempty)) := by
          ext U
          simp only [Finset.mem_insert, Finset.mem_powerset, Finset.mem_filter]
          constructor
          · intro hU
            rcases Finset.eq_empty_or_nonempty U with rfl | hne
            · left; rfl
            · right; exact ⟨hU, hne⟩
          · rintro (rfl | ⟨hU, _⟩)
            · exact Finset.empty_subset _
            · exact hU
        have hnot_emp : (∅ : Finset ℕ) ∉ T.powerset.filter (·.Nonempty) := by
          simp [Finset.not_nonempty_empty]
        rw [hU_split, Finset.sum_insert hnot_emp]
        refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
        · have h_emp_eq : ∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s ∈ (∅ : Finset ℕ), Z s p) *
                ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ ∅).card) =
              (((2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p : ℝ) : ℂ) := by
            simp only [Finset.prod_empty, one_mul, Finset.sdiff_empty]
            push_cast
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun p _ => by ring)
          rw [h_emp_eq, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg hw_nn))]
        · have h_each_U : ∀ U ∈ T.powerset.filter (·.Nonempty),
              ‖∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s ∈ U, Z s p) *
                ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ U).card)‖ ≤
              12 ^ R * (4 * C₃e * (n : ℝ) ^ (-η)) := by
            intro U hU
            have hU_sub : U ⊆ S_idx := Finset.Subset.trans (Finset.mem_filter.mp hU).1 hT_sub
            have hU_ne : U.Nonempty := (Finset.mem_filter.mp hU).2
            have hU_card : U.card ≤ R := le_trans (Finset.card_le_card hU_sub) hS_idx_card
            have hpull : ∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s ∈ U, Z s p) *
                  ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ U).card) =
                ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ U).card *
                  ∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ U, Z s p := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun p _ => by ring)
            rw [hpull, norm_mul, norm_pow, Complex.norm_real,
              Real.norm_of_nonneg (by positivity : 0 ≤ 2 / ((H : ℝ) + 1))]
            have h_pow_le1 : (2 / ((H : ℝ) + 1)) ^ (T \ U).card ≤ 1 := by
              apply pow_le_one₀ (by positivity)
              rw [div_le_one (by positivity)]
              have : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH_ge1
              linarith
            refine le_trans (mul_le_mul_of_nonneg_right h_pow_le1 (norm_nonneg _)) ?_
            rw [one_mul]
            have hZ_exp : ∀ p ∈ J m_r,
                ∏ s ∈ U, Z s p =
                  ∑ g ∈ Fintype.piFinset (fun _ : U => nzH),
                    (∏ s : U, b_real (g s)) *
                      eExp (∑ s ∈ U, (if hs : s ∈ U then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
              intro p _
              dsimp only [Z]
              rw [← Finset.prod_coe_sort U]
              rw [Fintype.prod_sum (fun (s : U) (h : ℤ) => b_real h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ) ^ (s : ℕ)) / 2)) (fun _ => nzH)]
              refine Finset.sum_congr rfl (fun g _ => ?_)
              rw [Finset.prod_mul_distrib, eExp_sum]
              congr 2
              rw [← Finset.sum_coe_sort U]
              refine Finset.sum_congr rfl (fun s _ => ?_)
              simp only [s.2, ↓reduceDIte]
              ring
            rw [Finset.sum_congr rfl (fun p hp => by rw [hZ_exp p hp, Finset.mul_sum])]
            rw [Finset.sum_comm]
            have h_each_g : ∀ g ∈ Fintype.piFinset (fun _ : U => nzH),
                ‖∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s : U, b_real (g s)) *
                  eExp (∑ s ∈ U, (if hs : s ∈ U then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s)))‖ ≤
                (∏ s : U, ‖b_real (g s)‖) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
              intro g hg
              have hpull_g : ∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s : U, b_real (g s)) *
                    eExp (∑ s ∈ U, (if hs : s ∈ U then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s))) =
                  (∏ s : U, b_real (g s)) * ∑ p ∈ J m_r, (w_p p : ℂ) *
                    eExp (∑ s ∈ U, (if hs : s ∈ U then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun p _ => by ring)
              rw [hpull_g, norm_mul, norm_prod]
              apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
              have hg_mem : ∀ s : U, g s ∈ nzH := fun s => Fintype.mem_piFinset.mp hg s
              obtain ⟨s0, hs0⟩ := hU_ne
              have hnz : ∃ s ∈ U, (if hs : s ∈ U then g ⟨s, hs⟩ else 0) ≠ 0 := by
                refine ⟨s0, hs0, ?_⟩
                simp only [hs0, ↓reduceDIte]
                exact (Finset.mem_filter.mp (hg_mem ⟨s0, hs0⟩)).2
              have hle : ∀ s ∈ U, |if hs : s ∈ U then g ⟨s, hs⟩ else 0| ≤ 2 * (H : ℤ) + 1 := by
                intro s hs
                simp only [hs, ↓reduceDIte]
                have := Finset.mem_Icc.mp (Finset.mem_filter.mp (hg_mem ⟨s, hs⟩)).1
                rw [abs_le]; omega
              exact h_J_exp m_r hm_r U hU_sub (fun s => if hs : s ∈ U then g ⟨s, hs⟩ else 0) hnz hle
            have h_nz_sum_le : ∑ h ∈ nzH, ‖b_real h‖ ≤ 12 := by
              have hnz_card : (nzH.card : ℝ) ≤ 4 * (H : ℝ) + 3 := by
                have h1 : nzH.card ≤ allH.card := Finset.card_filter_le _ _
                have h2 : allH.card = 4 * H + 3 := by dsimp only [allH]; rw [Int.card_Icc]; omega
                exact_mod_cast le_trans h1 h2.le
              calc ∑ h ∈ nzH, ‖b_real h‖ ≤ ∑ _h ∈ nzH, (3 / ((H : ℝ) + 1)) :=
                    Finset.sum_le_sum (fun h _ => hb_real_norm h)
                _ = (nzH.card : ℝ) * (3 / ((H : ℝ) + 1)) := by simp [Finset.sum_const, nsmul_eq_mul]
                _ ≤ (4 * (H : ℝ) + 3) * (3 / ((H : ℝ) + 1)) :=
                    mul_le_mul_of_nonneg_right hnz_card (by positivity)
                _ ≤ 12 := by
                    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
                    linarith
            calc ‖∑ g ∈ Fintype.piFinset (fun _ : U => nzH), ∑ p ∈ J m_r, _‖
                ≤ ∑ g ∈ Fintype.piFinset (fun _ : U => nzH), ‖∑ p ∈ J m_r, _‖ := norm_sum_le _ _
              _ ≤ ∑ g ∈ Fintype.piFinset (fun _ : U => nzH),
                    (∏ s : U, ‖b_real (g s)‖) * (4 * C₃e * (n : ℝ) ^ (-η)) :=
                  Finset.sum_le_sum h_each_g
              _ = (∑ g ∈ Fintype.piFinset (fun _ : U => nzH), ∏ s : U, ‖b_real (g s)‖) *
                    (4 * C₃e * (n : ℝ) ^ (-η)) := by rw [← Finset.sum_mul]
              _ = (∏ _s : U, ∑ h ∈ nzH, ‖b_real h‖) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
                  congr 1
                  exact (Fintype.prod_sum (fun (_s : U) (h : ℤ) => ‖b_real h‖) (fun _ => nzH)).symm
              _ ≤ 12 ^ U.card * (4 * C₃e * (n : ℝ) ^ (-η)) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
                  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) h_nz_sum_le _
              _ ≤ 12 ^ R * (4 * C₃e * (n : ℝ) ^ (-η)) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact pow_le_pow_right₀ (by norm_num) hU_card
          calc ‖∑ U ∈ T.powerset.filter (·.Nonempty), ∑ p ∈ J m_r, _‖
              ≤ ∑ U ∈ T.powerset.filter (·.Nonempty), ‖∑ p ∈ J m_r, _‖ := norm_sum_le _ _
            _ ≤ ∑ _U ∈ T.powerset.filter (·.Nonempty), 12 ^ R * (4 * C₃e * (n : ℝ) ^ (-η)) :=
                Finset.sum_le_sum h_each_U
            _ = ((T.powerset.filter (·.Nonempty)).card : ℝ) * (12 ^ R * (4 * C₃e * (n : ℝ) ^ (-η))) := by
                simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 2 ^ R * (12 ^ R * (4 * C₃e * (n : ℝ) ^ (-η))) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                have h1 : (T.powerset.filter (·.Nonempty)).card ≤ T.powerset.card := Finset.card_filter_le _ _
                have h2 : T.powerset.card = 2 ^ T.card := Finset.card_powerset T
                have h3 : T.card ≤ R := le_trans (Finset.card_le_card hT_sub) hS_idx_card
                have h4 : (2 : ℕ) ^ T.card ≤ 2 ^ R := Nat.pow_le_pow_right (by norm_num) h3
                exact_mod_cast le_trans h1 (by rw [h2]; exact h4)
            _ = 24 ^ R * (4 * C₃e * (n : ℝ) ^ (-η)) := by rw [← mul_pow]; norm_num
      calc ∑ T ∈ S_idx.powerset.filter (·.Nonempty), ∑ p ∈ J m_r, w_p p * ∏ s ∈ T, B_fn s p
          ≤ ∑ T ∈ S_idx.powerset.filter (·.Nonempty),
              ((2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p + 24 ^ R * (4 * C₃e * (n : ℝ) ^ (-η))) :=
            Finset.sum_le_sum h_each_T
        _ = (∑ T ∈ S_idx.powerset.filter (·.Nonempty), (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p) +
              ((S_idx.powerset.filter (·.Nonempty)).card : ℝ) * (24 ^ R * (4 * C₃e * (n : ℝ) ^ (-η))) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        _ ≤ (∑ T ∈ S_idx.powerset.filter (·.Nonempty), (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p) +
              48 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) := by
            apply add_le_add le_rfl
            have hcard_le : ((S_idx.powerset.filter (·.Nonempty)).card : ℝ) ≤ 2 ^ R := by
              have h1 : (S_idx.powerset.filter (·.Nonempty)).card ≤ S_idx.powerset.card := Finset.card_filter_le _ _
              have h2 : S_idx.powerset.card = 2 ^ S_idx.card := Finset.card_powerset S_idx
              exact_mod_cast le_trans h1 (by rw [h2]; exact Nat.pow_le_pow_right (by norm_num) hS_idx_card)
            have hlog_ge1 : 1 ≤ (Real.log (n : ℝ)) ^ (R * (R + 2)) := one_le_pow₀ (by linarith)
            calc ((S_idx.powerset.filter (·.Nonempty)).card : ℝ) * (24 ^ R * (4 * C₃e * (n : ℝ) ^ (-η)))
                ≤ 2 ^ R * (24 ^ R * (4 * C₃e * (n : ℝ) ^ (-η))) :=
                  mul_le_mul_of_nonneg_right hcard_le (by positivity)
              _ = 48 ^ R * (4 * C₃e) * 1 * (n : ℝ) ^ (-η) := by
                  rw [← mul_assoc, ← mul_pow]
                  norm_num
                  ring
              _ ≤ 48 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact mul_le_mul_of_nonneg_left hlog_ge1 (by positivity)
    have h96 : (6 : ℝ) ^ R + 48 ^ R ≤ 96 ^ R := by
      have h6_48 : (6 : ℝ) ^ R ≤ 48 ^ R := pow_le_pow_left₀ (by norm_num) (by norm_num) R
      have h2_96 : 2 * (48 : ℝ) ^ R ≤ 96 ^ R := by
        rw [show R = 1 + (R - 1) from by omega, pow_add, pow_add, pow_one, pow_one]
        have h48_96 : (48 : ℝ) ^ (R - 1) ≤ 96 ^ (R - 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        nlinarith
      linarith
    calc ‖∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ S_idx, a_fn s p‖
        ≤ (∑ T ∈ S_idx.powerset.filter (·.Nonempty), (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p) +
            ((6 ^ R + 48 ^ R) * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η)) := by
          linarith [h_split, h_main_b, h_B_err]
      _ ≤ (∑ T ∈ S_idx.powerset.filter (·.Nonempty), (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p) +
            96 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) := by
          apply add_le_add le_rfl
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right h96 (by positivity)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / Real.log (n : ℝ))]
  have hsum_re : ∑ p ∈ S_r, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1)) =
      ∑ m_r ∈ Finset.Icc 1 M_r, (-(-1 : ℝ) ^ m_r) *
        (∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) * ∏ s ∈ S_idx, a_fn s p).re := by
    rw [hS_r_part, Finset.sum_biUnion hdisj_J]
    refine Finset.sum_congr rfl (fun m_r hm_r => ?_)
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hv_on_J m_r hm_r p hp]
    have hprod_re : ((((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) * ∏ s ∈ S_idx, a_fn s p)).re =
        (Real.log (p : ℝ) / ((p : ℝ) - 1)) * ∏ s ∈ S_idx, (-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ) ^ s) := by
      have hcast : ∏ s ∈ S_idx, a_fn s p = ((∏ s ∈ S_idx, (-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) : ℂ) := by
        push_cast; rfl
      rw [hcast, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hprod_re]
    ring
  rw [hsum_re]
  have h_abs_le : |∑ m_r ∈ Finset.Icc 1 M_r, (-(-1 : ℝ) ^ m_r) *
        (∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) * ∏ s ∈ S_idx, a_fn s p).re| ≤
      ∑ m_r ∈ Finset.Icc 1 M_r, ‖∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) * ∏ s ∈ S_idx, a_fn s p‖ := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun m_r _ => ?_))
    rw [abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact Complex.abs_re_le_norm _
  have hmert_Sr : ∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤
      Real.log (n : ℝ) + Cm := by
    rw [← Finset.sum_biUnion hdisj_J, ← hS_r_part]
    have hsub : S_r ⊆ (Finset.Icc 3 (Nat.floor (n : ℝ))).filter Nat.Prime := by
      intro p hp; simp only [S_r, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, (Nat.le_floor_iff hn_pos.le).mpr (by exact_mod_cast le_trans hp.1.2 (Nat.sqrt_le_self n))⟩, hp.2.1⟩
    calc ∑ p ∈ S_r, Real.log (p : ℝ) / ((p : ℝ) - 1)
        ≤ ∑ p ∈ (Finset.Icc 3 (Nat.floor (n : ℝ))).filter Nat.Prime, Real.log (p : ℝ) / ((p : ℝ) - 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by
            have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
            have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
            have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
            exact div_nonneg hlogp hp1.le)
      _ ≤ Real.log (n : ℝ) + Cm := hCm n (by exact_mod_cast (by omega : 3 ≤ n))
  have h1_term : ∑ m_r ∈ Finset.Icc 1 M_r, ∑ T ∈ S_idx.powerset.filter (·.Nonempty),
        (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤
      2 ^ R * (2 + 2 * Cm) * (1 / Real.log (n : ℝ)) := by
    rw [Finset.sum_comm]
    have h_each_T_sum : ∀ T ∈ S_idx.powerset.filter (·.Nonempty),
        ∑ m_r ∈ Finset.Icc 1 M_r, (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤
          (2 + 2 * Cm) * (1 / Real.log (n : ℝ)) := by
      intro T hT
      rw [← Finset.mul_sum]
      have hT_card1 : 1 ≤ T.card := Finset.Nonempty.card_pos (Finset.mem_filter.mp hT).2
      have hpow_le : (2 / ((H : ℝ) + 1)) ^ T.card ≤ 2 / ((H : ℝ) + 1) := by
        have hbase : 2 / ((H : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          have : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH_ge1
          linarith
        exact pow_le_of_le_one (by positivity) hbase hT_card1.ne'
      have h2_H : (Real.log (n : ℝ)) ^ 2 ≤ (H : ℝ) + 1 := by
        have : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ (R + 2) :=
          pow_le_pow_right₀ (by linarith) (by omega)
        linarith [Nat.lt_floor_add_one ((Real.log (n : ℝ)) ^ (R + 2))]
      calc (2 / ((H : ℝ) + 1)) ^ T.card * ∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r, Real.log (p : ℝ) / ((p : ℝ) - 1)
          ≤ (2 / ((H : ℝ) + 1)) * (Real.log (n : ℝ) + Cm) :=
            mul_le_mul hpow_le hmert_Sr (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun p hp => by
              have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
              have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
              have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
              exact div_nonneg hlogp hp1.le))) (by positivity)
        _ ≤ (2 / (Real.log (n : ℝ)) ^ 2) * (Real.log (n : ℝ) + Cm) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h2_H
        _ ≤ (2 + 2 * Cm) * (1 / Real.log (n : ℝ)) := by
            rw [div_mul_eq_mul_div, mul_one_div, div_le_div_iff₀ (by positivity) hlogn_pos]
            nlinarith [hln100]
    calc ∑ T ∈ S_idx.powerset.filter (·.Nonempty),
            ∑ m_r ∈ Finset.Icc 1 M_r, (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, Real.log (p : ℝ) / ((p : ℝ) - 1)
        ≤ ∑ _T ∈ S_idx.powerset.filter (·.Nonempty), (2 + 2 * Cm) * (1 / Real.log (n : ℝ)) :=
          Finset.sum_le_sum h_each_T_sum
      _ = ((S_idx.powerset.filter (·.Nonempty)).card : ℝ) * ((2 + 2 * Cm) * (1 / Real.log (n : ℝ))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ R * ((2 + 2 * Cm) * (1 / Real.log (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have h1 : (S_idx.powerset.filter (·.Nonempty)).card ≤ S_idx.powerset.card := Finset.card_filter_le _ _
          have h2 : S_idx.powerset.card = 2 ^ S_idx.card := Finset.card_powerset S_idx
          exact_mod_cast le_trans h1 (by rw [h2]; exact Nat.pow_le_pow_right (by norm_num) hS_idx_card)
      _ = 2 ^ R * (2 + 2 * Cm) * (1 / Real.log (n : ℝ)) := by ring
  have h2_term : ∑ _m_r ∈ Finset.Icc 1 M_r,
        96 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) ≤
      96 ^ R * (4 * C₃e) * (1 / Real.log (n : ℝ)) := by
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hMr_le : ((M_r + 1 - 1 : ℕ) : ℝ) ≤ (Real.log (n : ℝ)) ^ A_R := by
      have : M_r + 1 - 1 = M_r := by omega
      rw [this]
      exact Nat.floor_le (by positivity)
    calc ((M_r + 1 - 1 : ℕ) : ℝ) * (96 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η))
        ≤ (Real.log (n : ℝ)) ^ A_R * (96 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η)) :=
          mul_le_mul_of_nonneg_right hMr_le (by positivity)
      _ = 96 ^ R * (4 * C₃e) * ((Real.log (n : ℝ)) ^ (A_R + R * (R + 2) + 1) / (n : ℝ) ^ η) * (1 / Real.log (n : ℝ)) := by
          rw [Real.rpow_neg hn_pos.le, pow_add, pow_add, pow_one]
          field_simp [hlogn_pos.ne']
          ring
      _ ≤ 96 ^ R * (4 * C₃e) * 1 * (1 / Real.log (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hpoly_sm (by positivity)
      _ = 96 ^ R * (4 * C₃e) * (1 / Real.log (n : ℝ)) := by ring
  calc |∑ m_r ∈ Finset.Icc 1 M_r, (-(-1 : ℝ) ^ m_r) *
          (∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) * ∏ s ∈ S_idx, a_fn s p).re|
      ≤ ∑ m_r ∈ Finset.Icc 1 M_r, ‖∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) * ∏ s ∈ S_idx, a_fn s p‖ := h_abs_le
    _ ≤ ∑ m_r ∈ Finset.Icc 1 M_r,
          ((∑ T ∈ S_idx.powerset.filter (·.Nonempty),
              (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, Real.log (p : ℝ) / ((p : ℝ) - 1)) +
            96 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η)) :=
        Finset.sum_le_sum h_prod_J
    _ = (∑ m_r ∈ Finset.Icc 1 M_r, ∑ T ∈ S_idx.powerset.filter (·.Nonempty),
            (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, Real.log (p : ℝ) / ((p : ℝ) - 1)) +
          ∑ _m_r ∈ Finset.Icc 1 M_r,
            96 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) := Finset.sum_add_distrib
    _ ≤ 2 ^ R * (2 + 2 * Cm) * (1 / Real.log (n : ℝ)) + 96 ^ R * (4 * C₃e) * (1 / Real.log (n : ℝ)) :=
        add_le_add h1_term h2_term
    _ = M_clean * (1 / Real.log (n : ℝ)) := by dsimp only [M_clean]; ring


end GrasGreenbergBrocard
