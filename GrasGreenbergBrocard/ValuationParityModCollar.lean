import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.ValuationParityDigits
import GrasGreenbergBrocard.ValuationParityVaaler
import GrasGreenbergBrocard.ExpSumBounds
import GrasGreenbergBrocard.ValuationParityThmHelpers
import GrasGreenbergBrocard.ValuationParityThm
import GrasGreenbergBrocard.ExpSumBoundsMod
import GrasGreenbergBrocard.VaalerMod
import GrasGreenbergBrocard.ValuationParityModWeight

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false

noncomputable section

open Real Finset BigOperators Asymptotics Filter
open Classical

namespace GrasGreenbergBrocard


/-! ### Collar, Inter-Collar, and Upper-Band Bounds for Modulus `h_mod` -/

theorem collar_mod_isBigO (h_mod z : ℕ) (hh_mod : 2 ≤ h_mod)
    (hz1 : 1 ≤ z) (hz2 : z < h_mod)
    (δ a b : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3)
    (r : ℕ) (hr2 : 2 ≤ r) (hrR : r ≤ Nat.floor (1 / δ)) :
    (fun n : ℕ => ∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
        p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧
        (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
        (p : ℝ) ∈ collar n r (6 * Nat.floor (1 / δ) + 30))),
      eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
        ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ))
      =O[atTop] (fun n : ℕ => 1 / Real.log (n : ℝ)) := by
  set R := Nat.floor (1 / δ)
  set A_R := 6 * R + 30
  have hR3 : 3 ≤ R := by
    rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hδ0]; push_cast; linarith
  obtain ⟨η', η, hη', hη, C₁e, C₂e, C₃e, hC₁e, hC₂e, hC₃e, hExp⟩ :=
    prime_exp_sum_bounds_mod h_mod hh_mod δ hδ0 hδ1
  obtain ⟨Cm, hCm_pos, hCm⟩ := mertens_sum_le
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_rpow_poly : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ (A_R + R + 1) / (n : ℝ) ^ η)
      atTop (nhds 0) :=
    log_pow_div_rpow_tendsto_zero (A_R + R + 1) hη
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
    have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    rw [le_div_iff₀ (pow_pos hlogn_pos 12)]
    calc (Nat.sqrt n : ℝ) * (Real.log (n : ℝ)) ^ 12 ≤ Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 12 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _); linarith
      _ = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
  have h_log_pow_R : ∀ᶠ n : ℕ in atTop,
      2 * (h_mod : ℝ) * (Real.log (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) + 1) ≤ Real.log (n : ℝ) := by
    let C_log : ℝ := 8 * (h_mod : ℝ) * ((R : ℝ) + 3) + 100
    filter_upwards [hlog_inf.eventually (eventually_ge_atTop (C_log ^ 2))] with n hn
    have hC_pos : 0 < C_log := by positivity
    have hln_pos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by positivity) hn
    have hln_ge1 : 1 ≤ Real.log (n : ℝ) := by
      have : (100 : ℝ) ^ 2 ≤ C_log ^ 2 := by nlinarith [show (100 : ℝ) ≤ C_log from by dsimp [C_log]; linarith [show (0 : ℝ) ≤ 8 * (h_mod : ℝ) * ((R : ℝ) + 3) from by positivity]]
      linarith
    have hfl_le : (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) :=
      Nat.floor_le (by positivity)
    have h1 : Real.log (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) ≤ ((R : ℝ) + 2) * Real.log (Real.log (n : ℝ)) := by
      have hH_ge1 : (1 : ℝ) ≤ (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) := by
        exact_mod_cast Nat.le_floor (by norm_num; exact one_le_pow₀ hln_ge1)
      calc Real.log (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ)
          ≤ Real.log ((Real.log (n : ℝ)) ^ (R + 2)) := Real.log_le_log (by linarith) hfl_le
        _ = ((R : ℝ) + 2) * Real.log (Real.log (n : ℝ)) := by rw [Real.log_pow]; push_cast; rfl
    have h2 : Real.log (Real.log (n : ℝ)) ≤ 2 * Real.sqrt (Real.log (n : ℝ)) := by
      have h_rpow := Real.log_le_rpow_div hln_pos.le (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← Real.sqrt_eq_rpow] at h_rpow
      linarith
    have h_sqrt_ge : C_log ≤ Real.sqrt (Real.log (n : ℝ)) := by
      rw [Real.le_sqrt hC_pos.le hln_pos.le]; exact hn
    have h_sq : Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) = Real.log (n : ℝ) :=
      Real.mul_self_sqrt hln_pos.le
    have h3 : 2 * (h_mod : ℝ) * (((R : ℝ) + 2) * (2 * Real.sqrt (Real.log (n : ℝ))) + 1) ≤ Real.log (n : ℝ) := by
      have h_lin : 2 * (h_mod : ℝ) * (((R : ℝ) + 2) * (2 * Real.sqrt (Real.log (n : ℝ))) + 1) ≤
          C_log * Real.sqrt (Real.log (n : ℝ)) := by
        dsimp [C_log]
        have h_s1 : (1 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) := by
          rw [Real.le_sqrt (by norm_num) hln_pos.le]; norm_num; exact hln_ge1
        nlinarith [show (0 : ℝ) ≤ (h_mod : ℝ) from by positivity, show (0 : ℝ) ≤ (R : ℝ) from by positivity]
      nlinarith
    have h12 : Real.log (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) ≤
        ((R : ℝ) + 2) * (2 * Real.sqrt (Real.log (n : ℝ))) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
    have h4 : 2 * (h_mod : ℝ) * (Real.log (Nat.floor ((Real.log (n : ℝ)) ^ (R + 2)) : ℝ) + 1) ≤
        2 * (h_mod : ℝ) * (((R : ℝ) + 2) * (2 * Real.sqrt (Real.log (n : ℝ))) + 1) := by
      gcongr
    linarith
  let M_clean : ℝ :=
    (1 + 2 * (h_mod : ℝ)) ^ R * (R : ℝ) * ((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₃e) +
    4 * C₃e + 1
  refine Asymptotics.IsBigO.of_bound M_clean ?_
  filter_upwards [Filter.eventually_ge_atTop 16, hExp, h_sqrt_12,
    hlog_inf.eventually (eventually_ge_atTop 100),
    (h_rpow_poly.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le),
    (h_rpow_div.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le),
    h_log_pow_R,
    ((tendsto_rpow_atTop hδ0).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)] with
    n hn hexp_n hsq12 hln100 hpoly_sm hdiv_sm hlogH_le hnd2
  dsimp only at hexp_n
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ 1 / Real.log (n : ℝ))]
  let H := Nat.floor ((Real.log (n : ℝ)) ^ (R + 2))
  have hH_ge1 : 1 ≤ H := Nat.le_floor (by norm_num; exact one_le_pow₀ (by linarith))
  have hH_ge_log : (Real.log (n : ℝ)) ^ (R + 2) / 2 ≤ (H : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((Real.log (n : ℝ)) ^ (R + 2))
    linarith [show (0 : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) from by positivity]
  let S_r := (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
    p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧
    (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
    (p : ℝ) ∈ collar n r A_R)
  let M_r := Nat.floor ((Real.log (n : ℝ)) ^ A_R)
  let J : ℕ → Finset ℕ := fun m_r => S_r.filter (fun p => (p : ℝ) ∈ collarSubinterval n r m_r A_R)
  have h_pow_R1 : ∀ p ∈ S_r, n < p ^ (R + 1) := by
    intro p hp
    have hp_lo := (Finset.mem_filter.mp hp).2.2.1
    have hR1 : 1 < (R + 1 : ℝ) * δ := by
      have : (1 / δ : ℝ) < (R : ℝ) + 1 := Nat.lt_floor_add_one (1 / δ)
      exact (one_lt_div hδ0).mp this |>.trans_le (by ring_nf; rfl) |> fun h => by
        rw [div_lt_iff₀ hδ0] at this; linarith
    have h_rpow : (n : ℝ) < (p : ℝ) ^ (R + 1) := by
      have h1 : (n : ℝ) ^ (1 : ℝ) < (n : ℝ) ^ ((R + 1 : ℕ) * δ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < n)) (by simpa using hR1)
      rw [Real.rpow_one] at h1
      have h2 : (n : ℝ) ^ ((R + 1 : ℕ) * δ) < (p : ℝ) ^ ((R + 1 : ℕ) : ℝ) := by
        rw [mul_comm, Real.rpow_mul hn_pos.le]
        exact Real.rpow_lt_rpow (by positivity) hp_lo (by positivity : (0 : ℝ) < ((R + 1 : ℕ) : ℝ))
      rw [Real.rpow_natCast] at h2
      exact lt_trans h1 h2
    exact_mod_cast h_rpow
  have hS_eq : S_r = (Finset.Icc 1 M_r).biUnion J := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_Icc, J, Finset.mem_filter]
    constructor
    · intro hp
      have hp_col := (Finset.mem_filter.mp hp).2.2.2.2.2
      have hp_pos : (0 : ℝ) < (p : ℝ) := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; positivity
      have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
      have h_mr_lo : (1 : ℝ) ≤ (n : ℝ) / (p : ℝ) ^ r := by
        rw [one_le_div (by positivity)]
        have := Real.rpow_le_rpow hp_pos.le hp_col.2 hr_pos.le
        rw [← Real.rpow_mul hn_pos.le, one_div_mul_cancel hr_pos.ne', Real.rpow_one, Real.rpow_natCast] at this
        exact this
      have h_mr_hi : (n : ℝ) / (p : ℝ) ^ r < (Real.log (n : ℝ)) ^ A_R := by
        have h1 := Real.rpow_lt_rpow (by positivity) hp_col.1 hr_pos
        rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hn_pos.le,
          ← Real.rpow_mul (by positivity), one_div_mul_cancel hr_pos.ne',
          div_mul_cancel₀ _ hr_pos.ne', Real.rpow_one, Real.rpow_natCast, Real.rpow_natCast] at h1
        exact (div_lt_iff₀ (by positivity)).mpr (by
          rw [div_lt_iff₀ (by positivity)] at h1; linarith)
      let m_r := Nat.floor ((n : ℝ) / (p : ℝ) ^ r)
      have hm1 : 1 ≤ m_r := Nat.le_floor (by norm_num; exact h_mr_lo)
      have hmM : m_r ≤ M_r := Nat.floor_mono h_mr_hi.le
      refine ⟨m_r, ⟨hm1, hmM⟩, hp, ?_, hp_col⟩
      have hfl1 : (m_r : ℝ) ≤ (n : ℝ) / (p : ℝ) ^ r := Nat.floor_le (by positivity)
      have hfl2 : (n : ℝ) / (p : ℝ) ^ r < (m_r : ℝ) + 1 := Nat.lt_floor_add_one _
      have hm_pos : (0 : ℝ) < (m_r : ℝ) := by exact_mod_cast (by omega : 0 < m_r)
      constructor
      · have h_lt : (n : ℝ) / ((m_r : ℝ) + 1) < (p : ℝ) ^ r := (div_lt_iff₀ (by positivity)).mpr (by
          rw [div_lt_iff₀ (by positivity)] at hfl2; linarith)
        have := Real.rpow_lt_rpow (by positivity) h_lt (by positivity : 0 < 1 / (r : ℝ))
        rwa [← Real.rpow_natCast (p : ℝ) r, ← Real.rpow_mul hp_pos.le,
          mul_one_div_cancel hr_pos.ne', Real.rpow_one] at this
      · have h_le : (p : ℝ) ^ r ≤ (n : ℝ) / (m_r : ℝ) := (le_div_iff₀ hm_pos).mpr (by
          rw [le_div_iff₀ (by positivity)] at hfl1; linarith)
        have := Real.rpow_le_rpow (by positivity) h_le (by positivity : 0 ≤ 1 / (r : ℝ))
        rwa [← Real.rpow_natCast (p : ℝ) r, ← Real.rpow_mul hp_pos.le,
          mul_one_div_cancel hr_pos.ne', Real.rpow_one] at this
    · rintro ⟨_, _, hp, _⟩; exact hp
  have hJ_disj : Set.PairwiseDisjoint (Finset.Icc 1 M_r : Set ℕ) J := by
    intro m₁ hm₁ m₂ hm₂ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have hcol₁ := (Finset.mem_filter.mp hp₁).2.1
    have hcol₂ := (Finset.mem_filter.mp hp₂).2.1
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have h1 := Real.rpow_lt_rpow (by positivity) hcol₁.1 hr_pos
    have h2 := Real.rpow_le_rpow (by positivity) hcol₁.2 hr_pos.le
    have h3 := Real.rpow_lt_rpow (by positivity) hcol₂.1 hr_pos
    have h4 := Real.rpow_le_rpow (by positivity) hcol₂.2 hr_pos.le
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hr_pos.ne', Real.rpow_one] at h1 h2 h3 h4
    have hm₁_pos : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm₁).1
    have hm₂_pos : (0 : ℝ) < (m₂ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm₂).1
    have h12 : (n : ℝ) / ((m₁ : ℝ) + 1) < (n : ℝ) / (m₂ : ℝ) := lt_of_lt_of_le h1 h4
    have h21 : (n : ℝ) / ((m₂ : ℝ) + 1) < (n : ℝ) / (m₁ : ℝ) := lt_of_lt_of_le h3 h2
    have : m₂ < m₁ + 1 := by exact_mod_cast (by rw [div_lt_div_iff₀ (by positivity) hm₂_pos] at h12; nlinarith : (m₂ : ℝ) < (m₁ : ℝ) + 1)
    have : m₁ < m₂ + 1 := by exact_mod_cast (by rw [div_lt_div_iff₀ (by positivity) hm₁_pos] at h21; nlinarith : (m₁ : ℝ) < (m₂ : ℝ) + 1)
    omega
  have hv_on_J : ∀ m_r ∈ Finset.Icc 1 M_r, ∀ p ∈ J m_r,
      eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) =
        eExp ((z : ℝ) * (m_r : ℝ) / (h_mod : ℝ)) *
        ∏ s ∈ Finset.Icc 1 (r - 1), eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) / (h_mod : ℝ)) := by
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
            have := (div_lt_iff₀ (by positivity)).mp hdiv_sm; linarith
          have h2 : (n : ℝ) ^ (1 / ((r : ℝ) + 1)) * (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) = (n : ℝ) ^ (1 / (r : ℝ)) := by
            rw [← Real.rpow_add hn_pos]
            congr 1; field_simp [hr_pos.ne', by positivity : (r : ℝ) + 1 ≠ 0]; ring
          have h_lt := lt_of_le_of_lt hpow_gt h1
          calc (n : ℝ) ^ (1 / ((r : ℝ) + 1)) * (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ))
              < (n : ℝ) ^ (1 / ((r : ℝ) + 1)) * (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) :=
                mul_lt_mul_of_pos_left h_lt (by positivity)
            _ = (n : ℝ) ^ (1 / (r : ℝ)) := h2
        have hlt_p := lt_trans h_gap h_col_lo
        have := Real.rpow_lt_rpow (by positivity) hlt_p (by positivity : (0 : ℝ) < (r : ℝ) + 1)
        rw [← Real.rpow_mul hn_pos.le, one_div_mul_cancel (by positivity : (r : ℝ) + 1 ≠ 0), Real.rpow_one] at this
        rw [show (r : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) from by push_cast; ring, Real.rpow_natCast] at this
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
      rw [show r = (r - 1) + 1 from by omega, Finset.sum_Icc_succ_top (by omega : 1 ≤ (r - 1) + 1), h_div_mr]
    rw [h_v, h_sum_split]
    have h_fl_eq : ∀ s ∈ Finset.Icc 1 (r - 1),
        Int.floor ((n : ℝ) / (p : ℝ) ^ s) = ((n / p ^ s : ℕ) : ℤ) := by
      intro s _
      have hp_pos' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pr.pos
      have hps_pos : (0 : ℝ) < (p : ℝ) ^ s := pow_pos hp_pos' s
      rw [Int.floor_eq_iff]
      constructor
      · rw [Int.cast_natCast, le_div_iff₀ hps_pos]; exact_mod_cast Nat.div_mul_le_self n (p ^ s)
      · rw [Int.cast_natCast, div_lt_iff₀ hps_pos]
        have h_nat : n < (n / p ^ s + 1) * p ^ s := by
          have := Nat.lt_div_mul_add (a := n) (pow_pos hp_pr.pos s); linarith
        have h_natR : (n : ℝ) < ((n / p ^ s + 1 : ℕ) : ℝ) * ((p ^ s : ℕ) : ℝ) := by exact_mod_cast h_nat
        push_cast at h_natR; exact h_natR
    have h_prod_e : ∏ s ∈ Finset.Icc 1 (r - 1),
          eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) / (h_mod : ℝ)) =
        eExp ((z : ℝ) * ((∑ s ∈ Finset.Icc 1 (r - 1), n / p ^ s : ℕ) : ℝ) / (h_mod : ℝ)) := by
      clear h_v h_div_mr h_gt_r_zero h_sum_split
      have h_cong : ∏ s ∈ Finset.Icc 1 (r - 1),
            eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) / (h_mod : ℝ)) =
          ∏ s ∈ Finset.Icc 1 (r - 1),
            eExp ((z : ℝ) * ((n / p ^ s : ℕ) : ℝ) / (h_mod : ℝ)) := by
        refine Finset.prod_congr rfl (fun s hs => ?_)
        rw [h_fl_eq s hs, Int.cast_natCast]
      rw [h_cong]
      induction (Finset.Icc 1 (r - 1)) using Finset.induction_on with
      | empty => simp [eExp]
      | @insert a S ha ih =>
        rw [Finset.prod_insert ha, ih, Finset.sum_insert ha, Nat.cast_add, mul_add, add_div, eExp_add]
    rw [h_prod_e, Nat.cast_add, mul_add, add_div, eExp_add]
    ring
  obtain ⟨c_mod, b_mod, hb_mod0, hb_mod_norm, h_vaaler_pw, h_L1⟩ :=
    vaaler_mod_approx h_mod hh_mod z hz1 hz2 H hH_ge1
  let allH := Finset.Icc (-(H : ℤ)) (H : ℤ)
  let nzH := allH.filter (· ≠ 0)
  let Psi_mod : ℝ → ℂ := fun x => ∑ m ∈ nzH, c_mod m * eExp ((m : ℝ) * x / (h_mod : ℝ))
  let B_mod : ℝ → ℂ := fun x => ∑ m ∈ allH, b_mod m * eExp ((m : ℝ) * x / (h_mod : ℝ))
  have hB_norm_le : ∀ x : ℝ, ‖B_mod x‖ ≤ 2 * (h_mod : ℝ) := by
    intro x
    calc ‖B_mod x‖ ≤ ∑ m ∈ allH, ‖b_mod m * eExp ((m : ℝ) * x / (h_mod : ℝ))‖ := norm_sum_le _ _
      _ = ∑ m ∈ allH, ‖b_mod m‖ := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [norm_mul, show ‖eExp ((m : ℝ) * x / (h_mod : ℝ))‖ = 1 from by
            exact norm_eExp _, mul_one]
      _ ≤ ∑ _m ∈ allH, (h_mod : ℝ) / ((H : ℝ) + 1) := Finset.sum_le_sum (fun m _ => hb_mod_norm m)
      _ = (allH.card : ℝ) * ((h_mod : ℝ) / ((H : ℝ) + 1)) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (H : ℝ) + 2) * ((h_mod : ℝ) / ((H : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard : allH.card = 2 * H + 1 := by
            dsimp only [allH]; rw [Int.card_Icc]; omega
          rw [hcard]; push_cast; linarith
      _ = 2 * (h_mod : ℝ) := by
          have : (H : ℝ) + 1 ≠ 0 := by positivity
          field_simp [this]
  have hPsi_norm_le : ∀ x : ℝ, ‖Psi_mod x‖ ≤ 1 + 2 * (h_mod : ℝ) := by
    intro x
    have h1 := h_vaaler_pw x
    have h2 : (B_mod x).re ≤ 2 * (h_mod : ℝ) := le_trans (Complex.re_le_norm _) (hB_norm_le x)
    have h3 : ‖eExp ((z : ℝ) * (Int.floor x : ℝ) / (h_mod : ℝ))‖ = 1 := by
      exact norm_eExp _
    calc ‖Psi_mod x‖ = ‖eExp ((z : ℝ) * (Int.floor x : ℝ) / (h_mod : ℝ)) -
          (eExp ((z : ℝ) * (Int.floor x : ℝ) / (h_mod : ℝ)) - Psi_mod x)‖ := by congr 1; ring
      _ ≤ ‖eExp ((z : ℝ) * (Int.floor x : ℝ) / (h_mod : ℝ))‖ +
          ‖eExp ((z : ℝ) * (Int.floor x : ℝ) / (h_mod : ℝ)) - Psi_mod x‖ := norm_sub_le _ _
      _ ≤ 1 + (B_mod x).re := by linarith
      _ ≤ 1 + 2 * (h_mod : ℝ) := by linarith
  have h_J_exp : ∀ (m_r : ℕ) (hm_r : m_r ∈ Finset.Icc 1 M_r) (A : Finset ℕ) (hA_sub : A ⊆ Finset.Icc 1 (r - 1))
      (h_fn : ℕ → ℤ) (hA_nz : ∃ s ∈ A, h_fn s ≠ 0) (hh_le : ∀ s ∈ A, |h_fn s| ≤ (H : ℤ)),
      ‖∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
          eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))‖ ≤
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
          have : (r : ℝ) ≤ (R : ℝ) := by exact_mod_cast hrR
          have : (R : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
          calc (r : ℝ) * δ ≤ (R : ℝ) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ0.le
            _ ≤ (1 / δ) * δ := mul_le_mul_of_nonneg_right this hδ0.le
            _ = 1 := one_div_mul_cancel hδ0.ne'
        · apply Real.rpow_le_rpow (by positivity) (div_le_self hn_pos.le (by linarith)) (by positivity)
      have hP_hi : P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := by
        have h1 : (n : ℝ) ^ (1 / (r : ℝ)) ≤ (Nat.sqrt n : ℝ) + 1 := by
          have h_le_sqrt : (n : ℝ) ^ (1 / (r : ℝ)) ≤ Real.sqrt (n : ℝ) := by
            rw [Real.sqrt_eq_rpow]
            apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
            exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hr2)
          have h_lt := Nat.lt_succ_sqrt' n
          have h_rt : Real.sqrt (n : ℝ) < (Nat.sqrt n : ℝ) + 1 := by
            rw [Real.sqrt_lt' (by positivity)]; exact_mod_cast h_lt
          linarith
        have h_half : (n : ℝ) ^ (1 / (r : ℝ)) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
          exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hr2)
        have hsq_half : (Nat.sqrt n : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := hsq12
        have hn_16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have h_extra : P ≤ (Nat.sqrt n : ℝ) := by
          obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr h_ne
          dsimp only [J] at hp₀
          have hp₀S := (Finset.mem_filter.mp hp₀).1
          have hp₀_sq : p₀ ≤ Nat.sqrt n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp₀S).1).2
          have hp₀_col := (Finset.mem_filter.mp hp₀).2.1
          calc P ≤ (p₀ : ℝ) := max_le (Finset.mem_filter.mp hp₀S).2.2.1.le hp₀_col.1.le
            _ ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast hp₀_sq
        exact le_trans h_extra hsq_half
      have hI_prime : ∀ p ∈ J m_r, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P := by
        intro p hp
        have hpS := (Finset.mem_filter.mp hp).1
        have hp_pr := (Finset.mem_filter.mp hpS).2.1
        have hp_nd : (n : ℝ) ^ δ < (p : ℝ) := (Finset.mem_filter.mp hp).2 |> fun h => (Finset.mem_filter.mp hpS).2.2.1
        have hp_col := (Finset.mem_filter.mp hp).2.1
        refine ⟨hp_pr, max_lt hp_nd hp_col.1, ?_⟩
        have h_ratio : ((n : ℝ) / (m_r : ℝ)) ^ (1 / (r : ℝ)) ≤ 2 * (((n : ℝ) / ((m_r : ℝ) + 1)) ^ (1 / (r : ℝ))) := by
          rw [← mul_one_div, ← Real.mul_rpow (by positivity) (by positivity)]
          apply Real.rpow_le_rpow (by positivity) _ (by positivity)
          have : (n : ℝ) / (m_r : ℝ) ≤ 2 ^ r * ((n : ℝ) / ((m_r : ℝ) + 1)) := by
            have h2r : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
              calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
                _ ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) (by omega : 1 ≤ r)
            rw [div_le_iff₀ hm_pos]
            calc (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm
              _ ≤ (n : ℝ) * (2 * (m_r : ℝ) / ((m_r : ℝ) + 1)) := by
                  apply mul_le_mul_of_nonneg_left _ hn_pos.le
                  rw [one_le_div (by positivity)]; linarith
              _ = 2 * ((m_r : ℝ) * ((n : ℝ) / ((m_r : ℝ) + 1))) := by ring
              _ ≤ (2 : ℝ) ^ r * ((m_r : ℝ) * ((n : ℝ) / ((m_r : ℝ) + 1))) := by
                  gcongr
              _ = (2 : ℝ) ^ r * ((n : ℝ) / ((m_r : ℝ) + 1)) * (m_r : ℝ) := by ring
          simpa [Real.rpow_natCast] using this
        exact le_trans hp_col.2 (le_trans h_ratio (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)))
      have hA_range : ∀ s ∈ A, 1 ≤ s ∧ s ≤ R := fun s hs => by
        have := Finset.mem_Icc.mp (hA_sub hs); exact ⟨this.1, by omega⟩
      have hPhase : ∀ s ∈ A, (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) / P ^ s := by
        intro s hs
        have hs_range := Finset.mem_Icc.mp (hA_sub hs)
        have hP_s : P ^ s ≤ (n : ℝ) ^ ((s : ℝ) / (r : ℝ)) := by
          calc P ^ s ≤ ((n : ℝ) ^ (1 / (r : ℝ))) ^ s := pow_le_pow_left₀ hP_pos.le hP_le_n1r s
            _ = (n : ℝ) ^ ((s : ℝ) / (r : ℝ)) := by
                rw [← Real.rpow_natCast _ s, ← Real.rpow_mul hn_pos.le, one_div_mul_eq_div]
        have h_n_div : (n : ℝ) ^ (1 / (r : ℝ)) ≤ (n : ℝ) / P ^ s := by
          rw [le_div_iff₀ (pow_pos hP_pos s)]
          calc (n : ℝ) ^ (1 / (r : ℝ)) * P ^ s ≤ (n : ℝ) ^ (1 / (r : ℝ)) * (n : ℝ) ^ ((s : ℝ) / (r : ℝ)) :=
                mul_le_mul_of_nonneg_left hP_s (by positivity)
            _ = (n : ℝ) ^ ((1 + (s : ℝ)) / (r : ℝ)) := by
                rw [← Real.rpow_add hn_pos]; congr 1; ring
            _ ≤ (n : ℝ) ^ (1 : ℝ) := by
                apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
                rw [div_le_one hr_pos]; exact_mod_cast (by omega : 1 + s ≤ r)
            _ = (n : ℝ) := Real.rpow_one _
        have h_log_le : (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) ^ (1 / (r : ℝ)) := by
          have h1 : (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) := by
            have := (div_lt_iff₀ (by positivity)).mp hdiv_sm; linarith
          have h2 : (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) ≤ (n : ℝ) ^ (1 / (r : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
            apply one_div_le_one_div_of_le hr_pos
            nlinarith
          have h2z : (2 : ℝ) ^ (-(R : ℤ)) ≤ 1 := by
            rw [zpow_neg, zpow_natCast]
            exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
          calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R
              ≤ 1 * (Real.log (n : ℝ)) ^ A_R := mul_le_mul_of_nonneg_right h2z (by positivity)
            _ ≤ (n : ℝ) ^ (1 / (r : ℝ)) := by linarith
        exact le_trans h_log_le h_n_div
      have hW_bound : ∀ t ∈ Set.Icc P (2 * P), |1 / (t - 1)| ≤ 2 / P := by
        intro t ht
        have hP2 : 2 ≤ P := le_trans hnd2 hP_lo
        have ht1 : P / 2 ≤ t - 1 := by linarith [ht.1]
        have ht_sub_pos : 0 < t - 1 := by linarith [ht.1, hP2]
        rw [abs_of_nonneg (one_div_nonneg.mpr ht_sub_pos.le)]
        rw [one_div, inv_le_comm₀ ht_sub_pos (div_pos (by norm_num) hP_pos), inv_div]
        linarith
      have h_res := hexp_n P (J m_r) A h_fn (fun t => 1 / (t - 1)) (2 / P) hA_nz
        hP_lo hP_hi hI_prime hA_range hh_le hPhase hW_bound (by positivity)
      let r₀ := (A.filter (fun s => h_fn s ≠ 0)).min' (by
        obtain ⟨s, hsA, hs0⟩ := hA_nz; exact ⟨s, Finset.mem_filter.mpr ⟨hsA, hs0⟩⟩)
      have hr₀_mem : r₀ ∈ A := (Finset.mem_filter.mp (Finset.min'_mem _ _)).1
      have hr₀_ne : h_fn r₀ ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ _)).2
      have hT₀_ge : |(h_fn r₀ : ℝ)| * (n : ℝ) / P ^ r₀ ≥ (n : ℝ) ^ (δ / 2) := by
        have hh1 : (1 : ℝ) ≤ |(h_fn r₀ : ℝ)| := by exact_mod_cast Int.one_le_abs hr₀_ne
        have hr₀_le : r₀ ≤ r - 1 := (Finset.mem_Icc.mp (hA_sub hr₀_mem)).2
        have hP_r₀ : P ^ r₀ ≤ (n : ℝ) ^ (((r : ℝ) - 1) / (r : ℝ)) := by
          calc P ^ r₀ ≤ ((n : ℝ) ^ (1 / (r : ℝ))) ^ r₀ := pow_le_pow_left₀ hP_pos.le hP_le_n1r r₀
            _ = (n : ℝ) ^ ((r₀ : ℝ) / (r : ℝ)) := by
                rw [← Real.rpow_natCast _ r₀, ← Real.rpow_mul hn_pos.le, one_div_mul_eq_div]
            _ ≤ (n : ℝ) ^ (((r : ℝ) - 1) / (r : ℝ)) := by
                apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
                apply div_le_div_of_nonneg_right _ hr_pos.le
                have : (r₀ : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast hr₀_le
                rwa [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] at this
        have h_n_div : (n : ℝ) ^ (δ / 2) ≤ (n : ℝ) / P ^ r₀ := by
          rw [le_div_iff₀ (pow_pos hP_pos r₀)]
          calc (n : ℝ) ^ (δ / 2) * P ^ r₀ ≤ (n : ℝ) ^ (δ / 2) * (n : ℝ) ^ (((r : ℝ) - 1) / (r : ℝ)) :=
                mul_le_mul_of_nonneg_left hP_r₀ (by positivity)
            _ = (n : ℝ) ^ (δ / 2 + ((r : ℝ) - 1) / (r : ℝ)) := (Real.rpow_add hn_pos _ _).symm
            _ ≤ (n : ℝ) ^ (1 : ℝ) := by
                apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
                have h_rδ : (r : ℝ) * δ ≤ 1 := by
                  have : (r : ℝ) ≤ (R : ℝ) := by exact_mod_cast hrR
                  have : (R : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
                  calc (r : ℝ) * δ ≤ (R : ℝ) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ0.le
                    _ ≤ (1 / δ) * δ := mul_le_mul_of_nonneg_right this hδ0.le
                    _ = 1 := one_div_mul_cancel hδ0.ne'
                have h_1r : 1 / (r : ℝ) ≥ δ := by
                  rw [ge_iff_le, le_div_iff₀ hr_pos]; linarith
                linarith [show ((r : ℝ) - 1) / (r : ℝ) = 1 - 1 / (r : ℝ) from by field_simp [hr_pos.ne']]
            _ = (n : ℝ) := Real.rpow_one _
        calc (n : ℝ) ^ (δ / 2) ≤ 1 * ((n : ℝ) / P ^ r₀) := by linarith
          _ ≤ |(h_fn r₀ : ℝ)| * ((n : ℝ) / P ^ r₀) :=
              mul_le_mul_of_nonneg_right hh1 (div_nonneg hn_pos.le (pow_nonneg hP_pos.le _))
          _ = |(h_fn r₀ : ℝ)| * (n : ℝ) / P ^ r₀ := by ring
      have h_res2 := h_res.2 hT₀_ge
      have h_eq_sum : ∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
            eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s)) =
          ∑ p ∈ J m_r, (((fun t => 1 / (t - 1)) (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
            eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s)) :=
        Finset.sum_congr rfl (fun p _ => by congr 2; ring)
      rw [h_eq_sum]
      calc ‖∑ p ∈ J m_r, (((fun t => 1 / (t - 1)) (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
            eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))‖
          ≤ P * (C₃e * (2 / P)) * (n : ℝ) ^ (-η) := h_res2
        _ = 2 * C₃e * (n : ℝ) ^ (-η) := by field_simp [hP_pos.ne']
        _ ≤ 4 * C₃e * (n : ℝ) ^ (-η) := by
            have : 0 ≤ C₃e * (n : ℝ) ^ (-η) := by positivity
            linarith
  -- Now sum over m_r ∈ Icc 1 M_r
  have hS_sum_eq : ∑ p ∈ S_r, eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
        ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) =
      ∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r,
        eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
        ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) := by
    rw [hS_eq, Finset.sum_biUnion (fun m₁ hm₁ m₂ hm₂ hne => hJ_disj hm₁ hm₂ hne)]
  -- On each J m_r, split into Psi_mod product + error
  have hJ_bound : ∀ m_r ∈ Finset.Icc 1 M_r,
      ‖∑ p ∈ J m_r, eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)‖ ≤
        (1 + 2 * (h_mod : ℝ)) ^ R * ∑ s ∈ Finset.Icc 1 (r - 1),
          (∑ p ∈ J m_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re) +
        (Real.log (n : ℝ)) ^ (r - 1) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
    intro m_r hm_r
    let I_s := Finset.Icc 1 (r - 1)
    let err_sum : ℂ := ∑ p ∈ J m_r,
      (eExp ((z : ℝ) * (m_r : ℝ) / (h_mod : ℝ)) *
        ((∏ s ∈ I_s, eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) / (h_mod : ℝ))) -
         (∏ s ∈ I_s, Psi_mod ((n : ℝ) / (p : ℝ) ^ s)))) *
      ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)
    let main_sum : ℂ := ∑ p ∈ J m_r,
      (eExp ((z : ℝ) * (m_r : ℝ) / (h_mod : ℝ)) *
        (∏ s ∈ I_s, Psi_mod ((n : ℝ) / (p : ℝ) ^ s))) *
      ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)
    have h_split : ∑ p ∈ J m_r, eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) = err_sum + main_sum := by
      dsimp only [err_sum, main_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [hv_on_J m_r hm_r p hp]; ring
    rw [h_split]
    have h_err_bd : ‖err_sum‖ ≤ (1 + 2 * (h_mod : ℝ)) ^ R * ∑ s ∈ I_s,
        (∑ p ∈ J m_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re) := by
      calc ‖err_sum‖ ≤ ∑ p ∈ J m_r, ‖(eExp ((z : ℝ) * (m_r : ℝ) / (h_mod : ℝ)) *
            ((∏ s ∈ I_s, eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) / (h_mod : ℝ))) -
             (∏ s ∈ I_s, Psi_mod ((n : ℝ) / (p : ℝ) ^ s)))) *
            ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ p ∈ J m_r, ((1 + 2 * (h_mod : ℝ)) ^ I_s.card *
              ∑ s ∈ I_s, (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re) *
              (Real.log (p : ℝ) / ((p : ℝ) - 1)) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
            have hw_nn : 0 ≤ Real.log (p : ℝ) / ((p : ℝ) - 1) := by
              have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
              have : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
              exact div_nonneg (Real.log_nonneg this) this.le
            rw [norm_mul, norm_mul, show ‖eExp ((z : ℝ) * (m_r : ℝ) / (h_mod : ℝ))‖ = 1 from by
                exact norm_eExp _, one_mul,
              Complex.norm_real, Real.norm_of_nonneg hw_nn]
            apply mul_le_mul_of_nonneg_right _ hw_nn
            exact prod_sub_prod_norm_le I_s
              (fun s => eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) / (h_mod : ℝ)))
              (fun s => Psi_mod ((n : ℝ) / (p : ℝ) ^ s))
              (fun s => (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re)
              (1 + 2 * (h_mod : ℝ)) (by linarith)
              (fun s _ => by exact norm_eExp _)
              (fun s _ => hPsi_norm_le _)
              (fun s _ => h_vaaler_pw _)
        _ ≤ (1 + 2 * (h_mod : ℝ)) ^ R * ∑ s ∈ I_s,
              (∑ p ∈ J m_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re) := by
            have hcard : I_s.card ≤ R := by dsimp only [I_s]; rw [Nat.card_Icc]; omega
            have hpow : (1 + 2 * (h_mod : ℝ)) ^ I_s.card ≤ (1 + 2 * (h_mod : ℝ)) ^ R :=
              pow_le_pow_right₀ (by linarith) hcard
            calc ∑ p ∈ J m_r, ((1 + 2 * (h_mod : ℝ)) ^ I_s.card *
                  ∑ s ∈ I_s, (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re) * (Real.log (p : ℝ) / ((p : ℝ) - 1))
                = (1 + 2 * (h_mod : ℝ)) ^ I_s.card * ∑ s ∈ I_s, ∑ p ∈ J m_r,
                    (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re := by
                  rw [Finset.mul_sum, Finset.sum_comm]
                  refine Finset.sum_congr rfl (fun p _ => ?_)
                  rw [Finset.sum_mul, Finset.mul_sum]
                  refine Finset.sum_congr rfl (fun s _ => by ring)
              _ ≤ (1 + 2 * (h_mod : ℝ)) ^ R * ∑ s ∈ I_s, ∑ p ∈ J m_r,
                    (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re := by
                  apply mul_le_mul_of_nonneg_right hpow
                  refine Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun p hp => ?_))
                  have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
                  have hw_nn : 0 ≤ Real.log (p : ℝ) / ((p : ℝ) - 1) := by
                    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
                    have : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
                    exact div_nonneg (Real.log_nonneg this) this.le
                  have hB_nn : 0 ≤ (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re :=
                    le_trans (norm_nonneg _) (h_vaaler_pw _)
                  exact mul_nonneg hw_nn hB_nn
    have h_main_bd : ‖main_sum‖ ≤ (Real.log (n : ℝ)) ^ (r - 1) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
      have h_eq : main_sum = eExp ((z : ℝ) * (m_r : ℝ) / (h_mod : ℝ)) *
          ∑ h ∈ I_s.pi (fun _ => nzH), (∏ s ∈ I_s.attach, c_mod (h s.1 s.2)) *
            ∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
              eExp (∑ s ∈ I_s, ((if hs : s ∈ I_s then h s hs else 0 : ℤ) : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s)) := by
        have h_inner : ∀ p ∈ J m_r,
            (eExp ((z : ℝ) * (m_r : ℝ) / (h_mod : ℝ)) * (∏ s ∈ I_s, Psi_mod ((n : ℝ) / (p : ℝ) ^ s))) *
              ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) =
            ∑ h ∈ I_s.pi (fun _ => nzH),
              eExp ((z : ℝ) * (m_r : ℝ) / (h_mod : ℝ)) *
                ((∏ s ∈ I_s.attach, c_mod (h s.1 s.2)) *
                  (((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
                    eExp (∑ s ∈ I_s, ((if hs : s ∈ I_s then h s hs else 0 : ℤ) : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s)))) := by
          intro p _
          dsimp only [Psi_mod]
          rw [Finset.prod_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun h _ => ?_)
          have h_e_prod : ∏ s ∈ I_s.attach, c_mod (h s.1 s.2) * eExp ((h s.1 s.2 : ℝ) * ((n : ℝ) / (p : ℝ) ^ s.1) / (h_mod : ℝ)) =
              (∏ s ∈ I_s.attach, c_mod (h s.1 s.2)) *
                eExp (∑ s ∈ I_s, ((if hs : s ∈ I_s then h s hs else 0 : ℤ) : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s)) := by
            rw [Finset.prod_mul_distrib, eExp_sum]
            congr 2
            rw [← Finset.sum_attach I_s]
            refine Finset.sum_congr rfl (fun s _ => ?_)
            simp only [dif_pos s.2]; ring
          rw [h_e_prod]; ring
        calc main_sum = ∑ p ∈ J m_r, ∑ h ∈ I_s.pi (fun _ => nzH),
              eExp ((z : ℝ) * (m_r : ℝ) / (h_mod : ℝ)) *
                ((∏ s ∈ I_s.attach, c_mod (h s.1 s.2)) *
                  (((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
                    eExp (∑ s ∈ I_s, ((if hs : s ∈ I_s then h s hs else 0 : ℤ) : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s)))) :=
              Finset.sum_congr rfl h_inner
          _ = ∑ h ∈ I_s.pi (fun _ => nzH), ∑ p ∈ J m_r,
              eExp ((z : ℝ) * (m_r : ℝ) / (h_mod : ℝ)) *
                ((∏ s ∈ I_s.attach, c_mod (h s.1 s.2)) *
                  (((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
                    eExp (∑ s ∈ I_s, ((if hs : s ∈ I_s then h s hs else 0 : ℤ) : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s)))) :=
              Finset.sum_comm
          _ = _ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun h _ => ?_)
              rw [Finset.mul_sum, Finset.mul_sum]
      rw [h_eq, norm_mul, show ‖eExp ((z : ℝ) * (m_r : ℝ) / (h_mod : ℝ))‖ = 1 from by
          exact norm_eExp _, one_mul]
      calc ‖∑ h ∈ I_s.pi (fun _ => nzH), _‖
          ≤ ∑ h ∈ I_s.pi (fun _ => nzH), ‖(∏ s ∈ I_s.attach, c_mod (h s.1 s.2)) *
              ∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
                eExp (∑ s ∈ I_s, ((if hs : s ∈ I_s then h s hs else 0 : ℤ) : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ h ∈ I_s.pi (fun _ => nzH), (∏ s ∈ I_s.attach, ‖c_mod (h s.1 s.2)‖) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
            refine Finset.sum_le_sum (fun h hh => ?_)
            rw [norm_mul, norm_prod]
            apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
            have h1_mem : 1 ∈ I_s := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
            have hh1_ne : (if hs : 1 ∈ I_s then h 1 hs else 0) ≠ 0 := by
              rw [dif_pos h1_mem]
              exact (Finset.mem_filter.mp (Finset.mem_pi.mp hh 1 h1_mem)).2
            have hh_le : ∀ s ∈ I_s, |(if hs : s ∈ I_s then h s hs else 0)| ≤ (H : ℤ) := by
              intro s hs
              rw [dif_pos hs]
              have := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_pi.mp hh s hs)).1
              exact abs_le.mpr this
            exact h_J_exp m_r hm_r I_s Subset.rfl (fun s => if hs : s ∈ I_s then h s hs else 0)
              ⟨1, h1_mem, hh1_ne⟩ hh_le
        _ = (∑ h ∈ I_s.pi (fun _ => nzH), ∏ s ∈ I_s.attach, ‖c_mod (h s.1 s.2)‖) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
            rw [← Finset.sum_mul]
        _ = (∏ _s ∈ I_s, ∑ m ∈ nzH, ‖c_mod m‖) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
            congr 1; rw [Finset.prod_sum]
        _ = (∑ m ∈ nzH, ‖c_mod m‖) ^ (r - 1) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
            rw [Finset.prod_const, show I_s.card = r - 1 from by dsimp only [I_s]; rw [Nat.card_Icc]; omega]
        _ ≤ (Real.log (n : ℝ)) ^ (r - 1) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
              (le_trans h_L1 hlogH_le) (r - 1)
    exact le_trans (norm_add_le _ _) (add_le_add h_err_bd h_main_bd)
  -- Bound the B_mod sum over S_r directly
  have h_B_total : ∀ s ∈ Finset.Icc 1 (r - 1),
      ∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r,
        (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re ≤
      ((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₃e) / Real.log (n : ℝ) := by
    intro s hs
    have h_B_eq : ∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r,
          (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re =
        (∑ p ∈ S_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (b_mod 0).re) +
        ∑ m ∈ nzH, (b_mod m * ∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r,
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
            eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))).re := by
      have h_p_eq : ∀ p : ℕ,
          (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re =
          (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (b_mod 0).re +
          ∑ m ∈ nzH, (b_mod m * ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
            eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))).re := by
        intro p
        have hall : allH = insert 0 nzH := by
          ext m; simp only [allH, nzH, Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
          constructor
          · intro hm; by_cases hm0 : m = 0; left; exact hm0; right; exact ⟨hm, hm0⟩
          · rintro (rfl | ⟨hm, _⟩); exact ⟨by omega, by omega⟩; exact hm
        have h0_not : (0 : ℤ) ∉ nzH := by simp [nzH]
        dsimp only [B_mod]
        rw [hall, Finset.sum_insert h0_not, Complex.add_re, Complex.re_sum, mul_add, Finset.mul_sum]
        congr 1
        · simp [eExp]
        · refine Finset.sum_congr rfl (fun m _ => ?_)
          have hre : (b_mod m * eExp ((m : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / (h_mod : ℝ)) *
              ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)).re =
              (Real.log (p : ℝ) / ((p : ℝ) - 1)) *
              (b_mod m * eExp ((m : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / (h_mod : ℝ))).re := by
            rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; ring
          calc (Real.log (p : ℝ) / ((p : ℝ) - 1)) *
                (b_mod m * eExp ((m : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / (h_mod : ℝ))).re
              = (b_mod m * ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
                  eExp ((m : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / (h_mod : ℝ))).re := by
                rw [← hre]; congr 1; ring
            _ = _ := by congr 2; ring
      have h_sum1 : ∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r,
            (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re =
          (∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (b_mod 0).re) +
          ∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r, ∑ m ∈ nzH,
            (b_mod m * ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
              eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))).re := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun m_r _ => ?_)
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun p _ => h_p_eq p)
      rw [h_sum1]
      congr 1
      · rw [hS_eq, Finset.sum_biUnion (fun m₁ hm₁ m₂ hm₂ hne => hJ_disj hm₁ hm₂ hne)]
      · rw [Finset.sum_comm]
        simp_rw [Finset.sum_comm (s := J _), ← Complex.re_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.sum_comm]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m_r _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => by ring)
    rw [h_B_eq]
    have h_m0_bd : ∑ p ∈ S_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (b_mod 0).re ≤
        (h_mod : ℝ) * (1 + Cm) / Real.log (n : ℝ) := by
      have hb0_re : (b_mod 0).re = (h_mod : ℝ) / ((H : ℝ) + 1) := by
        rw [hb_mod0, Complex.ofReal_re]
      rw [← Finset.sum_mul, hb0_re]
      have hsub : S_r ⊆ (Finset.Icc 3 n).filter Nat.Prime := fun p hp =>
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1,
          le_trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2 (Nat.sqrt_le_self n)⟩,
          (Finset.mem_filter.mp hp).2.1⟩
      have hmert_n : ∑ p ∈ S_r, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ Real.log (n : ℝ) + Cm := by
        calc ∑ p ∈ S_r, Real.log (p : ℝ) / ((p : ℝ) - 1)
            ≤ ∑ p ∈ (Finset.Icc 3 n).filter Nat.Prime, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_)
              have hp3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
              have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
              have : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
              exact div_nonneg (Real.log_nonneg this) this.le
          _ ≤ Real.log (n : ℝ) + Cm := by
              have := hCm (n : ℝ) (by exact_mod_cast (by omega : 3 ≤ n))
              rwa [Nat.floor_natCast] at this
      have hH_inv : 1 / ((H : ℝ) + 1) ≤ 2 / (Real.log (n : ℝ)) ^ (R + 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      have h_log_3 : (Real.log (n : ℝ) + Cm) / (Real.log (n : ℝ)) ^ (R + 2) ≤ (1 + Cm) / (Real.log (n : ℝ)) ^ 2 := by
        have hR4 : 4 ≤ R + 2 := by omega
        have hpow_ge : (Real.log (n : ℝ)) ^ 3 ≤ (Real.log (n : ℝ)) ^ (R + 1) := by
          apply pow_le_pow_right₀ (by linarith) (by omega)
        have hln1 : 1 ≤ Real.log (n : ℝ) := by linarith
        calc (Real.log (n : ℝ) + Cm) / (Real.log (n : ℝ)) ^ (R + 2)
            ≤ ((1 + Cm) * Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 3 := by
              apply div_le_div₀ (by positivity)
              · nlinarith [hCm_pos]
              · positivity
              · exact pow_le_pow_right₀ (by linarith) (by omega)
          _ = (1 + Cm) / (Real.log (n : ℝ)) ^ 2 := by
              field_simp [hlogn_pos.ne']
      calc (∑ p ∈ S_r, Real.log (p : ℝ) / ((p : ℝ) - 1)) * ((h_mod : ℝ) / ((H : ℝ) + 1))
          ≤ (Real.log (n : ℝ) + Cm) * ((h_mod : ℝ) * (2 / (Real.log (n : ℝ)) ^ (R + 2))) := by
            apply mul_le_mul hmert_n _ (by positivity) (by positivity)
            rw [div_eq_mul_one_div, div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_left hH_inv (by positivity)
        _ = 2 * (h_mod : ℝ) * ((Real.log (n : ℝ) + Cm) / (Real.log (n : ℝ)) ^ (R + 2)) := by ring
        _ ≤ 2 * (h_mod : ℝ) * ((1 + Cm) / (Real.log (n : ℝ)) ^ 2) :=
            mul_le_mul_of_nonneg_left h_log_3 (by positivity)
        _ ≤ (h_mod : ℝ) * (1 + Cm) / Real.log (n : ℝ) := by
            rw [div_le_div_iff₀ (by positivity) hlogn_pos]
            nlinarith [hCm_pos]
    have h_nz_bd : ∑ m ∈ nzH, (b_mod m * ∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r,
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
            eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))).re ≤
        8 * (h_mod : ℝ) * C₃e / Real.log (n : ℝ) := by
      calc ∑ m ∈ nzH, (b_mod m * ∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r,
              ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
                eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))).re
          ≤ ∑ m ∈ nzH, ‖b_mod m * ∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r,
              ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
                eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))‖ :=
            Finset.sum_le_sum (fun m _ => Complex.re_le_norm _)
        _ ≤ ∑ m ∈ nzH, ((h_mod : ℝ) / ((H : ℝ) + 1)) *
              ((M_r : ℝ) * (4 * C₃e * (n : ℝ) ^ (-η))) := by
            refine Finset.sum_le_sum (fun m hm => ?_)
            rw [norm_mul]
            apply mul_le_mul (hb_mod_norm m) _ (norm_nonneg _) (by positivity)
            calc ‖∑ m_r ∈ Finset.Icc 1 M_r, _‖
                ≤ ∑ m_r ∈ Finset.Icc 1 M_r, ‖∑ p ∈ J m_r, _‖ := norm_sum_le _ _
              _ ≤ ∑ _m_r ∈ Finset.Icc 1 M_r, (4 * C₃e * (n : ℝ) ^ (-η)) := by
                  refine Finset.sum_le_sum (fun m_r hm_r => ?_)
                  have h_res := h_J_exp m_r hm_r {s} (Finset.singleton_subset_iff.mpr hs)
                    (fun _ => m) ⟨s, Finset.mem_singleton_self s, (Finset.mem_filter.mp hm).2⟩
                    (fun _ _ => abs_le.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1))
                  simpa using h_res
              _ = (M_r : ℝ) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
                  simp [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        _ = (nzH.card : ℝ) * ((h_mod : ℝ) / ((H : ℝ) + 1)) * ((M_r : ℝ) * (4 * C₃e * (n : ℝ) ^ (-η))) := by
            simp [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ (2 * (h_mod : ℝ)) * ((Real.log (n : ℝ)) ^ A_R * (4 * C₃e * (n : ℝ) ^ (-η))) := by
            apply mul_le_mul _ _ (by positivity) (by positivity)
            · have hcard : nzH.card ≤ 2 * H := by
                have hsub : nzH ⊆ allH := Finset.filter_subset _ _
                have h0 : (0 : ℤ) ∈ allH := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
                have hlt : nzH.card < allH.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => by
                  have : (0 : ℤ) ∈ nzH := heq ▸ h0
                  exact (Finset.mem_filter.mp this).2 rfl⟩)
                have hcard_all : allH.card = 2 * H + 1 := by dsimp only [allH]; rw [Int.card_Icc]; omega
                omega
              have hcardR : (nzH.card : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hcard
              calc (nzH.card : ℝ) * ((h_mod : ℝ) / ((H : ℝ) + 1))
                  ≤ (2 * (H : ℝ)) * ((h_mod : ℝ) / ((H : ℝ) + 1)) := by gcongr
                _ ≤ 2 * (h_mod : ℝ) := by
                    rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
            · apply mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)
        _ = 8 * (h_mod : ℝ) * C₃e * ((Real.log (n : ℝ)) ^ A_R / (n : ℝ) ^ η) := by
            rw [Real.rpow_neg hn_pos.le, div_eq_mul_inv]; ring
        _ ≤ 8 * (h_mod : ℝ) * C₃e / Real.log (n : ℝ) := by
            have hpow : (Real.log (n : ℝ)) ^ (A_R + 1) / (n : ℝ) ^ η ≤ 1 := by
              calc (Real.log (n : ℝ)) ^ (A_R + 1) / (n : ℝ) ^ η
                  ≤ (Real.log (n : ℝ)) ^ (A_R + R + 1) / (n : ℝ) ^ η := by
                    apply div_le_div_of_nonneg_right _ (by positivity)
                    exact pow_le_pow_right₀ (by linarith) (by omega)
                _ ≤ 1 := hpoly_sm
            rw [div_le_div_iff₀ (by norm_num) hlogn_pos]
            have h1 : (Real.log (n : ℝ)) ^ A_R / (n : ℝ) ^ η * Real.log (n : ℝ) =
                (Real.log (n : ℝ)) ^ (A_R + 1) / (n : ℝ) ^ η := by
              rw [pow_succ]; ring
            nlinarith [show 0 ≤ 8 * (h_mod : ℝ) * C₃e from by positivity]
    linarith [show (h_mod : ℝ) * (1 + Cm) / Real.log (n : ℝ) + 8 * (h_mod : ℝ) * C₃e / Real.log (n : ℝ) =
        ((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₃e) / Real.log (n : ℝ) from by ring]
  -- Combine over all m_r ∈ Icc 1 M_r
  rw [hS_sum_eq]
  calc ‖∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r,
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)‖
      ≤ ∑ m_r ∈ Finset.Icc 1 M_r, ‖∑ p ∈ J m_r,
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ m_r ∈ Finset.Icc 1 M_r,
          ((1 + 2 * (h_mod : ℝ)) ^ R * ∑ s ∈ Finset.Icc 1 (r - 1),
            (∑ p ∈ J m_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re) +
          (Real.log (n : ℝ)) ^ (r - 1) * (4 * C₃e * (n : ℝ) ^ (-η))) :=
        Finset.sum_le_sum (fun m_r hm_r => hJ_bound m_r hm_r)
    _ = (1 + 2 * (h_mod : ℝ)) ^ R * ∑ s ∈ Finset.Icc 1 (r - 1),
          (∑ m_r ∈ Finset.Icc 1 M_r, ∑ p ∈ J m_r,
            (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re) +
        (M_r : ℝ) * ((Real.log (n : ℝ)) ^ (r - 1) * (4 * C₃e * (n : ℝ) ^ (-η))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
          show M_r + 1 - 1 = M_r from by omega, ← Finset.mul_sum]
        congr 2
        exact Finset.sum_comm
    _ ≤ (1 + 2 * (h_mod : ℝ)) ^ R * ∑ _s ∈ Finset.Icc 1 (r - 1),
          (((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₃e) / Real.log (n : ℝ)) +
        (Real.log (n : ℝ)) ^ A_R * ((Real.log (n : ℝ)) ^ (r - 1) * (4 * C₃e * (n : ℝ) ^ (-η))) := by
        refine add_le_add ?_ ?_
        · apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s hs => h_B_total s hs)) (by positivity)
        · gcongr; exact Nat.floor_le (by positivity)
    _ ≤ (1 + 2 * (h_mod : ℝ)) ^ R * (R : ℝ) *
          (((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₃e) / Real.log (n : ℝ)) +
        4 * C₃e / Real.log (n : ℝ) := by
        refine add_le_add ?_ ?_
        · rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
            show r - 1 + 1 - 1 = r - 1 from by omega]
          have hr1_le : ((r - 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : r - 1 ≤ R)
          gcongr
          positivity
        · have h_pow_le : (Real.log (n : ℝ)) ^ A_R * ((Real.log (n : ℝ)) ^ (r - 1) * (4 * C₃e * (n : ℝ) ^ (-η))) =
              4 * C₃e * ((Real.log (n : ℝ)) ^ (A_R + (r - 1)) / (n : ℝ) ^ η) := by
            rw [Real.rpow_neg hn_pos.le, div_eq_mul_inv, pow_add]; ring
          rw [h_pow_le]
          have h_p1 : (Real.log (n : ℝ)) ^ (A_R + (r - 1) + 1) / (n : ℝ) ^ η ≤ 1 := by
            calc (Real.log (n : ℝ)) ^ (A_R + (r - 1) + 1) / (n : ℝ) ^ η
                ≤ (Real.log (n : ℝ)) ^ (A_R + R + 1) / (n : ℝ) ^ η := by
                  apply div_le_div_of_nonneg_right _ (by positivity)
                  exact pow_le_pow_right₀ (by linarith) (by omega)
              _ ≤ 1 := hpoly_sm
          rw [le_div_iff₀ hlogn_pos]
          have h_mul : 4 * C₃e * ((Real.log (n : ℝ)) ^ (A_R + (r - 1)) / (n : ℝ) ^ η) * Real.log (n : ℝ) =
              4 * C₃e * ((Real.log (n : ℝ)) ^ (A_R + (r - 1) + 1) / (n : ℝ) ^ η) := by
            rw [pow_succ]; ring
          rw [h_mul]
          exact mul_le_of_le_one_right (by positivity) h_p1
    _ ≤ M_clean * (1 / Real.log (n : ℝ)) := by
        rw [show (1 + 2 * (h_mod : ℝ)) ^ R * (R : ℝ) *
            (((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₃e) / Real.log (n : ℝ)) +
            4 * C₃e / Real.log (n : ℝ) =
            ((1 + 2 * (h_mod : ℝ)) ^ R * (R : ℝ) *
              ((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₃e) + 4 * C₃e) *
              (1 / Real.log (n : ℝ)) from by ring]
        exact mul_le_mul_of_nonneg_right (by dsimp only [M_clean]; linarith) (by positivity)


end GrasGreenbergBrocard
