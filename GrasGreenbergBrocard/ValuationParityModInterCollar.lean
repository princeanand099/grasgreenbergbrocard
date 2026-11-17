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


theorem interCollar_mod_isBigO (h_mod z : ℕ) (hh_mod : 2 ≤ h_mod)
    (hz1 : 1 ≤ z) (hz2 : z < h_mod)
    (δ a b : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3)
    (r : ℕ) (hr2 : 2 ≤ r) (hrR : r ≤ Nat.floor (1 / δ)) :
    (fun n : ℕ => ∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
        p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧
        (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
        (p : ℝ) ∈ interCollar n r (6 * Nat.floor (1 / δ) + 30))),
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
    (1 + 2 * (h_mod : ℝ)) ^ R * (R : ℝ) * ((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₂e) +
    4 * C₂e + 1
  refine Asymptotics.IsBigO.of_bound M_clean ?_
  filter_upwards [Filter.eventually_ge_atTop 16, hExp, h_sqrt_12,
    hlog_inf.eventually (eventually_ge_atTop 100),
    (h_rpow_div.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le),
    h_log_pow_R,
    ((tendsto_rpow_atTop hδ0).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)] with
    n hn hexp_n hsq12 hln100 hdiv_sm hlogH_le hnd2
  dsimp only at hexp_n
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ 1 / Real.log (n : ℝ))]
  let H := Nat.floor ((Real.log (n : ℝ)) ^ (R + 2))
  have hH_ge1 : 1 ≤ H := Nat.le_floor (by norm_num; exact one_le_pow₀ (by linarith))
  have hH_ge_log : (Real.log (n : ℝ)) ^ (R + 2) / 2 ≤ (H : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((Real.log (n : ℝ)) ^ (R + 2))
    linarith [show (0 : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) from by positivity]
  let D_r := (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
    p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧
    (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
    (p : ℝ) ∈ interCollar n r A_R)
  have h_pow_R1 : ∀ p ∈ D_r, n < p ^ (R + 1) := by
    intro p hp
    have hp_lo := (Finset.mem_filter.mp hp).2.2.1
    have hR1 : 1 < (R + 1 : ℝ) * δ := by
      have : (1 / δ : ℝ) < (R : ℝ) + 1 := Nat.lt_floor_add_one (1 / δ)
      rw [div_lt_iff₀ hδ0] at this; linarith
    have h_rpow : (n : ℝ) < (p : ℝ) ^ (R + 1) := by
      have h1 : (n : ℝ) ^ (1 : ℝ) < (n : ℝ) ^ ((R + 1 : ℕ) * δ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < n)) (by simpa using hR1)
      rw [Real.rpow_one] at h1
      have h2 : (n : ℝ) ^ ((R + 1 : ℕ) * δ) < (p : ℝ) ^ ((R + 1 : ℕ) : ℝ) := by
        rw [mul_comm, Real.rpow_mul hn_pos.le, Real.rpow_natCast]
        have := Real.rpow_lt_rpow (by positivity) hp_lo (by positivity : (0 : ℝ) < (R + 1 : ℕ))
        simpa [Real.rpow_natCast] using this
      rw [Real.rpow_natCast] at h2
      exact lt_trans h1 h2
    exact_mod_cast h_rpow
  have hv_on_D : ∀ p ∈ D_r,
      eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) =
        ∏ s ∈ Finset.Icc 1 r, eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) / (h_mod : ℝ)) := by
    intro p hp
    have hp_pr := (Finset.mem_filter.mp hp).2.1
    have hp_ic := (Finset.mem_filter.mp hp).2.2.2.2.2
    have h_v : padicValNat p (Nat.factorial n) = ∑ s ∈ Finset.Icc 1 R, n / p ^ s :=
      padicValNat_factorial_eq_sum_Icc hp_pr (h_pow_R1 p hp)
    have h_gt_r_zero : ∀ s ∈ Finset.Icc (r + 1) R, n / p ^ s = 0 := by
      intro s hs
      have hs1 : r + 1 ≤ s := (Finset.mem_Icc.mp hs).1
      apply Nat.div_eq_of_lt
      have h_lt_n : (n : ℝ) < (p : ℝ) ^ (r + 1) := by
        have hp_lo := hp_ic.1
        have := Real.rpow_lt_rpow (by positivity) hp_lo (by positivity : (0 : ℝ) < (r : ℝ) + 1)
        rw [← Real.rpow_mul hn_pos.le, one_div_mul_cancel (by positivity : (r : ℝ) + 1 ≠ 0), Real.rpow_one] at this
        rw [show (r : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) from by push_cast; ring, Real.rpow_natCast] at this
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
    rw [h_v, h_sum_split]
    have h_fl_eq : ∀ s ∈ Finset.Icc 1 r,
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
        exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((n / p ^ s + 1 : ℕ) : ℝ) * ((p ^ s : ℕ) : ℝ))
    have h_cong : ∏ s ∈ Finset.Icc 1 r,
          eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) / (h_mod : ℝ)) =
        ∏ s ∈ Finset.Icc 1 r,
          eExp ((z : ℝ) * ((n / p ^ s : ℕ) : ℝ) / (h_mod : ℝ)) := by
      refine Finset.prod_congr rfl (fun s hs => ?_)
      rw [h_fl_eq s hs, Int.cast_natCast]
    rw [h_cong]
    clear h_v h_gt_r_zero h_sum_split h_cong
    induction (Finset.Icc 1 r) using Finset.induction_on with
    | empty => simp [eExp]
    | @insert a S ha ih =>
      rw [Finset.prod_insert ha, ← ih, Finset.sum_insert ha, Nat.cast_add, mul_add, add_div, eExp_add]
  let L := max ((n : ℝ) ^ δ) ((n : ℝ) ^ (1 / ((r : ℝ) + 1)))
  have hL_ge1 : 1 ≤ L := le_trans (Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) hδ0.le) (le_max_left _ _)
  let K := Nat.clog 2 (Nat.sqrt n) + 1
  let B_k : ℕ → Finset ℕ := fun k => D_r.filter (fun p => L * (2 : ℝ) ^ k < (p : ℝ) ∧ (p : ℝ) ≤ L * (2 : ℝ) ^ (k + 1))
  have hD_eq : D_r = (Finset.range (K + 1)).biUnion B_k := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_range, B_k, Finset.mem_filter]
    constructor
    · intro hp
      have hp_nd := (Finset.mem_filter.mp hp).2.2.1
      have hp_ic := (Finset.mem_filter.mp hp).2.2.2.2.2
      have hp_sq : p ≤ Nat.sqrt n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      have hp_gt_L : L < (p : ℝ) := max_lt hp_nd hp_ic.1
      have hp_div_L : 1 < (p : ℝ) / L := (one_lt_div (by linarith)).mpr hp_gt_L
      have hx_pos : 0 < Real.log ((p : ℝ) / L) / Real.log 2 :=
        div_pos (Real.log_pos hp_div_L) (Real.log_pos (by norm_num))
      have hceil_pos : 0 < Nat.ceil (Real.log ((p : ℝ) / L) / Real.log 2) := Nat.ceil_pos.mpr hx_pos
      let k := Nat.ceil (Real.log ((p : ℝ) / L) / Real.log 2) - 1
      have hk_succ : k + 1 = Nat.ceil (Real.log ((p : ℝ) / L) / Real.log 2) := Nat.sub_add_cancel hceil_pos
      have hk_lt_x : (k : ℝ) < Real.log ((p : ℝ) / L) / Real.log 2 := by
        rw [← Nat.lt_ceil]; omega
      have hx_le_k1 : Real.log ((p : ℝ) / L) / Real.log 2 ≤ ((k + 1 : ℕ) : ℝ) := by
        norm_cast; rw [hk_succ]; exact Nat.le_ceil _
      have hk_lt : k < K + 1 := by
        have h2 : Real.log ((p : ℝ) / L) / Real.log 2 ≤ Real.log (Nat.sqrt n : ℝ) / Real.log 2 := by
          apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
          apply Real.log_le_log (by positivity)
          exact le_trans (div_le_self (by positivity) hL_ge1) (by exact_mod_cast hp_sq)
        have h3 : (Nat.sqrt n : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (Nat.sqrt n) := by
          exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (Nat.sqrt n)
        have h4 : Real.log (Nat.sqrt n : ℝ) / Real.log 2 ≤ (Nat.clog 2 (Nat.sqrt n) : ℝ) := by
          rw [div_le_iff₀ (Real.log_pos (by norm_num))]
          have : Real.log (Nat.sqrt n : ℝ) ≤ Real.log ((2 : ℝ) ^ Nat.clog 2 (Nat.sqrt n)) :=
            Real.log_le_log (by positivity) h3
          rwa [Real.log_pow] at this
        have : (k : ℝ) < (K + 1 : ℝ) := by
          have : (K : ℝ) = (Nat.clog 2 (Nat.sqrt n) : ℝ) + 1 := by push_cast [K]; ring
          linarith
        exact_mod_cast this
      refine ⟨k, hk_lt, hp, ?_, ?_⟩
      · have h_lt : (2 : ℝ) ^ k < (p : ℝ) / L := by
          have h2 : (k : ℝ) * Real.log 2 < Real.log ((p : ℝ) / L) := (lt_div_iff₀ (Real.log_pos (by norm_num))).mp hk_lt_x
          rw [← Real.log_pow] at h2
          exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp h2
        calc L * (2 : ℝ) ^ k < L * ((p : ℝ) / L) := mul_lt_mul_of_pos_left h_lt (by linarith)
          _ = (p : ℝ) := mul_div_cancel₀ _ (by linarith)
      · have h_le : (p : ℝ) / L ≤ (2 : ℝ) ^ (k + 1) := by
          have h2 : Real.log ((p : ℝ) / L) ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 := (div_le_iff₀ (Real.log_pos (by norm_num))).mp hx_le_k1
          rw [← Real.log_pow] at h2
          exact (Real.log_le_log_iff (by positivity) (by positivity)).mp h2
        have hle : L * ((p : ℝ) / L) ≤ L * (2 : ℝ) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left h_le (by linarith)
        rwa [mul_div_cancel₀ _ (by linarith)] at hle
    · rintro ⟨_, _, hp, _⟩; exact hp
  have hB_disj : Set.PairwiseDisjoint (Finset.range (K + 1) : Set ℕ) B_k := by
    intro k₁ _ k₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have h1 := (Finset.mem_filter.mp hp₁).2
    have h2 := (Finset.mem_filter.mp hp₂).2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (2 : ℝ) ^ (k₁ + 1) ≤ (2 : ℝ) ^ k₂ := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    · have : (2 : ℝ) ^ (k₂ + 1) ≤ (2 : ℝ) ^ k₁ := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
  have hK_le : (K + 1 : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have h1 : Nat.clog 2 (Nat.sqrt n) ≤ Nat.log 2 (Nat.sqrt n) + 1 := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Nat.sqrt n)).le
    have hsqrt4 : 4 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
    have h2 : (2 : ℝ) ^ Nat.log 2 (Nat.sqrt n) ≤ (Nat.sqrt n : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h3 : (Nat.log 2 (Nat.sqrt n) : ℝ) * Real.log 2 ≤ Real.log (Nat.sqrt n : ℝ) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) h2
    have h4 : Real.log (Nat.sqrt n : ℝ) ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log (by positivity) (by exact_mod_cast Nat.sqrt_le_self n)
    have hlog2 : (0.69 : ℝ) < Real.log 2 := Real.log_two_gt_d9.trans_le' (by norm_num)
    have hK_R : (K + 1 : ℝ) ≤ (Nat.log 2 (Nat.sqrt n) : ℝ) + 3 := by
      have : K + 1 ≤ Nat.log 2 (Nat.sqrt n) + 3 := by omega
      exact_mod_cast this
    nlinarith
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
          have hcard : allH.card = 2 * H + 1 := by dsimp only [allH]; rw [Int.card_Icc]; omega
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
  have h_B_exp : ∀ (k : ℕ) (A : Finset ℕ) (hA_sub : A ⊆ Finset.Icc 1 r)
      (h_fn : ℕ → ℤ) (hA_nz : ∃ s ∈ A, h_fn s ≠ 0) (hh_le : ∀ s ∈ A, |h_fn s| ≤ (H : ℤ)),
      ‖∑ p ∈ B_k k, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
          eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))‖ ≤
        2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by
    intro k A hA_sub h_fn hA_nz hh_le
    rcases eq_or_ne (B_k k) ∅ with h_emp | h_ne
    · rw [h_emp, Finset.sum_empty, norm_zero]; positivity
    · let P := L * (2 : ℝ) ^ k
      have hP_lo : (n : ℝ) ^ δ ≤ P := by
        calc (n : ℝ) ^ δ ≤ L := le_max_left _ _
          _ = L * 1 := (mul_one _).symm
          _ ≤ L * (2 : ℝ) ^ k := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) (by linarith)
      have hP_pos : 0 < P := lt_of_lt_of_le (by positivity) hP_lo
      have hP_hi : P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := by
        obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr h_ne
        have hp₀_D := (Finset.mem_filter.mp hp₀).1
        have hp₀_sq : p₀ ≤ Nat.sqrt n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp₀_D).1).2
        have hp₀_gt : P < (p₀ : ℝ) := (Finset.mem_filter.mp hp₀).2.1
        exact le_trans hp₀_gt.le (le_trans (by exact_mod_cast hp₀_sq) hsq12)
      have hI_prime : ∀ p ∈ B_k k, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P := by
        intro p hp
        have hpD := (Finset.mem_filter.mp hp).1
        dsimp only [D_r] at hpD
        have hp_pr := (Finset.mem_filter.mp hpD).2.1
        have hp_bd := (Finset.mem_filter.mp hp).2
        refine ⟨hp_pr, hp_bd.1, ?_⟩
        calc (p : ℝ) ≤ L * (2 : ℝ) ^ (k + 1) := hp_bd.2
          _ = 2 * (L * (2 : ℝ) ^ k) := by rw [pow_succ]; ring
      have hA_range : ∀ s ∈ A, 1 ≤ s ∧ s ≤ R := fun s hs => by
        have := Finset.mem_Icc.mp (hA_sub hs); exact ⟨this.1, by omega⟩
      have hPhase : ∀ s ∈ A, (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) / P ^ s := by
        intro s hs
        have hs_range := Finset.mem_Icc.mp (hA_sub hs)
        obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr h_ne
        have hp₀D := (Finset.mem_filter.mp hp₀).1
        have hp₀_ic := (Finset.mem_filter.mp hp₀D).2.2.2.2.2
        have hp₀_bd := (Finset.mem_filter.mp hp₀).2
        have hP_lt_hi : P < (n : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)) :=
          lt_of_lt_of_le hp₀_bd.1 hp₀_ic.2
        have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
        have hP_r : P ^ r ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ A_R := by
          have h1 := Real.rpow_lt_rpow hP_pos.le hP_lt_hi hr_pos
          rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hn_pos.le,
            ← Real.rpow_mul (by positivity), one_div_mul_cancel hr_pos.ne',
            div_mul_cancel₀ _ hr_pos.ne', Real.rpow_one, Real.rpow_natCast, Real.rpow_natCast] at h1
          exact h1.le
        have hP_s : P ^ s ≤ P ^ r := pow_le_pow_right₀ (le_trans hL_ge1 (le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num)))) hs_range.2
        have h_div : (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) / P ^ s := by
          calc (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) / P ^ r :=
                (le_div_iff₀ (pow_pos hP_pos r)).mpr (by
                  have := (le_div_iff₀ (by positivity)).mp hP_r; linarith)
            _ ≤ (n : ℝ) / P ^ s := div_le_div_of_nonneg_left hn_pos.le (pow_pos hP_pos s) hP_s
        have h2z : (2 : ℝ) ^ (-(R : ℤ)) ≤ 1 := by
          rw [zpow_neg, zpow_natCast]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
        calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R
            ≤ 1 * (Real.log (n : ℝ)) ^ A_R := mul_le_mul_of_nonneg_right h2z (by positivity)
          _ ≤ (n : ℝ) / P ^ s := by linarith
      have hW_bound : ∀ t ∈ Set.Icc P (2 * P), |1 / (t - 1)| ≤ 2 / P := by
        intro t ht
        have hP2 : 2 ≤ P := le_trans hnd2 hP_lo
        have ht1 : P / 2 ≤ t - 1 := by linarith [ht.1]
        have ht_sub_pos : 0 < t - 1 := by linarith [ht.1, hP2]
        rw [abs_of_nonneg (one_div_nonneg.mpr ht_sub_pos.le), one_div, inv_le_comm₀ ht_sub_pos (div_pos (by norm_num) hP_pos), inv_div]
        linarith
      have h_res := (hexp_n P (B_k k) A h_fn (fun t => 1 / (t - 1)) (2 / P) hA_nz
        hP_lo hP_hi hI_prime hA_range hh_le hPhase hW_bound (by positivity)).1.2
      calc ‖∑ p ∈ B_k k, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
            eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))‖
          ≤ C₂e * (2 / P) * P * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_res
        _ = 2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by field_simp [hP_pos.ne']
  -- Bound ∑_{p ∈ D_r}
  have h_sum_split : ∑ p ∈ D_r, eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
        ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) =
      (∑ p ∈ D_r, (∏ s ∈ Finset.Icc 1 r, eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) / (h_mod : ℝ)) -
          ∏ s ∈ Finset.Icc 1 r, Psi_mod ((n : ℝ) / (p : ℝ) ^ s)) *
        ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)) +
      (∑ k ∈ Finset.range (K + 1), ∑ p ∈ B_k k,
        (∏ s ∈ Finset.Icc 1 r, Psi_mod ((n : ℝ) / (p : ℝ) ^ s)) *
        ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)) := by
    have h1 : ∑ p ∈ D_r, eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) =
        ∑ p ∈ D_r, (∏ s ∈ Finset.Icc 1 r, eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) / (h_mod : ℝ))) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) :=
      Finset.sum_congr rfl (fun p hp => by rw [hv_on_D p hp])
    rw [h1]
    have h2 : ∑ p ∈ D_r, (∏ s ∈ Finset.Icc 1 r, Psi_mod ((n : ℝ) / (p : ℝ) ^ s)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) =
        ∑ k ∈ Finset.range (K + 1), ∑ p ∈ B_k k,
          (∏ s ∈ Finset.Icc 1 r, Psi_mod ((n : ℝ) / (p : ℝ) ^ s)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) := by
      conv_lhs => rw [hD_eq, Finset.sum_biUnion (fun k₁ hk₁ k₂ hk₂ hne => hB_disj hk₁ hk₂ hne)]
    rw [← h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => by ring)
  rw [h_sum_split]
  have h_err_bd : ‖∑ p ∈ D_r, (∏ s ∈ Finset.Icc 1 r, eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) / (h_mod : ℝ)) -
        ∏ s ∈ Finset.Icc 1 r, Psi_mod ((n : ℝ) / (p : ℝ) ^ s)) *
      ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)‖ ≤
      (1 + 2 * (h_mod : ℝ)) ^ R * (R : ℝ) * ((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₂e) / Real.log (n : ℝ) := by
    let I_s := Finset.Icc 1 r
    have h_tr : ‖∑ p ∈ D_r, _‖ ≤ (1 + 2 * (h_mod : ℝ)) ^ R * ∑ s ∈ I_s,
        (∑ p ∈ D_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re) := by
      calc ‖∑ p ∈ D_r, _‖ ≤ ∑ p ∈ D_r, ‖_‖ := norm_sum_le _ _
        _ ≤ ∑ p ∈ D_r, ((1 + 2 * (h_mod : ℝ)) ^ I_s.card *
              ∑ s ∈ I_s, (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re) * (Real.log (p : ℝ) / ((p : ℝ) - 1)) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
            have hw_nn : 0 ≤ Real.log (p : ℝ) / ((p : ℝ) - 1) := by
              have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
              have : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
              exact div_nonneg (Real.log_nonneg this) this.le
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw_nn]
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
              (∑ p ∈ D_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re) := by
            have hcard : I_s.card ≤ R := by dsimp only [I_s]; rw [Nat.card_Icc]; omega
            have hpow : (1 + 2 * (h_mod : ℝ)) ^ I_s.card ≤ (1 + 2 * (h_mod : ℝ)) ^ R :=
              pow_le_pow_right₀ (by linarith) hcard
            calc ∑ p ∈ D_r, ((1 + 2 * (h_mod : ℝ)) ^ I_s.card *
                  ∑ s ∈ I_s, (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re) * (Real.log (p : ℝ) / ((p : ℝ) - 1))
                = (1 + 2 * (h_mod : ℝ)) ^ I_s.card * ∑ s ∈ I_s, ∑ p ∈ D_r,
                    (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re := by
                  rw [Finset.mul_sum, Finset.sum_comm]
                  refine Finset.sum_congr rfl (fun p _ => ?_)
                  rw [Finset.sum_mul, Finset.mul_sum]
                  refine Finset.sum_congr rfl (fun s _ => by ring)
              _ ≤ (1 + 2 * (h_mod : ℝ)) ^ R * ∑ s ∈ I_s, ∑ p ∈ D_r,
                    (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re := by
                  apply mul_le_mul_of_nonneg_right hpow
                  refine Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun p hp => ?_))
                  have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
                  have hw_nn : 0 ≤ Real.log (p : ℝ) / ((p : ℝ) - 1) := by
                    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
                    have : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
                    exact div_nonneg (Real.log_nonneg this) this.le
                  exact mul_nonneg hw_nn (le_trans (norm_nonneg _) (h_vaaler_pw _))
    have h_B_s : ∀ s ∈ I_s,
        ∑ p ∈ D_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re ≤
        ((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₂e) / Real.log (n : ℝ) := by
      intro s hs
      have h_B_eq : ∑ p ∈ D_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re =
          (∑ p ∈ D_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (b_mod 0).re) +
          ∑ m ∈ nzH, (b_mod m * ∑ k ∈ Finset.range (K + 1), ∑ p ∈ B_k k,
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
        rw [Finset.sum_congr rfl (fun p _ => h_p_eq p), Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        simp_rw [← Complex.re_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        congr 1
        conv_lhs => rw [hD_eq, Finset.sum_biUnion (fun k₁ hk₁ k₂ hk₂ hne => hB_disj hk₁ hk₂ hne)]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => by ring)
      rw [h_B_eq]
      have h_m0_bd : ∑ p ∈ D_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (b_mod 0).re ≤
          (h_mod : ℝ) * (1 + Cm) / Real.log (n : ℝ) := by
        have hb0_re : (b_mod 0).re = (h_mod : ℝ) / ((H : ℝ) + 1) := by rw [hb_mod0, Complex.ofReal_re]
        rw [← Finset.sum_mul, hb0_re]
        have hsub : D_r ⊆ (Finset.Icc 3 n).filter Nat.Prime := fun p hp =>
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1,
            le_trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2 (Nat.sqrt_le_self n)⟩,
            (Finset.mem_filter.mp hp).2.1⟩
        have hmert_n : ∑ p ∈ D_r, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ Real.log (n : ℝ) + Cm := by
          calc ∑ p ∈ D_r, Real.log (p : ℝ) / ((p : ℝ) - 1)
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
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
        have h_log_3 : (Real.log (n : ℝ) + Cm) / (Real.log (n : ℝ)) ^ (R + 2) ≤ (1 + Cm) / (Real.log (n : ℝ)) ^ 2 := by
          calc (Real.log (n : ℝ) + Cm) / (Real.log (n : ℝ)) ^ (R + 2)
              ≤ ((1 + Cm) * Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 3 := by
                apply div_le_div₀ (by positivity)
                · nlinarith [hCm_pos]
                · positivity
                · exact pow_le_pow_right₀ (by linarith) (by omega)
            _ = (1 + Cm) / (Real.log (n : ℝ)) ^ 2 := by field_simp [hlogn_pos.ne']
        calc (∑ p ∈ D_r, Real.log (p : ℝ) / ((p : ℝ) - 1)) * ((h_mod : ℝ) / ((H : ℝ) + 1))
            ≤ (Real.log (n : ℝ) + Cm) * ((h_mod : ℝ) * (2 / (Real.log (n : ℝ)) ^ (R + 2))) := by
              apply mul_le_mul hmert_n _ (by positivity) (by positivity)
              rw [div_eq_mul_one_div, div_eq_mul_one_div]
              exact mul_le_mul_of_nonneg_left hH_inv (by positivity)
          _ = 2 * (h_mod : ℝ) * ((Real.log (n : ℝ) + Cm) / (Real.log (n : ℝ)) ^ (R + 2)) := by ring
          _ ≤ 2 * (h_mod : ℝ) * ((1 + Cm) / (Real.log (n : ℝ)) ^ 2) :=
              mul_le_mul_of_nonneg_left h_log_3 (by positivity)
          _ ≤ (h_mod : ℝ) * (1 + Cm) / Real.log (n : ℝ) := by
              rw [div_le_div_iff₀ (by positivity) hlogn_pos]; nlinarith [hCm_pos]
      have h_nz_bd : ∑ m ∈ nzH, (b_mod m * ∑ k ∈ Finset.range (K + 1), ∑ p ∈ B_k k,
            ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
              eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))).re ≤
          8 * (h_mod : ℝ) * C₂e / Real.log (n : ℝ) := by
        calc ∑ m ∈ nzH, (b_mod m * ∑ k ∈ Finset.range (K + 1), ∑ p ∈ B_k k,
                ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
                  eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))).re
            ≤ ∑ m ∈ nzH, ‖b_mod m * ∑ k ∈ Finset.range (K + 1), ∑ p ∈ B_k k,
                ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
                  eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))‖ :=
              Finset.sum_le_sum (fun m _ => Complex.re_le_norm _)
          _ ≤ ∑ m ∈ nzH, ((h_mod : ℝ) / ((H : ℝ) + 1)) *
                (((K : ℝ) + 1) * (2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) := by
              refine Finset.sum_le_sum (fun m hm => ?_)
              rw [norm_mul]
              apply mul_le_mul (hb_mod_norm m) _ (norm_nonneg _) (by positivity)
              calc ‖∑ k ∈ Finset.range (K + 1), _‖
                  ≤ ∑ k ∈ Finset.range (K + 1), ‖∑ p ∈ B_k k, _‖ := norm_sum_le _ _
                _ ≤ ∑ _k ∈ Finset.range (K + 1), (2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
                    refine Finset.sum_le_sum (fun k _ => ?_)
                    have h_res := h_B_exp k {s} (Finset.singleton_subset_iff.mpr hs)
                      (fun _ => m) ⟨s, Finset.mem_singleton_self s, (Finset.mem_filter.mp hm).2⟩
                      (fun _ _ => abs_le.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1))
                    simpa using h_res
                _ = ((K : ℝ) + 1) * (2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
                    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ = (nzH.card : ℝ) * ((h_mod : ℝ) / ((H : ℝ) + 1)) *
                (((K : ℝ) + 1) * (2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) := by
              simp [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ (2 * (h_mod : ℝ)) * ((2 * Real.log (n : ℝ)) * (2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) := by
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
                  _ ≤ 2 * (h_mod : ℝ) := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
              · exact mul_le_mul_of_nonneg_right hK_le (by positivity)
          _ ≤ 8 * (h_mod : ℝ) * C₂e / Real.log (n : ℝ) := by
              have h_rpow : (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) = 1 / (Real.log (n : ℝ)) ^ (R + 2) := by
                rw [Real.rpow_neg hlogn_pos.le, one_div]
                congr 1; norm_cast; rw [Real.rpow_natCast]
              rw [h_rpow]
              have h_pow_ge : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ (R + 2) :=
                pow_le_pow_right₀ (by linarith) (by omega)
              have h1 : Real.log (n : ℝ) * (1 / (Real.log (n : ℝ)) ^ (R + 2)) ≤ 1 / Real.log (n : ℝ) := by
                rw [mul_one_div, div_le_div_iff₀ (by positivity) hlogn_pos]
                calc Real.log (n : ℝ) * Real.log (n : ℝ) = (Real.log (n : ℝ)) ^ 2 := by ring
                  _ ≤ (Real.log (n : ℝ)) ^ (R + 2) := h_pow_ge
                  _ = 1 * (Real.log (n : ℝ)) ^ (R + 2) := (one_mul _).symm
              calc 2 * (h_mod : ℝ) * (2 * Real.log (n : ℝ) * (2 * C₂e * (1 / (Real.log (n : ℝ)) ^ (R + 2))))
                  = 8 * (h_mod : ℝ) * C₂e * (Real.log (n : ℝ) * (1 / (Real.log (n : ℝ)) ^ (R + 2))) := by ring
                _ ≤ 8 * (h_mod : ℝ) * C₂e * (1 / Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left h1 (by positivity)
                _ = 8 * (h_mod : ℝ) * C₂e / Real.log (n : ℝ) := by ring
      linarith [show (h_mod : ℝ) * (1 + Cm) / Real.log (n : ℝ) + 8 * (h_mod : ℝ) * C₂e / Real.log (n : ℝ) =
          ((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₂e) / Real.log (n : ℝ) from by ring]
    calc ‖∑ p ∈ D_r, _‖ ≤ (1 + 2 * (h_mod : ℝ)) ^ R * ∑ s ∈ I_s,
          (∑ p ∈ D_r, (Real.log (p : ℝ) / ((p : ℝ) - 1)) * (B_mod ((n : ℝ) / (p : ℝ) ^ s)).re) := h_tr
      _ ≤ (1 + 2 * (h_mod : ℝ)) ^ R * ∑ _s ∈ I_s,
            (((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₂e) / Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s hs => h_B_s s hs)) (by positivity)
      _ ≤ (1 + 2 * (h_mod : ℝ)) ^ R * (R : ℝ) *
            (((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₂e) / Real.log (n : ℝ)) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show r + 1 - 1 = r from by omega]
          have hr_le : (r : ℝ) ≤ (R : ℝ) := by exact_mod_cast hrR
          gcongr; positivity
      _ = (1 + 2 * (h_mod : ℝ)) ^ R * (R : ℝ) * ((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₂e) / Real.log (n : ℝ) := by ring
  have h_main_bd : ‖∑ k ∈ Finset.range (K + 1), ∑ p ∈ B_k k,
        (∏ s ∈ Finset.Icc 1 r, Psi_mod ((n : ℝ) / (p : ℝ) ^ s)) *
        ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)‖ ≤
      4 * C₂e / Real.log (n : ℝ) := by
    let I_s := Finset.Icc 1 r
    have h_k_bd : ∀ k ∈ Finset.range (K + 1),
        ‖∑ p ∈ B_k k, (∏ s ∈ I_s, Psi_mod ((n : ℝ) / (p : ℝ) ^ s)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)‖ ≤
        (Real.log (n : ℝ)) ^ r * (2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
      intro k _
      have h_eq : ∑ p ∈ B_k k, (∏ s ∈ I_s, Psi_mod ((n : ℝ) / (p : ℝ) ^ s)) *
            ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) =
          ∑ h ∈ I_s.pi (fun _ => nzH), (∏ s ∈ I_s.attach, c_mod (h s.1 s.2)) *
            ∑ p ∈ B_k k, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
              eExp (∑ s ∈ I_s, ((if hs : s ∈ I_s then h s hs else 0 : ℤ) : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s)) := by
        have h_inner : ∀ p ∈ B_k k,
            (∏ s ∈ I_s, Psi_mod ((n : ℝ) / (p : ℝ) ^ s)) * ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) =
            ∑ h ∈ I_s.pi (fun _ => nzH),
              (∏ s ∈ I_s.attach, c_mod (h s.1 s.2)) *
                (((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
                  eExp (∑ s ∈ I_s, ((if hs : s ∈ I_s then h s hs else 0 : ℤ) : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))) := by
          intro p _
          dsimp only [Psi_mod]
          rw [Finset.prod_sum, Finset.sum_mul]
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
        calc ∑ p ∈ B_k k, (∏ s ∈ I_s, Psi_mod ((n : ℝ) / (p : ℝ) ^ s)) * ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)
            = ∑ p ∈ B_k k, ∑ h ∈ I_s.pi (fun _ => nzH),
                (∏ s ∈ I_s.attach, c_mod (h s.1 s.2)) *
                  (((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
                    eExp (∑ s ∈ I_s, ((if hs : s ∈ I_s then h s hs else 0 : ℤ) : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))) :=
              Finset.sum_congr rfl h_inner
          _ = ∑ h ∈ I_s.pi (fun _ => nzH), ∑ p ∈ B_k k,
                (∏ s ∈ I_s.attach, c_mod (h s.1 s.2)) *
                  (((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
                    eExp (∑ s ∈ I_s, ((if hs : s ∈ I_s then h s hs else 0 : ℤ) : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))) :=
              Finset.sum_comm
          _ = _ := by
              refine Finset.sum_congr rfl (fun h _ => ?_)
              rw [Finset.mul_sum]
      rw [h_eq]
      calc ‖∑ h ∈ I_s.pi (fun _ => nzH), _‖
          ≤ ∑ h ∈ I_s.pi (fun _ => nzH), ‖(∏ s ∈ I_s.attach, c_mod (h s.1 s.2)) *
              ∑ p ∈ B_k k, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
                eExp (∑ s ∈ I_s, ((if hs : s ∈ I_s then h s hs else 0 : ℤ) : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ h ∈ I_s.pi (fun _ => nzH), (∏ s ∈ I_s.attach, ‖c_mod (h s.1 s.2)‖) *
              (2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
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
              exact abs_le.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_pi.mp hh s hs)).1)
            exact h_B_exp k I_s Subset.rfl (fun s => if hs : s ∈ I_s then h s hs else 0)
              ⟨1, h1_mem, hh1_ne⟩ hh_le
        _ = (∑ h ∈ I_s.pi (fun _ => nzH), ∏ s ∈ I_s.attach, ‖c_mod (h s.1 s.2)‖) *
              (2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by rw [← Finset.sum_mul]
        _ = (∏ _s ∈ I_s, ∑ m ∈ nzH, ‖c_mod m‖) * (2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
            congr 1; rw [Finset.prod_sum]
        _ = (∑ m ∈ nzH, ‖c_mod m‖) ^ r * (2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
            rw [Finset.prod_const, show I_s.card = r from by dsimp only [I_s]; rw [Nat.card_Icc]; omega]
        _ ≤ (Real.log (n : ℝ)) ^ r * (2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
              (le_trans h_L1 hlogH_le) r
    have h_rpow : (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) = 1 / (Real.log (n : ℝ)) ^ (R + 2) := by
      rw [Real.rpow_neg hlogn_pos.le, one_div]; congr 1; norm_cast
    calc ‖∑ k ∈ Finset.range (K + 1), _‖
        ≤ ∑ k ∈ Finset.range (K + 1), ‖∑ p ∈ B_k k, _‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range (K + 1), ((Real.log (n : ℝ)) ^ r * (2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) :=
          Finset.sum_le_sum h_k_bd
      _ = ((K : ℝ) + 1) * ((Real.log (n : ℝ)) ^ r * (2 * C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (2 * Real.log (n : ℝ)) * ((Real.log (n : ℝ)) ^ R * (2 * C₂e * (1 / (Real.log (n : ℝ)) ^ (R + 2)))) := by
          rw [h_rpow]
          have h_pow_rR : (Real.log (n : ℝ)) ^ r ≤ (Real.log (n : ℝ)) ^ R := pow_le_pow_right₀ (by linarith) hrR
          exact mul_le_mul hK_le (mul_le_mul_of_nonneg_right h_pow_rR (by positivity))
            (by positivity) (by positivity)
      _ = 4 * C₂e / Real.log (n : ℝ) := by
          have hln0 : Real.log (n : ℝ) ≠ 0 := hlogn_pos.ne'
          rw [show R + 2 = (R + 1) + 1 from by omega, pow_succ, pow_succ]
          field_simp [hln0]; ring
  calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
    _ ≤ (1 + 2 * (h_mod : ℝ)) ^ R * (R : ℝ) * ((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₂e) / Real.log (n : ℝ) +
        4 * C₂e / Real.log (n : ℝ) := add_le_add h_err_bd h_main_bd
    _ ≤ M_clean * (1 / Real.log (n : ℝ)) := by
        rw [show (1 + 2 * (h_mod : ℝ)) ^ R * (R : ℝ) * ((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₂e) / Real.log (n : ℝ) +
            4 * C₂e / Real.log (n : ℝ) =
            ((1 + 2 * (h_mod : ℝ)) ^ R * (R : ℝ) * ((h_mod : ℝ) * (1 + Cm) + 8 * (h_mod : ℝ) * C₂e) + 4 * C₂e) *
              (1 / Real.log (n : ℝ)) from by ring]
        exact mul_le_mul_of_nonneg_right (by dsimp only [M_clean]; linarith) (by positivity)


end GrasGreenbergBrocard
