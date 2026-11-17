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
import GrasGreenbergBrocard.ValuationParityModCollar
import GrasGreenbergBrocard.ValuationParityModInterCollar

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false
set_option maxHeartbeats 800000

noncomputable section

open Real Finset BigOperators Asymptotics Filter
open Classical

namespace GrasGreenbergBrocard



theorem small_prime_mod_band_isBigO (h_mod z : ℕ) (hh_mod : 2 ≤ h_mod)
    (hz1 : 1 ≤ z) (hz2 : z < h_mod)
    (δ a b : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    (fun n : ℕ => ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
        p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b),
      eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
        ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ))
      =O[atTop] (fun n : ℕ => 1 / Real.log (n : ℝ)) := by
  set R := Nat.floor (1 / δ)
  set A_R := 6 * R + 30
  have hR3 : 3 ≤ R := by
    rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hδ0]; push_cast; linarith
  have h_col_sum : ∀ r ∈ Finset.Icc 2 R,
      (fun n : ℕ => ∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
          (p : ℝ) ∈ collar n r A_R)),
        eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ))
        =O[atTop] (fun n : ℕ => 1 / Real.log (n : ℝ)) := fun r hr =>
    collar_mod_isBigO h_mod z hh_mod hz1 hz2 δ a b hδ0 hδ1 r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2
  have h_int_sum : ∀ r ∈ Finset.Icc 2 R,
      (fun n : ℕ => ∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
          (p : ℝ) ∈ interCollar n r A_R)),
        eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ))
        =O[atTop] (fun n : ℕ => 1 / Real.log (n : ℝ)) := fun r hr =>
    interCollar_mod_isBigO h_mod z hh_mod hz1 hz2 δ a b hδ0 hδ1 r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2
  have h_fin_sum : (fun n : ℕ => ∑ r ∈ Finset.Icc 2 R,
      ((∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
          (p : ℝ) ∈ collar n r A_R)),
        eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)) +
       (∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
          (p : ℝ) ∈ interCollar n r A_R)),
        eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ))))
      =O[atTop] (fun n : ℕ => 1 / Real.log (n : ℝ)) :=
    Asymptotics.IsBigO.sum (fun r hr => (h_col_sum r hr).add (h_int_sum r hr))
  refine h_fin_sum.congr' ?_ EventuallyEq.rfl
  have h_rpow_all : ∀ᶠ n : ℕ in atTop, ∀ r ∈ Finset.Icc 2 R,
      (Real.log (n : ℝ)) ^ A_R / (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) ≤ 1 := by
    rw [Filter.eventually_all_finset]
    intro r _
    have ht := log_pow_div_rpow_tendsto_zero A_R (by positivity : (0 : ℝ) < 1 / ((r : ℝ) * ((r : ℝ) + 1)))
    exact (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)
  filter_upwards [(tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2),
    Filter.eventually_ge_atTop 16, h_rpow_all] with n hln hn hrpow_all
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  let S := (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
    p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b)
  let B : ℕ → Finset ℕ := fun r =>
    S.filter (fun p : ℕ => (p : ℝ) ∈ collar n r A_R ∪ interCollar n r A_R)
  have hS_eq : S = (Finset.Icc 2 R).biUnion B := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_Icc, B, Finset.mem_filter]
    constructor
    · intro hp
      have hp_nd : (n : ℝ) ^ δ < (p : ℝ) := hp.2.2.1
      have hp_sq : p ≤ Nat.sqrt n := hp.1.2
      have hp_le_n12 : (p : ℝ) ≤ (n : ℝ) ^ (1 / (2 : ℝ)) := by
        rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by positivity) hn_pos.le]
        exact_mod_cast (by have := Nat.sqrt_le' n; nlinarith : p ^ 2 ≤ n)
      have h_n1R1_le : (n : ℝ) ^ (1 / ((R : ℝ) + 1)) ≤ (n : ℝ) ^ δ := by
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
        have hlt : 1 / δ < (R : ℝ) + 1 := Nat.lt_floor_add_one (1 / δ)
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ hδ0] at hlt
        linarith
      have h_lt_n1R1 : (n : ℝ) ^ (1 / ((R : ℝ) + 1)) < (p : ℝ) := lt_of_le_of_lt h_n1R1_le hp_nd
      let T := (Finset.Icc 2 R).filter (fun r : ℕ => (p : ℝ) ≤ (n : ℝ) ^ (1 / (r : ℝ)))
      have h2_mem : 2 ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, by
        simpa using hp_le_n12⟩
      have hT_ne : T.Nonempty := ⟨2, h2_mem⟩
      let r := T.max' hT_ne
      have hr_mem : r ∈ T := Finset.max'_mem T hT_ne
      have hr_Icc : r ∈ Finset.Icc 2 R := (Finset.mem_filter.mp hr_mem).1
      have hr_le : (p : ℝ) ≤ (n : ℝ) ^ (1 / (r : ℝ)) := (Finset.mem_filter.mp hr_mem).2
      have hr_gt_next : (n : ℝ) ^ (1 / ((r : ℝ) + 1)) < (p : ℝ) := by
        by_cases hrR_eq : r = R
        · rw [hrR_eq]; exact h_lt_n1R1
        · have hr1_mem : r + 1 ∈ Finset.Icc 2 R := by
            have := Finset.mem_Icc.mp hr_Icc; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          by_contra hle
          push_neg at hle
          have : r + 1 ∈ T := Finset.mem_filter.mpr ⟨hr1_mem, by simpa using hle⟩
          have := Finset.le_max' T (r + 1) this
          omega
      refine ⟨r, hr_Icc, hp, ?_⟩
      by_cases hcol : (n : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)) < (p : ℝ)
      · left; exact ⟨hcol, hr_le⟩
      · right; exact ⟨hr_gt_next, le_of_not_gt hcol⟩
    · rintro ⟨r, _, hp, _⟩; exact hp
  have hB_disj : Set.PairwiseDisjoint (Finset.Icc 2 R : Set ℕ) B := by
    intro r₁ hr₁ r₂ hr₂ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have hmem₁ := (Finset.mem_filter.mp hp₁).2
    have hmem₂ := (Finset.mem_filter.mp hp₂).2
    have h_gap : ∀ r ∈ Finset.Icc 2 R,
        (n : ℝ) ^ (1 / ((r : ℝ) + 1)) < (n : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)) := by
      intro r hr
      have hr_pos : (0 : ℝ) < (r : ℝ) := by have := (Finset.mem_Icc.mp hr).1; exact_mod_cast (by omega : 0 < r)
      rw [lt_div_iff₀ (by positivity)]
      have hpow_gt : (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)) ≤ (Real.log (n : ℝ)) ^ A_R := by
        rw [← Real.rpow_natCast (Real.log (n : ℝ)) A_R]
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        exact div_le_self (by positivity) (by have := (Finset.mem_Icc.mp hr).1; exact_mod_cast (by omega : 1 ≤ r))
      have h1 : (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) := by
        have := (div_le_iff₀ (by positivity)).mp (hrpow_all r hr)
        linarith
      have h2 : (n : ℝ) ^ (1 / ((r : ℝ) + 1)) * (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) = (n : ℝ) ^ (1 / (r : ℝ)) := by
        rw [← Real.rpow_add hn_pos]
        congr 1; field_simp [hr_pos.ne', by positivity : (r : ℝ) + 1 ≠ 0]; ring
      have hlt_pow : (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)) < (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) := by
        by_cases h_eq : (Real.log (n : ℝ)) ^ A_R = (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1)))
        · have hr2' : 2 ≤ r := (Finset.mem_Icc.mp hr).1
          have h_strict : (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)) < (Real.log (n : ℝ)) ^ A_R := by
            rw [← Real.rpow_natCast (Real.log (n : ℝ)) A_R]
            apply Real.rpow_lt_rpow_of_exponent_lt (by linarith)
            exact div_lt_self (by positivity : (0 : ℝ) < (A_R : ℝ)) (by exact_mod_cast (by omega : 1 < r))
          linarith
        · exact lt_of_le_of_lt hpow_gt (lt_of_le_of_ne h1 h_eq)
      nlinarith [Real.rpow_pos_of_pos hn_pos (1 / ((r : ℝ) + 1))]
    have h_bounds : ∀ r ∈ Finset.Icc 2 R,
        (p : ℝ) ∈ collar n r A_R ∪ interCollar n r A_R →
        (n : ℝ) ^ (1 / ((r : ℝ) + 1)) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 / (r : ℝ)) := by
      intro r hr hp
      rcases hp with hcol | hint
      · exact ⟨lt_trans (h_gap r hr) hcol.1, hcol.2⟩
      · exact ⟨hint.1, le_trans hint.2 (div_le_self (by positivity) (Real.rpow_ge_one (by linarith) (by positivity)))⟩
    have hb₁ := h_bounds r₁ hr₁ hmem₁
    have hb₂ := h_bounds r₂ hr₂ hmem₂
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hle : (r₁ : ℝ) + 1 ≤ (r₂ : ℝ) := by exact_mod_cast hlt
      have : (n : ℝ) ^ (1 / (r₂ : ℝ)) ≤ (n : ℝ) ^ (1 / ((r₁ : ℝ) + 1)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
        exact one_div_le_one_div_of_le (by positivity) hle
      linarith [hb₁.1, hb₂.2]
    · have hle : (r₂ : ℝ) + 1 ≤ (r₁ : ℝ) := by exact_mod_cast hlt
      have : (n : ℝ) ^ (1 / (r₁ : ℝ)) ≤ (n : ℝ) ^ (1 / ((r₂ : ℝ) + 1)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
        exact one_div_le_one_div_of_le (by positivity) hle
      linarith [hb₂.1, hb₁.2]
  have h_sum_B : ∀ r ∈ Finset.Icc 2 R,
      ∑ p ∈ B r, eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
        ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) =
      (∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
          (p : ℝ) ∈ collar n r A_R)),
        eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)) +
      (∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
          (p : ℝ) ∈ interCollar n r A_R)),
        eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
          ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)) := by
    intro r _
    let C1 := (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
      p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
      (p : ℝ) ∈ collar n r A_R)
    let I1 := (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
      p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
      (p : ℝ) ∈ interCollar n r A_R)
    have hB_eq : B r = C1 ∪ I1 := by
      ext p; simp only [B, C1, I1, S, Finset.mem_union, Finset.mem_filter, Set.mem_union]
      tauto
    have hdisj_ci : Disjoint C1 I1 := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      have h1 := (Finset.mem_filter.mp hp1).2.2.2.2.2.1
      have h2 := (Finset.mem_filter.mp hp2).2.2.2.2.2.2
      linarith
    rw [hB_eq, Finset.sum_union hdisj_ci]
  calc ∑ r ∈ Finset.Icc 2 R, _ = ∑ r ∈ Finset.Icc 2 R, ∑ p ∈ B r, _ :=
        Finset.sum_congr rfl (fun r hr => (h_sum_B r hr).symm)
    _ = ∑ p ∈ S, _ := by
        conv_rhs => rw [hS_eq, Finset.sum_biUnion (fun r₁ hr₁ r₂ hr₂ hne => hB_disj hr₁ hr₂ hne)]

theorem upper_band_mod_isBigO (h_mod z : ℕ) (hh_mod : 2 ≤ h_mod)
    (hz1 : 1 ≤ z) (hz2 : z < h_mod)
    (δ a b : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    (fun n : ℕ => ∑ p ∈ (Finset.Icc (Nat.sqrt n + 1) n).filter (fun p : ℕ =>
        p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 - δ)),
      (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) *
        eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)))
      =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  set R := Nat.floor (1 / δ)
  set A_R := 6 * R + 30
  obtain ⟨η', η, hη', hη, C₁e, C₂e, C₃e, hC₁e, hC₂e, hC₃e, hExp⟩ :=
    prime_exp_sum_bounds_mod h_mod hh_mod δ hδ0 hδ1
  obtain ⟨Cm, hCm_pos, hCm⟩ := mertens_sum_le
  obtain ⟨Cθ, hCθ_pos, hCθ⟩ := thetaPrime_le_linear
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_n1d_12 : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 - δ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := by
    have ht := log_pow_div_rpow_tendsto_zero 12 hδ0
    filter_upwards [Filter.eventually_ge_atTop 4,
      (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)] with n hn hsm
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h1 := (div_le_iff₀ (by positivity)).mp hsm
    have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    rw [le_div_iff₀ (pow_pos hlogn_pos 12)]
    calc (n : ℝ) ^ (1 - δ) * (Real.log (n : ℝ)) ^ 12 ≤ (n : ℝ) ^ (1 - δ) * (n : ℝ) ^ δ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ = (n : ℝ) ^ ((1 - δ) + δ) := (Real.rpow_add hn_pos _ _).symm
      _ = (n : ℝ) := by ring_nf; exact Real.rpow_one _
  have h_nd_AR : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) ^ δ := by
    have ht := log_pow_div_rpow_tendsto_zero A_R hδ0
    filter_upwards [Filter.eventually_ge_atTop 4,
      (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)] with n hn hsm
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have := (div_le_iff₀ (by positivity)).mp hsm
    linarith
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
  let M_clean : ℝ := Cθ + (h_mod : ℝ) * (1 + Cm) + 4 * (h_mod : ℝ) * C₂e + 4 * C₂e + 1
  refine Asymptotics.IsBigO.of_bound M_clean ?_
  filter_upwards [Filter.eventually_ge_atTop 16, hExp, h_n1d_12, h_nd_AR,
    hlog_inf.eventually (eventually_ge_atTop 100), h_log_pow_R] with
    n hn hexp_n hn1d12 hndAR hln100 hlogH_le
  dsimp only at hexp_n
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  rw [Real.norm_of_nonneg hn_pos.le]
  let H := Nat.floor ((Real.log (n : ℝ)) ^ (R + 2))
  have hH_ge1 : 1 ≤ H := Nat.le_floor (by norm_num; exact one_le_pow₀ (by linarith))
  have hH_ge_log : (Real.log (n : ℝ)) ^ (R + 2) / 2 ≤ (H : ℝ) + 1 := by
    have := Nat.lt_floor_add_one ((Real.log (n : ℝ)) ^ (R + 2))
    linarith [show (0 : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) from by positivity]
  let U := (Finset.Icc (Nat.sqrt n + 1) n).filter (fun p : ℕ =>
    p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 - δ))
  have hv_U : ∀ p ∈ U, padicValNat p (Nat.factorial n) = n / p := by
    intro p hp
    have hp_pr := (Finset.mem_filter.mp hp).2.1
    have hsq : Nat.sqrt n + 1 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hn_lt : n < p ^ 2 := by have := Nat.lt_succ_sqrt' n; nlinarith
    exact padicValNat_factorial_eq_div_of_lt_sq hp_pr hn_lt
  -- Replace v_p(n!) * log p with (n / p : ℝ) * log p + O(Cθ * n)
  have h_frac_err : ‖(∑ p ∈ U, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) *
        eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) -
      (n : ℝ) * (∑ p ∈ U, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
        eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) / (h_mod : ℝ)))‖ ≤ Cθ * (n : ℝ) := by
    have h_eq : (∑ p ∈ U, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) -
        (n : ℝ) * (∑ p ∈ U, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
          eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) / (h_mod : ℝ))) =
        ∑ p ∈ U, (((((n / p : ℕ) : ℝ) - (n : ℝ) / (p : ℝ)) * Real.log (p : ℝ) : ℝ) : ℂ) *
          eExp ((z : ℝ) * ((n / p : ℕ) : ℝ) / (h_mod : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hp_pr := (Finset.mem_filter.mp hp).2.1
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pr.pos
      have hfl : Int.floor ((n : ℝ) / (p : ℝ)) = ((n / p : ℕ) : ℤ) := by
        rw [Int.floor_eq_iff]
        constructor
        · rw [Int.cast_natCast, le_div_iff₀ hp_pos]; exact_mod_cast Nat.div_mul_le_self n p
        · rw [Int.cast_natCast, div_lt_iff₀ hp_pos]
          have h_nat : n < (n / p + 1) * p := Nat.lt_div_mul_add hp_pr.pos
          exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((n / p + 1 : ℕ) : ℝ) * (p : ℝ))
      rw [hv_U p hp, hfl, Int.cast_natCast]
      push_cast; field_simp [hp_pos.ne']
    rw [h_eq]
    calc ‖∑ p ∈ U, _‖ ≤ ∑ p ∈ U, ‖(((((n / p : ℕ) : ℝ) - (n : ℝ) / (p : ℝ)) * Real.log (p : ℝ) : ℝ) : ℂ) *
          eExp ((z : ℝ) * ((n / p : ℕ) : ℝ) / (h_mod : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ U, Real.log (p : ℝ) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hp_pr := (Finset.mem_filter.mp hp).2.1
          have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pr.pos
          have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)
          rw [norm_mul, show ‖eExp ((z : ℝ) * ((n / p : ℕ) : ℝ) / (h_mod : ℝ))‖ = 1 from by
            exact norm_eExp _, mul_one,
            Complex.norm_real, Real.norm_eq_abs,
            abs_mul, abs_of_nonneg hlogp_nn]
          have h1 : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / (p : ℝ) := by
            rw [le_div_iff₀ hp_pos]; exact_mod_cast Nat.div_mul_le_self n p
          have h2 : (n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ) < 1 := by
            have h_nat : n < (n / p + 1) * p := Nat.lt_div_mul_add hp_pr.pos
            have hltR : (n : ℝ) < (((n / p : ℕ) : ℝ) + 1) * (p : ℝ) := by exact_mod_cast h_nat
            have := (div_lt_iff₀ hp_pos).mpr hltR
            linarith
          have habs : |((n / p : ℕ) : ℝ) - (n : ℝ) / (p : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
          nlinarith
      _ ≤ ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, Real.log (p : ℝ) := by
          have hsub : U ⊆ (Finset.Icc 2 n).filter Nat.Prime := fun p hp =>
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hp).2.1.two_le,
              (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2⟩, (Finset.mem_filter.mp hp).2.1⟩
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
            Real.log_nonneg (by exact_mod_cast (by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; omega : 1 ≤ p)))
      _ = thetaPrime (n : ℝ) := by
          unfold thetaPrime; congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Nat.floor_natCast]
      _ ≤ Cθ * (n : ℝ) := hCθ (n : ℝ) (by exact_mod_cast (by omega : 1 ≤ n))
  -- Now bound ∑_{p ∈ U} (log p / p) * e(z ⌊n/p⌋ / h_mod)
  let L := (Nat.sqrt n : ℝ)
  have hL_ge1 : 1 ≤ L := by
    have : 4 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
    dsimp only [L]; exact_mod_cast (by omega : 1 ≤ Nat.sqrt n)
  let K := Nat.clog 2 n + 1
  let B_k : ℕ → Finset ℕ := fun k => U.filter (fun p => L * (2 : ℝ) ^ k < (p : ℝ) ∧ (p : ℝ) ≤ L * (2 : ℝ) ^ (k + 1))
  have hU_eq : U = (Finset.range (K + 1)).biUnion B_k := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_range, B_k, Finset.mem_filter]
    constructor
    · intro hp
      have hp_sq : Nat.sqrt n + 1 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      have hp_n : p ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      have hp_gt_L : L < (p : ℝ) := by dsimp only [L]; exact_mod_cast (by omega : Nat.sqrt n < p)
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
        have h2 : Real.log ((p : ℝ) / L) / Real.log 2 ≤ Real.log (n : ℝ) / Real.log 2 := by
          apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
          apply Real.log_le_log (by positivity)
          exact le_trans (div_le_self (by positivity) hL_ge1) (by exact_mod_cast hp_n)
        have h3 : (n : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 n := by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) n
        have h4 : Real.log (n : ℝ) / Real.log 2 ≤ (Nat.clog 2 n : ℝ) := by
          rw [div_le_iff₀ (Real.log_pos (by norm_num))]
          have : Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ Nat.clog 2 n) := Real.log_le_log (by positivity) h3
          rwa [Real.log_pow] at this
        have : (k : ℝ) < (K + 1 : ℝ) := by
          have : (K : ℝ) = (Nat.clog 2 n : ℝ) + 1 := by push_cast [K]; ring
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
    have h1 : Nat.clog 2 n ≤ Nat.log 2 n + 1 := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n).le
    have h2 : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h3 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2
    have hlog2 : (0.69 : ℝ) < Real.log 2 := Real.log_two_gt_d9.trans_le' (by norm_num)
    have hK_R : (K + 1 : ℝ) ≤ (Nat.log 2 n : ℝ) + 3 := by
      have : K + 1 ≤ Nat.log 2 n + 3 := by omega
      exact_mod_cast this
    nlinarith
  obtain ⟨c_mod, b_mod, hb_mod0, hb_mod_norm, h_vaaler_pw, h_L1⟩ :=
    vaaler_mod_approx h_mod hh_mod z hz1 hz2 H hH_ge1
  let allH := Finset.Icc (-(H : ℤ)) (H : ℤ)
  let nzH := allH.filter (· ≠ 0)
  let Psi_mod : ℝ → ℂ := fun x => ∑ m ∈ nzH, c_mod m * eExp ((m : ℝ) * x / (h_mod : ℝ))
  let B_mod : ℝ → ℂ := fun x => ∑ m ∈ allH, b_mod m * eExp ((m : ℝ) * x / (h_mod : ℝ))
  have h_B_exp : ∀ (k : ℕ) (m : ℤ) (hm0 : m ≠ 0) (hmH : |m| ≤ (H : ℤ)),
      ‖∑ p ∈ B_k k, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
          eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ)))‖ ≤
        C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by
    intro k m hm0 hmH
    rcases eq_or_ne (B_k k) ∅ with h_emp | h_ne
    · rw [h_emp, Finset.sum_empty, norm_zero]; positivity
    · let P := L * (2 : ℝ) ^ k
      have hP_lo : (n : ℝ) ^ δ ≤ P := by
        have h_nd_sqrt : (n : ℝ) ^ δ ≤ (Nat.sqrt n : ℝ) := by
          have h_n13 : (n : ℝ) ^ δ ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) hδ1
          have h_rt_lt : (n : ℝ) ^ (1 / 3 : ℝ) ≤ Real.sqrt (n : ℝ) - 1 := by
            have h1 : (n : ℝ) ^ (1 / 3 : ℝ) * 2 ≤ Real.sqrt (n : ℝ) := by
              rw [Real.sqrt_eq_rpow]
              have h_rpow : (n : ℝ) ^ (1 / 6 : ℝ) ≥ 2 := by
                have h26 : (2 : ℝ) ^ (6 : ℕ) ≤ (n : ℝ) := by
                  have : 64 ≤ n := by
                    have : 6 ≤ Real.log (n : ℝ) := by linarith
                    have h_e6 : Real.exp 6 ≤ (n : ℝ) :=
                      (Real.exp_le_iff_le_log hn_pos).mpr (by linarith)
                    have : (64 : ℝ) < Real.exp 6 := by
                      have := Real.exp_one_gt_d9
                      have : (2.7 : ℝ) ^ 6 < Real.exp 6 := by
                        calc (2.7 : ℝ) ^ 6 < (Real.exp 1) ^ 6 := pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
                          _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
                      linarith [show (64 : ℝ) < (2.7 : ℝ) ^ 6 by norm_num]
                    exact_mod_cast (by linarith : (64 : ℝ) ≤ (n : ℝ))
                  exact_mod_cast this
                calc (2 : ℝ) = ((2 : ℝ) ^ (6 : ℕ)) ^ (1 / 6 : ℝ) := by
                      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
                  _ ≤ (n : ℝ) ^ (1 / 6 : ℝ) := Real.rpow_le_rpow (by positivity) h26 (by positivity)
              calc (n : ℝ) ^ (1 / 3 : ℝ) * 2 ≤ (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) := by gcongr
                _ = (n : ℝ) ^ (1 / 3 + 1 / 6 : ℝ) := (Real.rpow_add hn_pos _ _).symm
                _ = (n : ℝ) ^ (1 / 2 : ℝ) := by norm_num
            have h2 : 1 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by positivity)
            linarith
          have h_lt := Nat.lt_succ_sqrt' n
          have h_rt : Real.sqrt (n : ℝ) < (Nat.sqrt n : ℝ) + 1 := by
            rw [Real.sqrt_lt' (by positivity)]; exact_mod_cast h_lt
          linarith
        calc (n : ℝ) ^ δ ≤ L := h_nd_sqrt
          _ = L * 1 := (mul_one _).symm
          _ ≤ L * (2 : ℝ) ^ k := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) (by linarith)
      have hP_pos : 0 < P := lt_of_lt_of_le (by positivity) hP_lo
      have hP_hi : P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := by
        obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr h_ne
        have hp₀_U := (Finset.mem_filter.mp hp₀).1
        have hp₀_le : (p₀ : ℝ) ≤ (n : ℝ) ^ (1 - δ) := (Finset.mem_filter.mp hp₀_U).2.2.2.2
        have hp₀_gt : P < (p₀ : ℝ) := (Finset.mem_filter.mp hp₀).2.1
        exact le_trans hp₀_gt.le (le_trans hp₀_le hn1d12)
      have hI_prime : ∀ p ∈ B_k k, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P := by
        intro p hp
        have hpU := (Finset.mem_filter.mp hp).1
        have hp_pr := (Finset.mem_filter.mp hpU).2.1
        have hp_bd := (Finset.mem_filter.mp hp).2
        refine ⟨hp_pr, hp_bd.1, ?_⟩
        calc (p : ℝ) ≤ L * (2 : ℝ) ^ (k + 1) := hp_bd.2
          _ = 2 * (L * (2 : ℝ) ^ k) := by rw [pow_succ]; ring
      have hA_range : ∀ s ∈ ({1} : Finset ℕ), 1 ≤ s ∧ s ≤ R := fun s hs => by
        rw [Finset.mem_singleton.mp hs]
        have hR1 : 1 ≤ R := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hδ0]; linarith)
        exact ⟨le_rfl, hR1⟩
      have hPhase : ∀ s ∈ ({1} : Finset ℕ), (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) / P ^ s := by
        intro s hs
        rw [Finset.mem_singleton.mp hs, pow_one]
        obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr h_ne
        have hp₀_U := (Finset.mem_filter.mp hp₀).1
        have hp₀_le : (p₀ : ℝ) ≤ (n : ℝ) ^ (1 - δ) := (Finset.mem_filter.mp hp₀_U).2.2.2.2
        have hp₀_gt : P < (p₀ : ℝ) := (Finset.mem_filter.mp hp₀).2.1
        have hP_le_n1d : P ≤ (n : ℝ) ^ (1 - δ) := le_trans hp₀_gt.le hp₀_le
        have h_n_div : (n : ℝ) ^ δ ≤ (n : ℝ) / P := by
          rw [le_div_iff₀ hP_pos]
          calc (n : ℝ) ^ δ * P ≤ (n : ℝ) ^ δ * (n : ℝ) ^ (1 - δ) := mul_le_mul_of_nonneg_left hP_le_n1d (by positivity)
            _ = (n : ℝ) ^ (δ + (1 - δ)) := (Real.rpow_add hn_pos _ _).symm
            _ = (n : ℝ) := by ring_nf; exact Real.rpow_one _
        have h2z : (2 : ℝ) ^ (-(R : ℤ)) ≤ 1 := by
          rw [zpow_neg, zpow_natCast]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
        calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ 1 * (Real.log (n : ℝ)) ^ A_R :=
              mul_le_mul_of_nonneg_right h2z (by positivity)
          _ ≤ (n : ℝ) ^ δ := by linarith [hndAR]
          _ ≤ (n : ℝ) / P := h_n_div
      have hW_bound : ∀ t ∈ Set.Icc P (2 * P), |1 / t| ≤ 1 / P := by
        intro t ht
        have ht_pos : 0 < t := lt_of_lt_of_le hP_pos ht.1
        rw [abs_of_nonneg (by positivity)]
        exact one_div_le_one_div_of_le hP_pos ht.1
      let w : ℝ → ℝ := fun t => 1 / t
      have h_res := (hexp_n P (B_k k) {1} (fun _ => m) w (1 / P)
        ⟨1, Finset.mem_singleton_self 1, hm0⟩ hP_lo hP_hi hI_prime hA_range
        (fun _ _ => hmH) hPhase hW_bound (by positivity)).1.2
      have h_eq_sum : ∑ p ∈ B_k k, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
            eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ))) =
          ∑ p ∈ B_k k, (w (p : ℝ) * Real.log (p : ℝ) : ℂ) *
            eExp (∑ s ∈ ({1} : Finset ℕ), ((m : ℤ) : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s)) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        dsimp only [w]
        rw [← Complex.ofReal_mul, Finset.sum_singleton, pow_one]
        congr 1
        exact congrArg Complex.ofReal (by ring)
      rw [h_eq_sum]
      calc ‖∑ p ∈ B_k k, (w (p : ℝ) * Real.log (p : ℝ) : ℂ) *
            eExp (∑ s ∈ ({1} : Finset ℕ), ((m : ℤ) : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ) ^ s))‖
          ≤ C₂e * (1 / P) * P * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := h_res
        _ = C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) := by field_simp [hP_pos.ne']
  -- Split U into Vaaler error + main term
  have h_U_bd : ‖∑ p ∈ U, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
        eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) / (h_mod : ℝ))‖ ≤
      (h_mod : ℝ) * (1 + Cm) + 4 * (h_mod : ℝ) * C₂e + 4 * C₂e := by
    have h_split : ∑ p ∈ U, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
          eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) / (h_mod : ℝ)) =
        (∑ p ∈ U, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
          (eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) / (h_mod : ℝ)) - Psi_mod ((n : ℝ) / (p : ℝ)))) +
        (∑ k ∈ Finset.range (K + 1), ∑ p ∈ B_k k, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
          Psi_mod ((n : ℝ) / (p : ℝ))) := by
      have h1 : ∑ p ∈ U, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) * Psi_mod ((n : ℝ) / (p : ℝ)) =
          ∑ k ∈ Finset.range (K + 1), ∑ p ∈ B_k k, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) * Psi_mod ((n : ℝ) / (p : ℝ)) := by
        conv_lhs => rw [hU_eq, Finset.sum_biUnion (fun k₁ hk₁ k₂ hk₂ hne => hB_disj hk₁ hk₂ hne)]
      rw [← h1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun p _ => by ring)
    rw [h_split]
    have h_err : ‖∑ p ∈ U, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
          (eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) / (h_mod : ℝ)) - Psi_mod ((n : ℝ) / (p : ℝ)))‖ ≤
        (h_mod : ℝ) * (1 + Cm) + 4 * (h_mod : ℝ) * C₂e := by
      have h_tr : ‖∑ p ∈ U, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
            (eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) / (h_mod : ℝ)) - Psi_mod ((n : ℝ) / (p : ℝ)))‖ ≤
          ∑ p ∈ U, (Real.log (p : ℝ) / (p : ℝ)) * (B_mod ((n : ℝ) / (p : ℝ))).re := by
        calc ‖∑ p ∈ U, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
              (eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) / (h_mod : ℝ)) - Psi_mod ((n : ℝ) / (p : ℝ)))‖ ≤
            ∑ p ∈ U, ‖((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
              (eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) / (h_mod : ℝ)) - Psi_mod ((n : ℝ) / (p : ℝ)))‖ := norm_sum_le _ _
          _ ≤ ∑ p ∈ U, (Real.log (p : ℝ) / (p : ℝ)) * (B_mod ((n : ℝ) / (p : ℝ))).re := by
              refine Finset.sum_le_sum (fun p hp => ?_)
              have hp_sq : Nat.sqrt n + 1 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
              have hw_nn : 0 ≤ Real.log (p : ℝ) / (p : ℝ) := by
                have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
                positivity
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw_nn]
              exact mul_le_mul_of_nonneg_left (h_vaaler_pw _) hw_nn
      have h_B_eq : ∑ p ∈ U, (Real.log (p : ℝ) / (p : ℝ)) * (B_mod ((n : ℝ) / (p : ℝ))).re =
          (∑ p ∈ U, (Real.log (p : ℝ) / (p : ℝ)) * (b_mod 0).re) +
          ∑ m ∈ nzH, (b_mod m * ∑ k ∈ Finset.range (K + 1), ∑ p ∈ B_k k,
            ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
              eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ)))).re := by
        have h_p_eq : ∀ p : ℕ,
            (Real.log (p : ℝ) / (p : ℝ)) * (B_mod ((n : ℝ) / (p : ℝ))).re =
            (Real.log (p : ℝ) / (p : ℝ)) * (b_mod 0).re +
            ∑ m ∈ nzH, (b_mod m * ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
              eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ)))).re := by
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
            have hre : (b_mod m * eExp ((m : ℝ) * ((n : ℝ) / (p : ℝ)) / (h_mod : ℝ)) *
                ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ)).re =
                (Real.log (p : ℝ) / (p : ℝ)) *
                (b_mod m * eExp ((m : ℝ) * ((n : ℝ) / (p : ℝ)) / (h_mod : ℝ))).re := by
              rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; ring
            calc (Real.log (p : ℝ) / (p : ℝ)) *
                  (b_mod m * eExp ((m : ℝ) * ((n : ℝ) / (p : ℝ)) / (h_mod : ℝ))).re
                = (b_mod m * ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
                    eExp ((m : ℝ) * ((n : ℝ) / (p : ℝ)) / (h_mod : ℝ))).re := by
                  rw [← hre]; congr 1; ring
              _ = _ := by congr 2; ring
        rw [Finset.sum_congr rfl (fun p _ => h_p_eq p), Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        simp_rw [← Complex.re_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        congr 1
        conv_lhs => rw [hU_eq, Finset.sum_biUnion (fun k₁ hk₁ k₂ hk₂ hne => hB_disj hk₁ hk₂ hne)]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => by ring)
      have h_m0 : ∑ p ∈ U, (Real.log (p : ℝ) / (p : ℝ)) * (b_mod 0).re ≤ (h_mod : ℝ) * (1 + Cm) := by
        have hb0_re : (b_mod 0).re = (h_mod : ℝ) / ((H : ℝ) + 1) := by rw [hb_mod0, Complex.ofReal_re]
        rw [← Finset.sum_mul, hb0_re]
        have hsub : U ⊆ (Finset.Icc 3 n).filter Nat.Prime := fun p hp => by
          have hp_sq : Nat.sqrt n + 1 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
          have hsq4 : 4 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2⟩,
            (Finset.mem_filter.mp hp).2.1⟩
        have hmert_n : ∑ p ∈ U, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (n : ℝ) + Cm := by
          calc ∑ p ∈ U, Real.log (p : ℝ) / (p : ℝ)
              ≤ ∑ p ∈ U, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
                refine Finset.sum_le_sum (fun p hp => ?_)
                have hp_sq : Nat.sqrt n + 1 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
                have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
                have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < p))
                have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
                exact div_le_div_of_nonneg_left hlogp_nn hp1_pos (by linarith)
            _ ≤ ∑ p ∈ (Finset.Icc 3 n).filter Nat.Prime, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_)
                have hp3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
                have hp_ge1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
                have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < p))
                exact div_nonneg (Real.log_nonneg hp_ge1) hp1_pos.le
            _ ≤ Real.log (n : ℝ) + Cm := by
                have := hCm (n : ℝ) (by exact_mod_cast (by omega : 3 ≤ n))
                rwa [Nat.floor_natCast] at this
        have hH_inv : 1 / ((H : ℝ) + 1) ≤ 2 / (Real.log (n : ℝ)) ^ (R + 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
        have h_log_le : (Real.log (n : ℝ) + Cm) / (Real.log (n : ℝ)) ^ (R + 2) ≤ (1 + Cm) / 2 := by
          have hR1 : 1 ≤ R := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hδ0]; linarith)
          have hpow : 2 * Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) := by
            have : 2 ≤ Real.log (n : ℝ) := by linarith
            calc 2 * Real.log (n : ℝ) ≤ Real.log (n : ℝ) * Real.log (n : ℝ) := by nlinarith
              _ = (Real.log (n : ℝ)) ^ 2 := by ring
              _ ≤ (Real.log (n : ℝ)) ^ (R + 2) := pow_le_pow_right₀ (by linarith) (by omega)
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hCm_pos]
        calc (∑ p ∈ U, Real.log (p : ℝ) / (p : ℝ)) * ((h_mod : ℝ) / ((H : ℝ) + 1))
            ≤ (Real.log (n : ℝ) + Cm) * ((h_mod : ℝ) * (2 / (Real.log (n : ℝ)) ^ (R + 2))) := by
              apply mul_le_mul hmert_n _ (by positivity) (by positivity)
              rw [div_eq_mul_one_div (h_mod : ℝ) ((H : ℝ) + 1)]
              exact mul_le_mul_of_nonneg_left hH_inv (by positivity)
          _ = 2 * (h_mod : ℝ) * ((Real.log (n : ℝ) + Cm) / (Real.log (n : ℝ)) ^ (R + 2)) := by ring
          _ ≤ 2 * (h_mod : ℝ) * ((1 + Cm) / 2) := mul_le_mul_of_nonneg_left h_log_le (by positivity)
          _ = (h_mod : ℝ) * (1 + Cm) := by ring
      have h_nz : ∑ m ∈ nzH, (b_mod m * ∑ k ∈ Finset.range (K + 1), ∑ p ∈ B_k k,
            ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
              eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ)))).re ≤
          4 * (h_mod : ℝ) * C₂e := by
        calc ∑ m ∈ nzH, _ ≤ ∑ m ∈ nzH, ‖b_mod m * ∑ k ∈ Finset.range (K + 1), ∑ p ∈ B_k k,
                ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
                  eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ)))‖ :=
              Finset.sum_le_sum (fun m _ => Complex.re_le_norm _)
          _ ≤ ∑ m ∈ nzH, ((h_mod : ℝ) / ((H : ℝ) + 1)) *
                (((K : ℝ) + 1) * (C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) := by
              refine Finset.sum_le_sum (fun m hm => ?_)
              rw [norm_mul]
              apply mul_le_mul (hb_mod_norm m) _ (norm_nonneg _) (by positivity)
              calc ‖∑ k ∈ Finset.range (K + 1), _‖
                  ≤ ∑ k ∈ Finset.range (K + 1), ‖∑ p ∈ B_k k, _‖ := norm_sum_le _ _
                _ ≤ ∑ _k ∈ Finset.range (K + 1), (C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) :=
                    Finset.sum_le_sum (fun k _ => h_B_exp k m (Finset.mem_filter.mp hm).2
                      (abs_le.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1)))
                _ = ((K : ℝ) + 1) * (C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
                    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ = (nzH.card : ℝ) * ((h_mod : ℝ) / ((H : ℝ) + 1)) *
                (((K : ℝ) + 1) * (C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) := by
              simp [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ (2 * (h_mod : ℝ)) * ((2 * Real.log (n : ℝ)) * (C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) := by
              apply mul_le_mul _ _ (by positivity) (by positivity)
              · have hcard : nzH.card ≤ 2 * H := by
                  have hsub : nzH ⊆ allH := Finset.filter_subset _ _
                  have h0 : (0 : ℤ) ∈ allH := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
                  have hlt : nzH.card < allH.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => by
                    have : (0 : ℤ) ∈ nzH := heq ▸ h0; exact (Finset.mem_filter.mp this).2 rfl⟩)
                  have hcard_all : allH.card = 2 * H + 1 := by dsimp only [allH]; rw [Int.card_Icc]; omega
                  omega
                have hcardR : (nzH.card : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hcard
                calc (nzH.card : ℝ) * ((h_mod : ℝ) / ((H : ℝ) + 1))
                    ≤ (2 * (H : ℝ)) * ((h_mod : ℝ) / ((H : ℝ) + 1)) := by gcongr
                  _ ≤ 2 * (h_mod : ℝ) := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
              · exact mul_le_mul_of_nonneg_right hK_le (by positivity)
          _ ≤ 4 * (h_mod : ℝ) * C₂e := by
              have h_rpow : (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) = 1 / (Real.log (n : ℝ)) ^ (R + 2) := by
                rw [Real.rpow_neg hlogn_pos.le, one_div]; congr 1; norm_cast
              rw [h_rpow]
              have h1 : Real.log (n : ℝ) * (1 / (Real.log (n : ℝ)) ^ (R + 2)) ≤ 1 := by
                rw [mul_one_div, div_le_one (by positivity)]
                have hR1 : 1 ≤ R := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hδ0]; linarith)
                calc Real.log (n : ℝ) = (Real.log (n : ℝ)) ^ 1 := (pow_one _).symm
                  _ ≤ (Real.log (n : ℝ)) ^ (R + 2) := pow_le_pow_right₀ (by linarith) (by omega)
              calc 2 * (h_mod : ℝ) * (2 * Real.log (n : ℝ) * (C₂e * (1 / (Real.log (n : ℝ)) ^ (R + 2))))
                  = 4 * (h_mod : ℝ) * C₂e * (Real.log (n : ℝ) * (1 / (Real.log (n : ℝ)) ^ (R + 2))) := by ring
                _ ≤ 4 * (h_mod : ℝ) * C₂e * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
                _ = 4 * (h_mod : ℝ) * C₂e := mul_one _
      linarith
    have h_main : ‖∑ k ∈ Finset.range (K + 1), ∑ p ∈ B_k k,
          ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) * Psi_mod ((n : ℝ) / (p : ℝ))‖ ≤ 4 * C₂e := by
      have h_k : ∀ k ∈ Finset.range (K + 1),
          ‖∑ p ∈ B_k k, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) * Psi_mod ((n : ℝ) / (p : ℝ))‖ ≤
          Real.log (n : ℝ) * (C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
        intro k _
        have h_eq : ∑ p ∈ B_k k, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) * Psi_mod ((n : ℝ) / (p : ℝ)) =
            ∑ m ∈ nzH, c_mod m * ∑ p ∈ B_k k, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
              eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ))) := by
          have h_inner : ∀ p ∈ B_k k,
              ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) * Psi_mod ((n : ℝ) / (p : ℝ)) =
              ∑ m ∈ nzH, c_mod m * (((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
                eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ)))) := by
            intro p _
            dsimp only [Psi_mod]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun m _ => ?_)
            have : (m : ℝ) * ((n : ℝ) / (p : ℝ)) / (h_mod : ℝ) = (m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ)) := by ring
            rw [this]; ring
          calc ∑ p ∈ B_k k, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) * Psi_mod ((n : ℝ) / (p : ℝ))
              = ∑ p ∈ B_k k, ∑ m ∈ nzH, c_mod m * (((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
                  eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ)))) := Finset.sum_congr rfl h_inner
            _ = ∑ m ∈ nzH, ∑ p ∈ B_k k, c_mod m * (((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
                  eExp ((m : ℝ) * (n : ℝ) / ((h_mod : ℝ) * (p : ℝ)))) := Finset.sum_comm
            _ = _ := by
                refine Finset.sum_congr rfl (fun m _ => ?_)
                rw [Finset.mul_sum]
        rw [h_eq]
        calc ‖∑ m ∈ nzH, _‖ ≤ ∑ m ∈ nzH, ‖c_mod m * ∑ p ∈ B_k k, _‖ := norm_sum_le _ _
          _ ≤ ∑ m ∈ nzH, ‖c_mod m‖ * (C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by
              refine Finset.sum_le_sum (fun m hm => ?_)
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (h_B_exp k m (Finset.mem_filter.mp hm).2
                (abs_le.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1))) (norm_nonneg _)
          _ = (∑ m ∈ nzH, ‖c_mod m‖) * (C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) := by rw [← Finset.sum_mul]
          _ ≤ Real.log (n : ℝ) * (C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) :=
              mul_le_mul_of_nonneg_right (le_trans h_L1 hlogH_le) (by positivity)
      have h_rpow : (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)) = 1 / (Real.log (n : ℝ)) ^ (R + 2) := by
        rw [Real.rpow_neg hlogn_pos.le, one_div]; congr 1; norm_cast
      calc ‖∑ k ∈ Finset.range (K + 1), _‖
          ≤ ∑ k ∈ Finset.range (K + 1), ‖∑ p ∈ B_k k, _‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range (K + 1), (Real.log (n : ℝ) * (C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) :=
            Finset.sum_le_sum h_k
        _ = ((K : ℝ) + 1) * (Real.log (n : ℝ) * (C₂e * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2)))) := by
            simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ (2 * Real.log (n : ℝ)) * (Real.log (n : ℝ) * (C₂e * (1 / (Real.log (n : ℝ)) ^ (R + 2)))) := by
            rw [h_rpow]; exact mul_le_mul hK_le le_rfl (by positivity) (by positivity)
        _ ≤ 4 * C₂e := by
            have h1 : (Real.log (n : ℝ)) ^ 2 / (Real.log (n : ℝ)) ^ (R + 2) ≤ 1 := by
              rw [div_le_one (by positivity)]
              have hR1 : 1 ≤ R := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hδ0]; linarith)
              exact pow_le_pow_right₀ (by linarith) (by omega)
            calc 2 * Real.log (n : ℝ) * (Real.log (n : ℝ) * (C₂e * (1 / (Real.log (n : ℝ)) ^ (R + 2))))
                = 2 * C₂e * ((Real.log (n : ℝ)) ^ 2 / (Real.log (n : ℝ)) ^ (R + 2)) := by ring
              _ ≤ 2 * C₂e * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
              _ ≤ 4 * C₂e := by linarith
    exact le_trans (norm_add_le _ _) (add_le_add h_err h_main)
  calc ‖∑ p ∈ U, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) *
        eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖
      = ‖((∑ p ∈ U, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) *
            eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) -
          (n : ℝ) * (∑ p ∈ U, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
            eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) / (h_mod : ℝ)))) +
          (n : ℝ) * (∑ p ∈ U, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
            eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) / (h_mod : ℝ)))‖ := by congr 1; ring
    _ ≤ ‖(∑ p ∈ U, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) *
            eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) -
          (n : ℝ) * (∑ p ∈ U, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
            eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) / (h_mod : ℝ)))‖ +
        ‖((n : ℝ) : ℂ) * (∑ p ∈ U, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
            eExp ((z : ℝ) * (Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) / (h_mod : ℝ)))‖ := norm_add_le _ _
    _ ≤ Cθ * (n : ℝ) + (n : ℝ) * ((h_mod : ℝ) * (1 + Cm) + 4 * (h_mod : ℝ) * C₂e + 4 * C₂e) := by
        refine add_le_add h_frac_err ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn_pos.le]
        exact mul_le_mul_of_nonneg_left h_U_bd hn_pos.le
    _ ≤ M_clean * (n : ℝ) := by
        dsimp only [M_clean]
        nlinarith [hn_pos]

/-- **Theorem 2.5(iii) (Multi-Modulus Power-Band Equidistribution, eq. 2.18)**:
For every integer modulus `h_mod ≥ 2`, every residue class `c mod h_mod`, and every exponent band
`0 ≤ a < b ≤ 1`,
`∑_{n^a < p ≤ n^b, v_p(n!) ≡ c [MOD h_mod]} v_p(n!) log p = ((b - a) / h_mod + o(1)) n log n`. -/
theorem multi_modulus_power_band_equidistribution (h_mod c : ℕ) (hh_mod : 2 ≤ h_mod)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (fun n : ℕ =>
      (∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
        p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
        padicValNat p (Nat.factorial n) ≡ c [MOD h_mod]),
        (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) -
      ((b - a) / (h_mod : ℝ)) * ((n : ℝ) * Real.log (n : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  have hh_pos : (0 : ℝ) < (h_mod : ℝ) := by exact_mod_cast (by omega : 0 < h_mod)
  have hh_ge1 : 1 ≤ h_mod := by omega
  have h_band_tot := band_total_weight_isBigO a b ha hab hb
  have h_char_z : ∀ (z : ℕ) (hz1 : 1 ≤ z) (hz2 : z < h_mod),
      (fun n : ℕ => ∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b),
        ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)))
        =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
    intro z hz1 hz2
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    let δ : ℝ := min (1 / 3 : ℝ) (ε / 4)
    have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
    have hδ1 : δ ≤ 1 / 3 := min_le_left _ _
    have hδ_lt : 2 * δ < ε := by
      have : δ ≤ ε / 4 := min_le_right _ _
      linarith
    have h_pref_δ := prefix_weight_isBigO δ hδ0.le (le_trans hδ1 (by norm_num))
    have h_tail_δ := band_total_weight_isBigO (1 - δ) 1 (by linarith) (by linarith) le_rfl
    have h_small := small_prime_mod_band_isBigO h_mod z hh_mod hz1 hz2 δ a b hδ0 hδ1
    have h_upper := upper_band_mod_isBigO h_mod z hh_mod hz1 hz2 δ a b hδ0 hδ1
    obtain ⟨M₁, hM₁⟩ := h_pref_δ.bound
    obtain ⟨M₂, hM₂⟩ := h_tail_δ.bound
    obtain ⟨M₃, hM₃⟩ := h_small.bound
    obtain ⟨M₄, hM₄⟩ := h_upper.bound
    have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h_ev_log : ∀ᶠ n : ℕ in atTop,
        Real.log 2 + M₁ + M₂ + M₃ + M₄ + 1 ≤ (ε - 2 * δ) * Real.log (n : ℝ) := by
      have h_tend : Tendsto (fun n : ℕ => (ε - 2 * δ) * Real.log (n : ℝ)) atTop atTop :=
        hlog_inf.const_mul_atTop (by linarith)
      exact h_tend.eventually (eventually_ge_atTop _)
    have h_sqrt_le : ∀ᶠ n : ℕ in atTop, 2 * (Nat.sqrt n : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) := by
      have ht := log_pow_div_rpow_tendsto_zero 1 (by norm_num : (0 : ℝ) < 1 / 2)
      filter_upwards [Filter.eventually_ge_atTop 4,
        (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le)] with n hn hsm
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have h1 := (div_le_iff₀ (by positivity)).mp hsm
      rw [pow_one, ← Real.sqrt_eq_rpow] at h1
      have h2 : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
        rw [Real.le_sqrt (by positivity) (by positivity)]; exact_mod_cast Nat.sqrt_le' n
      calc 2 * (Nat.sqrt n : ℝ) * Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num))
              (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
        _ ≤ 2 * Real.sqrt (n : ℝ) * ((1 / 2 : ℝ) * Real.sqrt (n : ℝ)) := by
            apply mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by ring
        _ = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
    filter_upwards [Filter.eventually_ge_atTop 16, hM₁, hM₂, hM₃, hM₄,
      hlog_inf.eventually (eventually_ge_atTop 2), h_ev_log, h_sqrt_le] with
      n hn h1 h2 h3 h4 hln2 hev_log hsq_log
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
    have h_nlogn_nn : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by positivity
    rw [Real.norm_of_nonneg h_nlogn_nn]
    let S : Finset ℕ := (Finset.Icc 2 n).filter (fun p : ℕ =>
      p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b)
    let S_low : Finset ℕ := S.filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) ^ δ)
    let S_mid : Finset ℕ := S.filter (fun p : ℕ => (n : ℝ) ^ δ < (p : ℝ) ∧ p ≤ Nat.sqrt n)
    let S_up : Finset ℕ := S.filter (fun p : ℕ => Nat.sqrt n < p ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 - δ))
    let S_hi : Finset ℕ := S.filter (fun p : ℕ => Nat.sqrt n < p ∧ (n : ℝ) ^ (1 - δ) < (p : ℝ))
    have hS_part : S = (((S_low ∪ S_mid : Finset ℕ) ∪ S_up : Finset ℕ) ∪ S_hi : Finset ℕ) := by
      ext p
      simp only [Finset.mem_union, S_low, S_mid, S_up, S_hi, Finset.mem_filter]
      constructor
      · intro hp
        by_cases hle_d : (p : ℝ) ≤ (n : ℝ) ^ δ
        · left; left; left; exact ⟨hp, hle_d⟩
        · by_cases hle_sq : p ≤ Nat.sqrt n
          · left; left; right; exact ⟨hp, lt_of_not_ge hle_d, hle_sq⟩
          · by_cases hle_1d : (p : ℝ) ≤ (n : ℝ) ^ (1 - δ)
            · left; right; exact ⟨hp, by omega, hle_1d⟩
            · right; exact ⟨hp, by omega, lt_of_not_ge hle_1d⟩
      · rintro (((⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩) | ⟨hp, _⟩) <;> exact hp
    have hd1 : Disjoint S_low S_mid := by
      rw [Finset.disjoint_left]; intro p h1 h2
      linarith [(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2.1]
    have hd2 : Disjoint (S_low ∪ S_mid) S_up := by
      rw [Finset.disjoint_left]; intro p h1 h2
      have hgt : Nat.sqrt n < p := (Finset.mem_filter.mp h2).2.1
      rcases Finset.mem_union.mp h1 with h1 | h1
      · have hle : (p : ℝ) ≤ (n : ℝ) ^ δ := (Finset.mem_filter.mp h1).2
        have h_nd_sqrt : (n : ℝ) ^ δ ≤ (Nat.sqrt n : ℝ) := by
          have h_n13 : (n : ℝ) ^ δ ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
          have h_rt : (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (n : ℝ) := (Real.sqrt_eq_rpow (n : ℝ)).symm
          have h_lt := Nat.lt_succ_sqrt' n
          have h_sq_rt : Real.sqrt (n : ℝ) < (Nat.sqrt n : ℝ) + 1 := by
            rw [Real.sqrt_lt' (by positivity)]; exact_mod_cast h_lt
          have : (p : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by linarith
          have hp_lt : p ≤ Nat.sqrt n + 1 := by exact_mod_cast this
          have h_n13' : (n : ℝ) ^ δ ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) hδ1
          have h_cube : (n : ℝ) ^ (1 / 3 : ℝ) < (Nat.sqrt n : ℝ) := by
            have h16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            have h_sq4 : 4 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
            have h_lt_sq : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
              exact_mod_cast (by push_cast; exact Nat.lt_succ_sqrt' n : (n : ℝ) < ((Nat.sqrt n + 1 : ℕ) : ℝ) ^ 2)
            have h_le3 : ((Nat.sqrt n : ℝ) + 1) ^ 2 ≤ (Nat.sqrt n : ℝ) ^ 3 := by
              have h4 : (4 : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast h_sq4
              nlinarith
            have h_n_lt : (n : ℝ) < (Nat.sqrt n : ℝ) ^ 3 := lt_of_lt_of_le h_lt_sq h_le3
            have := Real.rpow_lt_rpow hn_pos.le h_n_lt (by positivity : (0 : ℝ) < 1 / 3)
            rwa [← Real.rpow_natCast (Nat.sqrt n : ℝ) 3, ← Real.rpow_mul (by positivity),
              show (3 : ℕ) * (1 / 3 : ℝ) = 1 from by norm_num, Real.rpow_one] at this
          linarith
        have : (p : ℝ) ≤ (Nat.sqrt n : ℝ) := le_trans hle h_nd_sqrt
        have : p ≤ Nat.sqrt n := by exact_mod_cast this
        omega
      · exact absurd (Finset.mem_filter.mp h1).2.2 (by omega)
    have hd3 : Disjoint (S_low ∪ S_mid ∪ S_up) S_hi := by
      rw [Finset.disjoint_left]; intro p h1 h2
      have h2' := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with (h1 | h1) | h1
      · have hle : (p : ℝ) ≤ (n : ℝ) ^ δ := (Finset.mem_filter.mp h1).2
        have : (n : ℝ) ^ δ ≤ (n : ℝ) ^ (1 - δ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
        linarith
      · have := (Finset.mem_filter.mp h1).2.2; omega
      · linarith [(Finset.mem_filter.mp h1).2.2, h2'.2]
    have h_sum_split : ∑ p ∈ S, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) =
        (∑ p ∈ S_low, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) + (∑ p ∈ S_mid, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) + (∑ p ∈ S_up, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) + (∑ p ∈ S_hi, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) := by
      rw [hS_part, Finset.sum_union hd3, Finset.sum_union hd2, Finset.sum_union hd1]
    -- Bound S_low
    have hS_low_bd : ‖∑ p ∈ S_low, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ ≤
        δ * ((n : ℝ) * Real.log (n : ℝ)) + M₁ * (n : ℝ) := by
      have hsub : S_low ⊆ (Finset.Icc 2 n).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ (n : ℝ) ^ δ) := fun p hp =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1,
          (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1, (Finset.mem_filter.mp hp).2⟩
      calc ‖∑ p ∈ S_low, _‖
          ≤ ∑ p ∈ S_low, ‖((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
              eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ := norm_sum_le _ _
        _ = ∑ p ∈ S_low, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
            refine Finset.sum_congr rfl (fun p hp => ?_)
            have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
            rw [norm_mul, norm_mul, norm_eExp, mul_one, Complex.norm_real, Complex.norm_real,
              Real.norm_of_nonneg (Nat.cast_nonneg _),
              Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p)))]
        _ ≤ ∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ (n : ℝ) ^ δ),
              (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_)
            have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
            exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p)))
        _ ≤ δ * ((n : ℝ) * Real.log (n : ℝ)) + M₁ * (n : ℝ) := by
            rw [Real.norm_eq_abs, Real.norm_of_nonneg hn_pos.le] at h1
            linarith [le_abs_self ((∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ (n : ℝ) ^ δ),
              (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) - δ * ((n : ℝ) * Real.log (n : ℝ)))]
    -- Bound S_hi
    have hS_hi_bd : ‖∑ p ∈ S_hi, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ ≤
        δ * ((n : ℝ) * Real.log (n : ℝ)) + M₂ * (n : ℝ) := by
      have hsub : S_hi ⊆ (Finset.Icc 2 n).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ (1 - δ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 : ℝ)) := by
        intro p hp
        have hpS := (Finset.mem_filter.mp hp).1
        have hpn : p ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpS).1).2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpS).1, (Finset.mem_filter.mp hpS).2.1,
          (Finset.mem_filter.mp hp).2.2, by rw [Real.rpow_one]; exact_mod_cast hpn⟩
      calc ‖∑ p ∈ S_hi, _‖
          ≤ ∑ p ∈ S_hi, ‖((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
              eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ := norm_sum_le _ _
        _ = ∑ p ∈ S_hi, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
            refine Finset.sum_congr rfl (fun p hp => ?_)
            have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
            rw [norm_mul, norm_mul, norm_eExp, mul_one, Complex.norm_real, Complex.norm_real,
              Real.norm_of_nonneg (Nat.cast_nonneg _),
              Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p)))]
        _ ≤ ∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
              p.Prime ∧ (n : ℝ) ^ (1 - δ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 : ℝ)),
              (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_)
            have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
            exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p)))
        _ ≤ δ * ((n : ℝ) * Real.log (n : ℝ)) + M₂ * (n : ℝ) := by
            rw [Real.norm_eq_abs, Real.norm_of_nonneg hn_pos.le] at h2
            have h1d : (1 : ℝ) - (1 - δ) = δ := by ring
            rw [h1d] at h2
            linarith [le_abs_self ((∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
              p.Prime ∧ (n : ℝ) ^ (1 - δ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 : ℝ)),
              (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) - δ * ((n : ℝ) * Real.log (n : ℝ)))]
    -- Bound S_mid using Legendre's identity v_p(n!) = (n - s_p(n)) / (p - 1) and small_prime_mod_band_isBigO
    have hS_mid_bd : ‖∑ p ∈ S_mid, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ ≤
        (Real.log 2 + 1 + M₃) * (n : ℝ) := by
      let S_mid2 := S_mid.filter (· = 2)
      let S_mid3 := S_mid.filter (3 ≤ ·)
      have hSm_eq : S_mid = S_mid2 ∪ S_mid3 := by
        ext p; simp only [S_mid2, S_mid3, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hp
          have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp.1).1).1
          by_cases h2 : p = 2; left; exact ⟨hp, h2⟩; right; exact ⟨hp, by omega⟩
        · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
      have hdm : Disjoint S_mid2 S_mid3 := by
        rw [Finset.disjoint_left]; intro p h1 h2
        rw [(Finset.mem_filter.mp h1).2] at h2
        have := (Finset.mem_filter.mp h2).2; omega
      have h_2_bd : ‖∑ p ∈ S_mid2, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
            eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ ≤ Real.log 2 * (n : ℝ) := by
        by_cases h2_mem : 2 ∈ S_mid
        · have hS2 : S_mid2 = {2} := by
            ext p; simp only [S_mid2, Finset.mem_filter, Finset.mem_singleton]
            exact ⟨fun h => h.2, fun h => h ▸ ⟨h2_mem, rfl⟩⟩
          rw [hS2, Finset.sum_singleton, norm_mul, show ‖eExp _‖ = 1 from by
              exact norm_eExp _, mul_one,
            Nat.cast_ofNat, Complex.norm_real]
          have hv2 : padicValNat 2 (Nat.factorial n) ≤ n := by
            haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
            have hleg := sub_one_mul_padicValNat_factorial (p := 2) n
            simp only [Nat.reduceSub, one_mul] at hleg
            omega
          have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
          rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog2_pos.le)]
          have : (padicValNat 2 (Nat.factorial n) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hv2
          nlinarith
        · have hS2 : S_mid2 = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]; intro p hp
            exact h2_mem ((Finset.mem_filter.mp hp).2 ▸ (Finset.mem_filter.mp hp).1)
          rw [hS2, Finset.sum_empty, norm_zero]
          have : 0 < Real.log 2 := Real.log_pos (by norm_num)
          positivity
      have hS_mid3_eq : S_mid3 = (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b) := by
        ext p; simp only [S_mid3, S_mid, S, Finset.mem_filter, Finset.mem_Icc]; omega
      have h_3_bd : ‖∑ p ∈ S_mid3, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
            eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ ≤ (1 + M₃) * (n : ℝ) := by
        have h_diff : ∑ p ∈ S_mid3, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
              eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) =
            ((n : ℝ) : ℂ) * (∑ p ∈ S_mid3,
              eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
                ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)) -
            ∑ p ∈ S_mid3, ((((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ)) : ℂ) *
              eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun p hp => ?_)
          have hp_pr : p.Prime := by
            have := hp; rw [hS_mid3_eq] at this; exact (Finset.mem_filter.mp this).2.1
          have hp3 : 3 ≤ p := by
            have := hp; rw [hS_mid3_eq] at this; exact (Finset.mem_Icc.mp (Finset.mem_filter.mp this).1).1
          have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : p ≠ 1))
          have hleg : (p - 1) * padicValNat p (Nat.factorial n) = n - (Nat.digits p n).sum := by
            haveI : Fact p.Prime := ⟨hp_pr⟩; exact sub_one_mul_padicValNat_factorial n
          have hsum_le : (Nat.digits p n).sum ≤ n := by
            calc (Nat.digits p n).sum ≤ Nat.ofDigits p (Nat.digits p n) := Nat.sum_le_ofDigits _ hp_pr.pos
              _ = n := Nat.ofDigits_digits p n
          have hlegR : ((p : ℝ) - 1) * (padicValNat p (Nat.factorial n) : ℝ) =
              (n : ℝ) - ((Nat.digits p n).sum : ℝ) := by
            have h1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring
            have h2 : (p - 1) * padicValNat p (Nat.factorial n) + (Nat.digits p n).sum = n := by omega
            have h3 : ((p - 1 : ℕ) : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) + ((Nat.digits p n).sum : ℝ) = (n : ℝ) := by
              exact_mod_cast h2
            linarith
          have hvpR : (padicValNat p (Nat.factorial n) : ℝ) =
              (n : ℝ) / ((p : ℝ) - 1) - ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) := by
            field_simp [hp1]; linarith
          rw [hvpR]; push_cast; ring
        rw [h_diff]
        have h_n_sum : ‖((n : ℝ) : ℂ) * ∑ p ∈ S_mid3,
              eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
                ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)‖ ≤ M₃ * (n : ℝ) := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn_pos.le]
          rw [Real.norm_of_nonneg (by positivity : 0 ≤ 1 / Real.log (n : ℝ))] at h3
          have h3' : ‖∑ p ∈ S_mid3, eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
              ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)‖ ≤ M₃ := by
            have h_le1 : 1 / Real.log (n : ℝ) ≤ 1 := div_le_one_of_le₀ (by linarith) hlogn_pos.le
            have hM3_nn : 0 ≤ M₃ := by
              have : 0 ≤ ‖∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
                p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b),
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) *
                  ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ)‖ := norm_nonneg _
              exact nonneg_of_mul_nonneg_left (le_trans this h3) (by positivity)
            calc _ ≤ M₃ * (1 / Real.log (n : ℝ)) := by rw [hS_mid3_eq]; exact h3
              _ ≤ M₃ * 1 := mul_le_mul_of_nonneg_left h_le1 hM3_nn
              _ = M₃ := mul_one _
          nlinarith
        have h_dig : ‖∑ p ∈ S_mid3, ((((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ)) : ℂ) *
              eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ ≤ (n : ℝ) := by
          have h_each : ∀ p ∈ S_mid3, ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ) ≤
              2 * Real.log (n : ℝ) := by
            intro p hp
            rw [hS_mid3_eq] at hp
            have hp_pr := (Finset.mem_filter.mp hp).2.1
            have hp3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
            have hpn : p ≤ n := le_trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2 (Nat.sqrt_le_self n)
            have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < p))
            have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
            have hdig_len : (Nat.digits p n).length ≤ Nat.floor (Real.log (n : ℝ) / Real.log (p : ℝ)) + 1 := by
              have h1 : p ^ ((Nat.digits p n).length - 1) ≤ n := by
                rcases eq_or_ne (Nat.digits p n).length 0 with hl0 | hlne
                · simp [hl0]; omega
                · have h_le := Nat.base_pow_length_digits_le p n hp_pr.one_lt (by omega)
                  have h_eq : (Nat.digits p n).length = ((Nat.digits p n).length - 1) + 1 := by omega
                  rw [h_eq, pow_succ'] at h_le
                  exact Nat.le_of_mul_le_mul_left h_le hp_pr.pos
              have h2 : (((Nat.digits p n).length - 1 : ℕ) : ℝ) * Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
                have : ((p ^ ((Nat.digits p n).length - 1) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
                have hlog := Real.log_le_log (by positivity) this
                rwa [Nat.cast_pow, Real.log_pow] at hlog
              have h3 : (((Nat.digits p n).length - 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) / Real.log (p : ℝ) :=
                (le_div_iff₀ hlogp_pos).mpr h2
              have h4 : (Nat.digits p n).length - 1 ≤ Nat.floor (Real.log (n : ℝ) / Real.log (p : ℝ)) :=
                (Nat.le_floor_iff (div_nonneg hlogn_pos.le hlogp_pos.le)).mpr h3
              omega
            have hdig_sum_gen : ∀ L : List ℕ, (∀ d ∈ L, d ≤ p - 1) → L.sum ≤ L.length * (p - 1) := by
              intro L hL
              induction L with
              | nil => simp
              | cons a l ih =>
                simp only [List.sum_cons, List.length_cons]
                have ha := hL a (by simp)
                have hl := ih (fun d hd => hL d (by simp [hd]))
                nlinarith
            have hdig_sum : (Nat.digits p n).sum ≤ (Nat.digits p n).length * (p - 1) :=
              hdig_sum_gen (Nat.digits p n) (fun d hd => Nat.le_sub_one_of_lt (Nat.digits_lt_base hp_pr.one_lt hd))
            have hsum_R : ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) ≤ Real.log (n : ℝ) / Real.log (p : ℝ) + 1 := by
              have h1 : ((Nat.digits p n).sum : ℝ) ≤ ((Nat.digits p n).length : ℝ) * ((p : ℝ) - 1) := by
                have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring
                rw [← this]; exact_mod_cast hdig_sum
              have h2 : ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) ≤ ((Nat.digits p n).length : ℝ) :=
                (div_le_iff₀ hp1_pos).mpr h1
              have h3 : ((Nat.digits p n).length : ℝ) ≤ (Nat.floor (Real.log (n : ℝ) / Real.log (p : ℝ)) : ℝ) + 1 := by
                exact_mod_cast hdig_len
              have h4 : (Nat.floor (Real.log (n : ℝ) / Real.log (p : ℝ)) : ℝ) ≤ Real.log (n : ℝ) / Real.log (p : ℝ) :=
                Nat.floor_le (div_nonneg hlogn_pos.le hlogp_pos.le)
              linarith
            have hlogp_le : Real.log (p : ℝ) ≤ Real.log (n : ℝ) :=
              Real.log_le_log (by positivity) (by exact_mod_cast hpn)
            calc ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ)
                ≤ (Real.log (n : ℝ) / Real.log (p : ℝ) + 1) * Real.log (p : ℝ) :=
                  mul_le_mul_of_nonneg_right hsum_R hlogp_pos.le
              _ = Real.log (n : ℝ) + Real.log (p : ℝ) := by field_simp [hlogp_pos.ne']
              _ ≤ 2 * Real.log (n : ℝ) := by linarith
          have h_card : (S_mid3.card : ℝ) ≤ (Nat.sqrt n : ℝ) := by
            have hsub : S_mid3 ⊆ Finset.Icc 1 (Nat.sqrt n) := fun p hp => by
              rw [hS_mid3_eq] at hp
              exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; omega,
                (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2⟩
            exact_mod_cast le_trans (Finset.card_le_card hsub) (by simp)
          have h_sq_log : 2 * (Nat.sqrt n : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) := hsq_log
          calc ‖∑ p ∈ S_mid3, ((((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ)) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖
              ≤ ∑ p ∈ S_mid3, ‖((((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ)) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ := norm_sum_le _ _
            _ = ∑ p ∈ S_mid3, ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ) := by
                refine Finset.sum_congr rfl (fun p hp => ?_)
                rw [hS_mid3_eq] at hp
                have hp3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
                rw [norm_mul, norm_mul, norm_eExp, mul_one, Complex.norm_real, Complex.norm_real,
                  Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) (sub_pos.mpr (by exact_mod_cast (by omega : 1 < p))).le),
                  Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p)))]
            _ ≤ ∑ _p ∈ S_mid3, 2 * Real.log (n : ℝ) := Finset.sum_le_sum h_each
            _ = (S_mid3.card : ℝ) * (2 * Real.log (n : ℝ)) := by simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (Nat.sqrt n : ℝ) * (2 * Real.log (n : ℝ)) := mul_le_mul_of_nonneg_right h_card (by positivity)
            _ ≤ (n : ℝ) := by linarith
        exact le_trans (norm_sub_le _ _) (by linarith)
      rw [hSm_eq, Finset.sum_union hdm]
      exact le_trans (norm_add_le _ _) (by linarith)
    -- Bound S_up
    have hS_up_bd : ‖∑ p ∈ S_up, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ ≤ M₄ * (n : ℝ) := by
      have h_eq_U : S_up = (Finset.Icc (Nat.sqrt n + 1) n).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 - δ)) := by
        have hsq1 : 1 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
        ext p; simp only [S_up, S, Finset.mem_filter, Finset.mem_Icc]
        constructor <;> intro h <;> rcases h with ⟨⟨h1, h2⟩, h3⟩ <;> refine ⟨⟨by omega, by omega⟩, ?_⟩ <;> tauto
      rw [h_eq_U]
      rwa [Real.norm_of_nonneg hn_pos.le] at h4
    -- Combine all four ranges
    rw [h_sum_split]
    calc ‖(∑ p ∈ S_low, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) + (∑ p ∈ S_mid, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) + (∑ p ∈ S_up, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) + (∑ p ∈ S_hi, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)))‖
        ≤ ‖∑ p ∈ S_low, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ + ‖∑ p ∈ S_mid, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ + ‖∑ p ∈ S_up, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ + ‖∑ p ∈ S_hi, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
          eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ :=
          calc ‖(∑ p ∈ S_low, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) + (∑ p ∈ S_mid, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) + (∑ p ∈ S_up, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) + (∑ p ∈ S_hi, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)))‖
              ≤ ‖(∑ p ∈ S_low, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) + (∑ p ∈ S_mid, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) + (∑ p ∈ S_up, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)))‖ + ‖∑ p ∈ S_hi, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ := norm_add_le _ _
            _ ≤ (‖(∑ p ∈ S_low, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) + (∑ p ∈ S_mid, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)))‖ + ‖∑ p ∈ S_up, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖) + ‖∑ p ∈ S_hi, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ := by gcongr; exact norm_add_le _ _
            _ ≤ (‖∑ p ∈ S_low, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ + ‖∑ p ∈ S_mid, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ + ‖∑ p ∈ S_up, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖) + ‖∑ p ∈ S_hi, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (δ * ((n : ℝ) * Real.log (n : ℝ)) + M₁ * (n : ℝ)) +
          (Real.log 2 + 1 + M₃) * (n : ℝ) + M₄ * (n : ℝ) +
          (δ * ((n : ℝ) * Real.log (n : ℝ)) + M₂ * (n : ℝ)) := by
          gcongr
      _ = 2 * δ * ((n : ℝ) * Real.log (n : ℝ)) + (Real.log 2 + M₁ + M₂ + M₃ + M₄ + 1) * (n : ℝ) := by ring
      _ ≤ 2 * δ * ((n : ℝ) * Real.log (n : ℝ)) + ((ε - 2 * δ) * Real.log (n : ℝ)) * (n : ℝ) := by
          gcongr
      _ = ε * ((n : ℝ) * Real.log (n : ℝ)) := by ring
  -- Now assemble eq. (2.18) using indicator_mod_eq_sum_eExp
  have h_sum_C : (fun n : ℕ =>
      Complex.ofReal ((∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
          padicValNat p (Nat.factorial n) ≡ c [MOD h_mod]),
          (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) -
        ((b - a) / (h_mod : ℝ)) * ((n : ℝ) * Real.log (n : ℝ))))
      =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
    have h_z0 : (fun n : ℕ => ((1 / (h_mod : ℂ)) *
        ((∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
            p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b),
          ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ)) -
         (((b - a) * ((n : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ))))
        =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
      have h1 : (fun n : ℕ =>
          (∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
              p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b),
            (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) -
          (b - a) * ((n : ℝ) * Real.log (n : ℝ)))
          =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
        have h_n_o : (fun n : ℕ => (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
          rw [Asymptotics.isLittleO_iff]
          intro ε hε
          filter_upwards [Filter.eventually_ge_atTop 1,
            (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1 / ε))] with n hn hln
          have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by positivity
          have hln_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
          rw [Real.norm_of_nonneg hn_nn, Real.norm_of_nonneg (mul_nonneg hn_nn hln_nn)]
          dsimp only [Function.comp_apply] at hln
          calc (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm
            _ = (n : ℝ) * (ε * (1 / ε)) := by field_simp [hε.ne']
            _ ≤ (n : ℝ) * (ε * Real.log (n : ℝ)) := by gcongr
            _ = ε * ((n : ℝ) * Real.log (n : ℝ)) := by ring
        exact h_band_tot.trans_isLittleO h_n_o
      have h2 : (fun n : ℕ => Complex.ofReal ((∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
              p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b),
            (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) -
          (b - a) * ((n : ℝ) * Real.log (n : ℝ))))
          =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
        rw [Asymptotics.isLittleO_iff] at h1 ⊢
        intro ε hε
        filter_upwards [h1 hε] with n hn
        rw [Complex.norm_real]
        exact hn
      exact (Asymptotics.IsLittleO.const_mul_left h2 (1 / (h_mod : ℂ))).congr'
        (Eventually.of_forall (fun n => by push_cast; ring)) EventuallyEq.rfl
    have h_znz : (fun n : ℕ => ∑ z ∈ (Finset.range h_mod).filter (· ≠ 0),
        (1 / (h_mod : ℂ)) * eExp (-((z : ℝ) * (c : ℝ) / (h_mod : ℝ))) *
          ∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
            p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b),
            ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
              eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)))
        =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
      have h_sum := Asymptotics.IsLittleO.sum (s := (Finset.range h_mod).filter (· ≠ 0))
        (f := fun z n => (1 / (h_mod : ℂ)) * eExp (-((z : ℝ) * (c : ℝ) / (h_mod : ℝ))) *
          ∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
            p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b),
            ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
              eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)))
        (fun z hz => by
          have hz_mem := Finset.mem_filter.mp hz
          have hz1 : 1 ≤ z := by have := Finset.mem_range.mp hz_mem.1; have := hz_mem.2; omega
          have hz2 : z < h_mod := Finset.mem_range.mp hz_mem.1
          exact Asymptotics.IsLittleO.const_mul_left (h_char_z z hz1 hz2) _)
      simpa using h_sum
    refine (h_z0.add h_znz).congr' ?_ EventuallyEq.rfl
    filter_upwards with n
    let S := (Finset.Icc 2 n).filter (fun p : ℕ =>
      p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b)
    have h_lhs : (∑ p ∈ S.filter (fun p => padicValNat p (Nat.factorial n) ≡ c [MOD h_mod]),
          ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ)) =
        ∑ p ∈ S, (if padicValNat p (Nat.factorial n) ≡ c [MOD h_mod] then (1 : ℂ) else 0) *
          ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun p _ => by split_ifs <;> ring)
    have h_S_filt : (Finset.Icc 2 n).filter (fun p : ℕ =>
        p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b ∧
        padicValNat p (Nat.factorial n) ≡ c [MOD h_mod]) =
        S.filter (fun p => padicValNat p (Nat.factorial n) ≡ c [MOD h_mod]) := by
      ext p; simp only [S, Finset.mem_filter]; tauto
    have h_ind : ∑ p ∈ S, (if padicValNat p (Nat.factorial n) ≡ c [MOD h_mod] then (1 : ℂ) else 0) *
          ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) =
        (1 / (h_mod : ℂ)) * (∑ p ∈ S, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ)) +
        ∑ z ∈ (Finset.range h_mod).filter (· ≠ 0),
          (1 / (h_mod : ℂ)) * eExp (-((z : ℝ) * (c : ℝ) / (h_mod : ℝ))) *
            ∑ p ∈ S, ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
              eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ)) := by
      have h_each : ∀ p ∈ S,
          (if padicValNat p (Nat.factorial n) ≡ c [MOD h_mod] then (1 : ℂ) else 0) *
            ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) =
          (1 / (h_mod : ℂ)) * ((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) +
          ∑ z ∈ (Finset.range h_mod).filter (· ≠ 0),
            (1 / (h_mod : ℂ)) * eExp (-((z : ℝ) * (c : ℝ) / (h_mod : ℝ))) *
              (((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ))) := by
        intro p _
        rw [indicator_mod_eq_sum_eExp (padicValNat p (Nat.factorial n)) c h_mod hh_ge1]
        have h_rng : Finset.range h_mod = insert 0 ((Finset.range h_mod).filter (· ≠ 0)) := by
          ext z; simp only [Finset.mem_insert, Finset.mem_range, Finset.mem_filter]; omega
        have h0_not : (0 : ℕ) ∉ (Finset.range h_mod).filter (· ≠ 0) := by simp
        rw [h_rng, Finset.sum_insert h0_not, Nat.cast_zero, zero_mul, zero_div,
          show eExp 0 = 1 from by unfold eExp; simp, mul_add, mul_one, add_mul, Finset.mul_sum, Finset.sum_mul]
        congr 1
        · ring
        · refine Finset.sum_congr rfl (fun z _ => ?_)
          have harg : (z : ℝ) * ((padicValNat p (Nat.factorial n) : ℝ) - (c : ℝ)) / (h_mod : ℝ) =
              -((z : ℝ) * (c : ℝ) / (h_mod : ℝ)) +
              (z : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) / (h_mod : ℝ) := by ring
          rw [harg, ← eExp_add]; ring
      rw [Finset.sum_congr rfl h_each, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [← Finset.mul_sum]
    rw [h_S_filt]
    push_cast
    rw [h_lhs, h_ind]
    push_cast
    ring
  rw [Asymptotics.isLittleO_iff] at h_sum_C ⊢
  intro ε hε
  filter_upwards [h_sum_C hε] with n hn
  rw [Complex.norm_real] at hn
  exact hn

end GrasGreenbergBrocard
