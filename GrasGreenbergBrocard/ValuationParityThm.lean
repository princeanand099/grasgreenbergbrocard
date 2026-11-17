import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.ValuationParityDigits
import GrasGreenbergBrocard.ValuationParityVaaler
import GrasGreenbergBrocard.ExpSumBounds
import GrasGreenbergBrocard.ValuationParityThmHelpers
import GrasGreenbergBrocard.ValuationParityThmPart1
import GrasGreenbergBrocard.ValuationParityThmCollar
import GrasGreenbergBrocard.ValuationParityThmInterCollar

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard

/-- **Theorem 2.5(ii), eq. (2.16) (Collar-Decomposed Parity Band Bound)**:
For every `δ ∈ (0, 1/3]`,
`∑_{n^δ < p ≤ √n} (-1)^{v_p(n!) - 1} log p / (p - 1) = O_δ(1 / log n)`. -/
theorem small_prime_parity_band_bound (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    (fun n : ℕ => ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ)),
      ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1)))
      =O[atTop] (fun n : ℕ => 1 / Real.log (n : ℝ)) := by
  set R := Nat.floor (1 / δ)
  set A_R := 6 * R + 30
  have hR3 : 3 ≤ R := by
    rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hδ0]; linarith
  have h_col_sum : ∀ r ∈ Finset.Icc 2 R,
      (fun n : ℕ => ∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ∈ collar n r A_R)),
        ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1)))
        =O[atTop] (fun n : ℕ => 1 / Real.log (n : ℝ)) := fun r hr =>
    collar_band_isBigO δ hδ0 hδ1 r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2
  have h_int_sum : ∀ r ∈ Finset.Icc 2 R,
      (fun n : ℕ => ∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ∈ interCollar n r A_R)),
        ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1)))
        =O[atTop] (fun n : ℕ => 1 / Real.log (n : ℝ)) := fun r hr =>
    interCollar_band_isBigO δ hδ0 hδ1 r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2
  have h_fin_sum : (fun n : ℕ => ∑ r ∈ Finset.Icc 2 R,
      ((∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ∈ collar n r A_R)),
        ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1))) +
       (∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ∈ interCollar n r A_R)),
        ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1)))))
      =O[atTop] (fun n : ℕ => 1 / Real.log (n : ℝ)) :=
    Asymptotics.IsBigO.sum (fun r hr => (h_col_sum r hr).add (h_int_sum r hr))
  refine h_fin_sum.congr' ?_ EventuallyEq.rfl
  have h_rpow_all : ∀ᶠ n : ℕ in atTop, ∀ r ∈ Finset.Icc 2 R,
      (Real.log (n : ℝ)) ^ A_R / (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) ≤ 1 := by
    rw [Filter.eventually_all_finset]
    intro r hr
    have ht := log_pow_div_rpow_tendsto_zero A_R (by positivity : (0 : ℝ) < 1 / ((r : ℝ) * ((r : ℝ) + 1)))
    exact (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)
  filter_upwards [(tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2),
    Filter.eventually_ge_atTop 16, h_rpow_all] with n hln hn hrpow_all
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  let S := (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ))
  let B : ℕ → Finset ℕ := fun r =>
    S.filter (fun p : ℕ => (p : ℝ) ∈ collar n r A_R ∪ interCollar n r A_R)
  have hS_eq : S = (Finset.Icc 2 R).biUnion B := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_Icc, B, Finset.mem_filter]
    constructor
    · intro hp
      have hp_le_sq : (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by positivity) (by positivity)]
        exact_mod_cast le_trans (Nat.pow_le_pow_left (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2 2) (Nat.sqrt_le' n)
      have hp_gt_R1 : (n : ℝ) ^ (1 / ((R : ℝ) + 1)) < (p : ℝ) := by
        have h1 : 1 / ((R : ℝ) + 1) < δ := by
          rw [div_lt_iff₀ (by positivity)]
          have := Nat.lt_floor_add_one (1 / δ)
          nlinarith [(div_lt_iff₀ hδ0).mp this]
        calc (n : ℝ) ^ (1 / ((R : ℝ) + 1)) < (n : ℝ) ^ δ :=
              Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < n)) h1
          _ < (p : ℝ) := (Finset.mem_filter.mp hp).2.2
      have hex : ∃ r ∈ Finset.Icc 2 R, (n : ℝ) ^ (1 / ((r : ℝ) + 1)) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 / (r : ℝ)) := by
        have h_nonemp : ((Finset.Icc 2 R).filter (fun r : ℕ => (p : ℝ) ≤ (n : ℝ) ^ (1 / (r : ℝ)))).Nonempty :=
          ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, by norm_num; exact hp_le_sq⟩⟩
        let r := ((Finset.Icc 2 R).filter (fun r : ℕ => (p : ℝ) ≤ (n : ℝ) ^ (1 / (r : ℝ)))).max' h_nonemp
        have hr_mem := Finset.max'_mem _ h_nonemp
        have hr_icc : r ∈ Finset.Icc 2 R := (Finset.mem_filter.mp hr_mem).1
        have hr_le : (p : ℝ) ≤ (n : ℝ) ^ (1 / (r : ℝ)) := (Finset.mem_filter.mp hr_mem).2
        refine ⟨r, hr_icc, ?_, hr_le⟩
        by_cases hrR : r = R
        · subst hrR; exact hp_gt_R1
        · have hr1_icc : r + 1 ∈ Finset.Icc 2 R := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          by_contra hle; push Not at hle
          have hle' := Finset.le_max' _ (r + 1) (Finset.mem_filter.mpr ⟨hr1_icc, by push_cast; exact hle⟩)
          omega
      obtain ⟨r, hr_icc, hlo, hhi⟩ := hex
      refine ⟨r, hr_icc, hp, ?_⟩
      rcases le_or_gt (p : ℝ) ((n : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ))) with h_ic | h_co
      · right; exact ⟨hlo, h_ic⟩
      · left; exact ⟨h_co, hhi⟩
    · rintro ⟨r, _, hp, _⟩; exact hp
  have hdisj_B : (Finset.Icc 2 R : Set ℕ).PairwiseDisjoint B := by
    intro r₁ hr₁ r₂ hr₂ hne
    dsimp only [Function.onFun]; rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2
    have h2 := (Finset.mem_filter.mp hp2).2
    have hrange : ∀ r ∈ Finset.Icc 2 R, (p : ℝ) ∈ collar n r A_R ∪ interCollar n r A_R →
        (n : ℝ) ^ (1 / ((r : ℝ) + 1)) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 / (r : ℝ)) := by
      intro r hr hp_u
      have hr1 : 1 ≤ r := by have := (Finset.mem_Icc.mp hr).1; omega
      have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
      rcases hp_u with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
      · refine ⟨?_, hhi⟩
        have h_gap : (n : ℝ) ^ (1 / ((r : ℝ) + 1)) ≤
            (n : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)) := by
          rw [le_div_iff₀ (by positivity)]
          have hpow_gt : (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)) ≤ (Real.log (n : ℝ)) ^ A_R := by
            rw [← Real.rpow_natCast (Real.log (n : ℝ)) A_R]
            apply Real.rpow_le_rpow_of_exponent_le (by linarith)
            exact div_le_self (by positivity) (by exact_mod_cast hr1)
          have h_n1 : (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) := by
            have := (div_le_iff₀ (by positivity)).mp (hrpow_all r hr)
            linarith
          have h_n2 : (n : ℝ) ^ (1 / ((r : ℝ) + 1)) * (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) =
              (n : ℝ) ^ (1 / (r : ℝ)) := by
            rw [← Real.rpow_add hn_pos]
            congr 1; field_simp [hr_pos.ne', by positivity : (r : ℝ) + 1 ≠ 0]; ring
          nlinarith [Real.rpow_pos_of_pos hn_pos (1 / ((r : ℝ) + 1))]
        exact lt_of_le_of_lt h_gap hlo
      · refine ⟨hlo, le_trans hhi ?_⟩
        exact div_le_self (by positivity) (Real.one_le_rpow (by linarith) (by positivity))
    obtain ⟨h1_lo, h1_hi⟩ := hrange r₁ hr₁ h1
    obtain ⟨h2_lo, h2_hi⟩ := hrange r₂ hr₂ h2
    have h12 : (n : ℝ) ^ (1 / ((r₁ : ℝ) + 1)) < (n : ℝ) ^ (1 / (r₂ : ℝ)) := lt_trans h1_lo h2_hi
    have h21 : (n : ℝ) ^ (1 / ((r₂ : ℝ) + 1)) < (n : ℝ) ^ (1 / (r₁ : ℝ)) := lt_trans h2_lo h1_hi
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have h_lt1 : r₂ < r₁ + 1 := by
      by_contra hle; push Not at hle
      have hexp : 1 / (r₂ : ℝ) ≤ 1 / ((r₁ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hle)
      have hpow := Real.rpow_le_rpow_of_exponent_le hn1.le hexp
      linarith
    have h_lt2 : r₁ < r₂ + 1 := by
      by_contra hle; push Not at hle
      have hexp : 1 / (r₁ : ℝ) ≤ 1 / ((r₂ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hle)
      have hpow := Real.rpow_le_rpow_of_exponent_le hn1.le hexp
      linarith
    omega
  rw [hS_eq, Finset.sum_biUnion hdisj_B]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hB_eq : B r =
      ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ∈ collar n r A_R)) ∪
      ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ∈ interCollar n r A_R)) := by
    ext p
    simp only [B, S, Finset.mem_union, Finset.mem_filter, Set.mem_union]
    tauto
  have hdisj_ci : Disjoint
      ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ∈ collar n r A_R))
      ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ∈ interCollar n r A_R)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2.2.2.1
    have h2 := (Finset.mem_filter.mp hp2).2.2.2.2
    linarith
  rw [hB_eq, Finset.sum_union hdisj_ci, add_comm]

/-- **Theorem 2.5(ii), eq. (2.17), part 1**:
`Σ*_parity(n) = o(log n)`. -/
theorem Sigma_star_parity_isLittleO_log :
    (fun n : ℕ => Sigma_star_parity n) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
  obtain ⟨Cm, hCm_pos, hCm⟩ := mertens_sum_le
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  let δ := min (1 / 3 : ℝ) (ε / 4)
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 3 := min_le_left _ _
  have hδ_eps : δ ≤ ε / 4 := min_le_right _ _
  obtain ⟨M_band, hM_band⟩ := (small_prime_parity_band_bound δ hδ0 hδ1).bound
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 16, hM_band,
    hlog_inf.eventually (eventually_ge_atTop (max (4 * (Cm + Real.log 3) / ε + 1) (Real.sqrt (2 * |M_band| / ε) + 2)))] with
    n hn hband hln
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by
    have : 0 ≤ 4 * (Cm + Real.log 3) / ε := by positivity
    linarith [le_max_left (4 * (Cm + Real.log 3) / ε + 1) (Real.sqrt (2 * |M_band| / ε) + 2)]
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hlogn_pos.le]
  let S := (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime
  let S_lo := S.filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) ^ δ)
  let S_hi := S.filter (fun p : ℕ => (n : ℝ) ^ δ < (p : ℝ))
  have hS_split : S = S_lo ∪ S_hi := by
    ext p; simp only [Finset.mem_union, Finset.mem_filter, S_lo, S_hi]
    constructor
    · intro hp; rcases le_or_gt (p : ℝ) ((n : ℝ) ^ δ) with h | h
      · left; exact ⟨hp, h⟩
      · right; exact ⟨hp, h⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hdisj : Disjoint S_lo S_hi := by
    rw [Finset.disjoint_left]; intro p hp1 hp2
    simp only [Finset.mem_filter, S_lo, S_hi] at hp1 hp2; linarith
  have h_sig_eq : Sigma_star_parity n =
      (∑ p ∈ S_lo, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1))) +
      (∑ p ∈ S_hi, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1))) := by
    unfold Sigma_star_parity
    change ∑ p ∈ S, _ = _
    rw [hS_split, Finset.sum_union hdisj]
  have h_lo_bound : |∑ p ∈ S_lo, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1))| ≤
      (ε / 2) * Real.log (n : ℝ) := by
    calc |∑ p ∈ S_lo, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1))|
        ≤ ∑ p ∈ S_lo, |((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ p ∈ S_lo, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
          have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
          have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (div_nonneg hlogp hp1.le)]
      _ ≤ ∑ p ∈ (Finset.Icc 3 (Nat.floor (max 3 ((n : ℝ) ^ δ)))).filter Nat.Prime,
            Real.log (p : ℝ) / ((p : ℝ) - 1) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p hp _ => by
            have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
            have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
            have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
            exact div_nonneg hlogp hp1.le)
          intro p hp
          simp only [S_lo, S, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨⟨hp.1.1.1, (Nat.le_floor_iff (by positivity)).mpr (le_trans hp.2 (le_max_right _ _))⟩, hp.1.2⟩
      _ ≤ Real.log (max 3 ((n : ℝ) ^ δ)) + Cm := hCm _ (le_max_left _ _)
      _ ≤ (ε / 2) * Real.log (n : ℝ) := by
          have h1 : Real.log (max 3 ((n : ℝ) ^ δ)) ≤ δ * Real.log (n : ℝ) + Real.log 3 := by
            rcases le_or_gt 3 ((n : ℝ) ^ δ) with h | h
            · rw [max_eq_right h, Real.log_rpow hn_pos]
              linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)]
            · rw [max_eq_left h.le]
              linarith [mul_nonneg hδ0.le hlogn_pos.le]
          have hCm_le : Cm + Real.log 3 ≤ (ε / 4) * Real.log (n : ℝ) := by
            have hge : 4 * (Cm + Real.log 3) / ε ≤ Real.log (n : ℝ) := by
              linarith [le_max_left (4 * (Cm + Real.log 3) / ε + 1) (Real.sqrt (2 * |M_band| / ε) + 2)]
            have hmul := (div_le_iff₀ hε).mp hge
            linarith
          linarith [mul_le_mul_of_nonneg_right hδ_eps hlogn_pos.le]
  have h_hi_bound : |∑ p ∈ S_hi, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1))| ≤
      (ε / 2) * Real.log (n : ℝ) := by
    have hS_hi_eq : S_hi = (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ)) := by
      ext p; simp only [S_hi, S, Finset.mem_filter]; tauto
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)] at hband
    rw [hS_hi_eq]
    have hM_le : |M_band| / Real.log (n : ℝ) ≤ (ε / 2) * Real.log (n : ℝ) := by
      rw [div_le_iff₀ hlogn_pos]
      have hsq : Real.sqrt (2 * |M_band| / ε) ≤ Real.log (n : ℝ) := by
        linarith [le_max_right (4 * (Cm + Real.log 3) / ε + 1) (Real.sqrt (2 * |M_band| / ε) + 2)]
      have hsq2 : 2 * |M_band| / ε ≤ (Real.log (n : ℝ)) ^ 2 := by
        calc 2 * |M_band| / ε = (Real.sqrt (2 * |M_band| / ε)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
          _ ≤ (Real.log (n : ℝ)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
      have := (div_le_iff₀ hε).mp hsq2
      nlinarith
    calc |∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ)), _|
        ≤ M_band * (1 / Real.log (n : ℝ)) := hband
      _ ≤ |M_band| / Real.log (n : ℝ) := by
          rw [mul_one_div]; exact div_le_div_of_nonneg_right (le_abs_self _) hlogn_pos.le
      _ ≤ (ε / 2) * Real.log (n : ℝ) := hM_le
  rw [h_sig_eq]
  exact le_trans (abs_add_le _ _) (by linarith)

/-- **Theorem 2.5(ii), eq. (2.17), part 2**:
`Δ_parity(n) = o(n log n)`. -/
theorem Delta_parity_isLittleO_mul_log :
    (fun n : ℕ => Delta_parity n) =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  have h1 : (fun n : ℕ => Delta_parity n - (Real.log 2 - 1 - Sigma_star_parity n) * (n : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := Delta_parity_second_order
  have h1' : (fun n : ℕ => Delta_parity n - (Real.log 2 - 1 - Sigma_star_parity n) * (n : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
    refine h1.trans_isBigO ?_
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [(tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)] with n hln
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
    exact div_le_mul_of_nonneg_left (le_self_pow₀ hln (by norm_num : 2 ≠ 0) |> fun h => by nlinarith) (by positivity) (by linarith)
  have h2 : (fun n : ℕ => (Real.log 2 - 1 - Sigma_star_parity n) * (n : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
    have hconst : (fun n : ℕ => (Real.log 2 - 1 : ℝ)) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)) :=
      (isLittleO_const_id_atTop (Real.log 2 - 1)).comp_tendsto (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have hdiff := hconst.sub Sigma_star_parity_isLittleO_log
    have hmul := hdiff.mul_isBigO (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
    refine hmul.congr' (EventuallyEq.of_eq rfl) ?_
    filter_upwards with n; ring
  simpa [sub_add_cancel] using h1'.add h2

theorem n_log_n_sub_n_le_log_factorial (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) ≤ Real.log ((Nat.factorial n : ℕ) : ℝ) ∧
    Real.log ((Nat.factorial n : ℕ) : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
  constructor
  · induction n, hn using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_ne_zero m))]
      have hlog_diff : (m : ℝ) * Real.log ((m : ℝ) + 1) - (m : ℝ) * Real.log (m : ℝ) ≤ 1 := by
        have h1 : Real.log (((m : ℝ) + 1) / (m : ℝ)) ≤ ((m : ℝ) + 1) / (m : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div (by positivity) hm_pos.ne'] at h1
        have h2 : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by field_simp [hm_pos.ne']; ring
        rw [h2] at h1
        have h3 := mul_le_mul_of_nonneg_left h1 hm_pos.le
        rw [mul_one_div_cancel hm_pos.ne'] at h3
        linarith
      push_cast
      linarith
  · rw [← Finset.prod_Icc_id_eq_factorial, Nat.cast_prod, Real.log_prod (fun k hk => by
      exact_mod_cast (by have := (Finset.mem_Icc.mp hk).1; omega : k ≠ 0))]
    calc ∑ k ∈ Finset.Icc 1 n, Real.log (k : ℝ)
        ≤ ∑ _k ∈ Finset.Icc 1 n, Real.log (n : ℝ) := by
          refine Finset.sum_le_sum (fun k hk => Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp hk).1)
            (by exact_mod_cast (Finset.mem_Icc.mp hk).2))
      _ = (n : ℝ) * Real.log (n : ℝ) := by simp [Finset.sum_const, Nat.card_Icc]

/-- **Theorem 2.5(ii), eq. (2.17), part 3**:
`S_odd(n) = (1/2 + o(1)) n log n`. -/
theorem S_odd_asymptotic :
    (fun n : ℕ => S_odd n - (1 / 2 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  have hsum_eq : ∀ n : ℕ, 2 ≤ n →
      S_odd n + S_even n = Real.log ((Nat.factorial n : ℕ) : ℝ) -
        (padicValNat 2 (Nat.factorial n) : ℝ) * Real.log 2 := by
    intro n hn
    have hfac : Nat.factorial n ≠ 0 := Nat.factorial_ne_zero n
    have hsupp : (Nat.factorial n).factorization.support ⊆ (Finset.Icc 2 n).filter Nat.Prime := by
      intro p hp
      simp only [Finsupp.mem_support_iff, ne_eq] at hp
      have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by simpa [Nat.primeFactors] using hp)
      have hdvd : p ∣ Nat.factorial n := Nat.dvd_of_mem_primeFactors (by simpa [Nat.primeFactors] using hp)
      have hle : p ≤ n := hprime.dvd_factorial.mp hdvd
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hprime.two_le, hle⟩, hprime⟩
    have hlog_fac : Real.log ((Nat.factorial n : ℕ) : ℝ) =
        ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime,
          (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
      conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hfac]
      rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => by simp)]
      push_cast [Nat.cast_prod]
      rw [Real.log_prod (fun p hp => by
        have hprime : p.Prime := (Finset.mem_filter.mp hp).2
        exact_mod_cast pow_ne_zero _ hprime.ne_zero)]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hprime : p.Prime := (Finset.mem_filter.mp hp).2
      haveI : Fact p.Prime := ⟨hprime⟩
      rw [Nat.cast_pow, Real.log_pow, Nat.factorization_def _ hprime]
    have h2_mem : (2 : ℕ) ∈ (Finset.Icc 2 n).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hn⟩, Nat.prime_two⟩
    have h_ins : (Finset.Icc 2 n).filter Nat.Prime =
        insert 2 ((Finset.Icc 3 n).filter Nat.Prime) := by
      ext p
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hp2, hpn⟩, hp_pr⟩
        by_cases hp_eq : p = 2
        · left; exact hp_eq
        · right; exact ⟨⟨by omega, hpn⟩, hp_pr⟩
      · rintro (rfl | ⟨⟨hp3, hpn⟩, hp_pr⟩)
        · exact ⟨⟨le_rfl, hn⟩, Nat.prime_two⟩
        · exact ⟨⟨by omega, hpn⟩, hp_pr⟩
    have h2_not : (2 : ℕ) ∉ (Finset.Icc 3 n).filter Nat.Prime := by simp
    rw [hlog_fac, h_ins, Finset.sum_insert h2_not]
    have h_split3 : (Finset.Icc 3 n).filter Nat.Prime =
        ((Finset.Icc 3 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (Nat.factorial n))) ∪
        ((Finset.Icc 3 n).filter (fun p => p.Prime ∧ 2 ∣ padicValNat p (Nat.factorial n))) := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    have h_disj3 : Disjoint
        ((Finset.Icc 3 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (Nat.factorial n)))
        ((Finset.Icc 3 n).filter (fun p => p.Prime ∧ 2 ∣ padicValNat p (Nat.factorial n))) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact (Finset.mem_filter.mp h1).2.2 (Finset.mem_filter.mp h2).2.2
    have h_odd_eq : S_odd n =
        ∑ p ∈ (Finset.Icc 3 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (Nat.factorial n)),
          (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
      unfold S_odd Podd
      congr 1; ext p
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hp2, hpn⟩, hp_pr, hp_odd⟩, hp3⟩; exact ⟨⟨hp3, hpn⟩, hp_pr, hp_odd⟩
      · rintro ⟨⟨hp3, hpn⟩, hp_pr, hp_odd⟩; exact ⟨⟨⟨by omega, hpn⟩, hp_pr, hp_odd⟩, hp3⟩
    have h_even_eq : S_even n =
        ∑ p ∈ (Finset.Icc 3 n).filter (fun p => p.Prime ∧ 2 ∣ padicValNat p (Nat.factorial n)),
          (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
      unfold S_even Peven
      congr 1; ext p
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hp2, hpn⟩, hp_pr, hp_ev⟩, hp3⟩; exact ⟨⟨hp3, hpn⟩, hp_pr, hp_ev⟩
      · rintro ⟨⟨hp3, hpn⟩, hp_pr, hp_ev⟩; exact ⟨⟨⟨by omega, hpn⟩, hp_pr, hp_ev⟩, hp3⟩
    rw [h_split3, Finset.sum_union h_disj3, ← h_odd_eq, ← h_even_eq]
    ring
  have h_sum_asymp : (fun n : ℕ => S_odd n + S_even n - (n : ℝ) * Real.log (n : ℝ))
      =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    filter_upwards [Filter.eventually_ge_atTop 2,
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop ((1 + Real.log 2) / ε + 1))] with
      n hn hln
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlogn_pos : 0 < Real.log (n : ℝ) := by
      have : 0 ≤ (1 + Real.log 2) / ε := by positivity
      linarith
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hv2_le : padicValNat 2 (Nat.factorial n) ≤ n := by
      have hleg : (2 - 1) * padicValNat 2 (Nat.factorial n) = n - (Nat.digits 2 n).sum := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact sub_one_mul_padicValNat_factorial n
      omega
    have hfac := n_log_n_sub_n_le_log_factorial n (by omega)
    rw [hsum_eq n hn, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    have hbd : |Real.log ((Nat.factorial n : ℕ) : ℝ) - (padicValNat 2 (Nat.factorial n) : ℝ) * Real.log 2 -
          (n : ℝ) * Real.log (n : ℝ)| ≤ (n : ℝ) * (1 + Real.log 2) := by
      have hv2R : (padicValNat 2 (Nat.factorial n) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hv2_le
      rw [abs_le]
      constructor
      · nlinarith [hlog2_pos]
      · nlinarith [hlog2_pos]
    calc |Real.log ((Nat.factorial n : ℕ) : ℝ) - (padicValNat 2 (Nat.factorial n) : ℝ) * Real.log 2 -
            (n : ℝ) * Real.log (n : ℝ)|
        ≤ (n : ℝ) * (1 + Real.log 2) := hbd
      _ ≤ ε * ((n : ℝ) * Real.log (n : ℝ)) := by
          have : (1 + Real.log 2) / ε ≤ Real.log (n : ℝ) := by linarith
          have := (div_le_iff₀ hε).mp this
          nlinarith
  have h_eq : ∀ n : ℕ, S_odd n - (1 / 2 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) =
      (1 / 2 : ℝ) * (S_odd n + S_even n - (n : ℝ) * Real.log (n : ℝ)) -
      (1 / 2 : ℝ) * Delta_parity n := by
    intro n; unfold Delta_parity; ring
  simp_rw [h_eq]
  exact ((h_sum_asymp.const_mul_left (1 / 2)).sub (Delta_parity_isLittleO_mul_log.const_mul_left (1 / 2)))

/-- **Theorem 2.5(ii), eq. (2.17), part 4**:
`S_even(n) = (1/2 + o(1)) n log n`. -/
theorem S_even_asymptotic :
    (fun n : ℕ => S_even n - (1 / 2 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  have h_eq : ∀ n : ℕ, S_even n - (1 / 2 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) =
      (S_odd n - (1 / 2 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))) + Delta_parity n := by
    intro n; unfold Delta_parity; ring
  simp_rw [h_eq]
  exact S_odd_asymptotic.add Delta_parity_isLittleO_mul_log

end GrasGreenbergBrocard
