import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.ValuationParityDigits
import GrasGreenbergBrocard.ValuationParityVaaler
import GrasGreenbergBrocard.ExpSumBounds
import GrasGreenbergBrocard.ValuationParityThmHelpers
import GrasGreenbergBrocard.ValuationParityThm
import GrasGreenbergBrocard.VaalerMod

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard


/-! ### Total Weight Asymptotic on Power Bands -/

private lemma log_le_sqrt_of_two_mul_sqrt_log {n : ℕ} (hn : 16 ≤ n)
    (hsq_log : 2 * (Nat.sqrt n : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ)) :
    Real.log (n : ℝ) ≤ (Nat.sqrt n : ℝ) := by
  have hsq4 : (4 : ℝ) ≤ (Nat.sqrt n : ℝ) := by
    have : 4 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
    exact_mod_cast this
  have hn_le_sq : (n : ℝ) ≤ ((Nat.sqrt n + 1 : ℕ) : ℝ) ^ 2 := by
    have := Nat.lt_succ_sqrt' n
    exact_mod_cast (by nlinarith : n ≤ (Nat.sqrt n + 1) ^ 2)
  have h_sq_bound : ((Nat.sqrt n + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * (Nat.sqrt n : ℝ) ^ 2 := by
    push_cast; nlinarith [hsq4]
  nlinarith [hsq_log, hn_le_sq, h_sq_bound]

private lemma abs5_bound {a b c d e B1 B2 B3 B4 B5 M : ℝ}
    (h1 : |a| ≤ B1) (h2 : |b| ≤ B2) (h3 : |c| ≤ B3) (h4 : |d| ≤ B4) (h5 : |e| ≤ B5)
    (hsum : B1 + B2 + B3 + B4 + B5 ≤ M) :
    |a + b - c + d - e| ≤ M := by
  have h_abs5 : |a + b - c + d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
    linarith [abs_sub (a + b - c + d) e, abs_add_le (a + b - c) d, abs_sub (a + b) c, abs_add_le a b]
  linarith

theorem prefix_weight_isBigO (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (fun n : ℕ =>
      (∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ (n : ℝ) ^ α),
        (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) -
      α * ((n : ℝ) * Real.log (n : ℝ)))
      =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  obtain ⟨Cm, hCm_pos, hMertens⟩ := mertens_first_theorem
  obtain ⟨Cθ, hCθ_pos, hCθ⟩ := thetaPrime_le_linear
  let M : ℝ := Real.log 2 + Real.log 3 + 2 * Cm + 2 * Cθ + 4
  refine Asymptotics.IsBigO.of_bound M ?_
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
  filter_upwards [Filter.eventually_ge_atTop 16, h_sqrt_le] with n hn hsq_log
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hn_pos.le]
  let S := (Finset.Icc 2 n).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ (n : ℝ) ^ α)
  let S_2 : Finset ℕ := if (2 : ℝ) ≤ (n : ℝ) ^ α then {2} else ∅
  let S_low := S.filter (fun p : ℕ => 3 ≤ p ∧ p ≤ Nat.sqrt n)
  let S_hi := S.filter (fun p : ℕ => Nat.sqrt n < p)
  have hS_eq : S = S_2 ∪ S_low ∪ S_hi := by
    ext p
    simp only [Finset.mem_union, S, S_2, S_low, S_hi, Finset.mem_filter, Finset.mem_Icc]
    split_ifs with h2
    · simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hp2, hpn⟩, hp_pr, hpa⟩
        by_cases hp_eq : p = 2
        · left; left; exact hp_eq
        · by_cases hsq : p ≤ Nat.sqrt n
          · left; right; exact ⟨⟨⟨hp2, hpn⟩, hp_pr, hpa⟩, by omega, hsq⟩
          · right; exact ⟨⟨⟨hp2, hpn⟩, hp_pr, hpa⟩, by omega⟩
      · rintro ((rfl | ⟨hp, _⟩) | ⟨hp, _⟩)
        · exact ⟨⟨le_rfl, by omega⟩, Nat.prime_two, h2⟩
        · exact hp
        · exact hp
    · simp only [Finset.notMem_empty]
      constructor
      · rintro ⟨⟨hp2, hpn⟩, hp_pr, hpa⟩
        have hp_ne2 : p ≠ 2 := by rintro rfl; exact h2 hpa
        by_cases hsq : p ≤ Nat.sqrt n
        · left; right; exact ⟨⟨⟨hp2, hpn⟩, hp_pr, hpa⟩, by omega, hsq⟩
        · right; exact ⟨⟨⟨hp2, hpn⟩, hp_pr, hpa⟩, by omega⟩
      · rintro ((h | ⟨hp, _⟩) | ⟨hp, _⟩)
        · exact False.elim h
        · exact hp
        · exact hp
  have hdisj1 : Disjoint S_2 S_low := by
    rw [Finset.disjoint_left]; intro p hp1 hp2
    dsimp only [S_2] at hp1; split_ifs at hp1
    · rw [Finset.mem_singleton.mp hp1] at hp2
      have := (Finset.mem_filter.mp hp2).2.1; omega
    · exact absurd hp1 (Finset.notMem_empty _)
  have hdisj2 : Disjoint (S_2 ∪ S_low) S_hi := by
    rw [Finset.disjoint_left]; intro p hp1 hp2
    have hgt := (Finset.mem_filter.mp hp2).2
    rcases Finset.mem_union.mp hp1 with hp1 | hp1
    · dsimp only [S_2] at hp1; split_ifs at hp1
      · rw [Finset.mem_singleton.mp hp1] at hgt
        have hsq4 : 4 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
        omega
      · exact absurd hp1 (Finset.notMem_empty _)
    · have hle := (Finset.mem_filter.mp hp1).2.2; omega
  have hS_sum : ∑ p ∈ S, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) =
      (∑ p ∈ S_2, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) +
      (∑ p ∈ S_low, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) +
      (∑ p ∈ S_hi, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) := by
    rw [hS_eq, Finset.sum_union hdisj2, Finset.sum_union hdisj1]
  have hS2_bound : |∑ p ∈ S_2, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)| ≤ Real.log 2 * (n : ℝ) := by
    dsimp only [S_2]; split_ifs
    · simp only [Finset.sum_singleton, Nat.cast_ofNat]
      have hv2_le : padicValNat 2 (Nat.factorial n) ≤ n := by
        have hleg : (2 - 1) * padicValNat 2 (Nat.factorial n) = n - (Nat.digits 2 n).sum := by
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          exact sub_one_mul_padicValNat_factorial n
        omega
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog2_pos.le)]
      have : (padicValNat 2 (Nat.factorial n) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hv2_le
      nlinarith
    · simp; positivity
  -- Bound S_low using Legendre's identity v_p(n!) = (n - s_p(n)) / (p - 1)
  have hS_low_eq : ∑ p ∈ S_low, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) =
      (n : ℝ) * (∑ p ∈ S_low, Real.log (p : ℝ) / ((p : ℝ) - 1)) -
      (∑ p ∈ S_low, ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
    have hp3 : 3 ≤ p := (Finset.mem_filter.mp hp).2.1
    have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : p ≠ 1))
    have hleg : (p - 1) * padicValNat p (Nat.factorial n) = n - (Nat.digits p n).sum := by
      haveI : Fact p.Prime := ⟨hp_pr⟩
      exact sub_one_mul_padicValNat_factorial n
    have hsum_le : (Nat.digits p n).sum ≤ n := by
      have := Nat.ofDigits_digits p n
      calc (Nat.digits p n).sum ≤ Nat.ofDigits p (Nat.digits p n) := Nat.sum_le_ofDigits (Nat.digits p n) hp_pr.pos
        _ = n := this
    have hlegR : ((p : ℝ) - 1) * (padicValNat p (Nat.factorial n) : ℝ) =
        (n : ℝ) - ((Nat.digits p n).sum : ℝ) := by
      have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring
      have hleg' : (p - 1) * padicValNat p (Nat.factorial n) + (Nat.digits p n).sum = n := by omega
      have hR : ((p - 1 : ℕ) : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) + ((Nat.digits p n).sum : ℝ) = (n : ℝ) := by
        exact_mod_cast hleg'
      rw [hsub] at hR
      linarith
    have hdiv : (padicValNat p (Nat.factorial n) : ℝ) =
        ((n : ℝ) - ((Nat.digits p n).sum : ℝ)) / ((p : ℝ) - 1) :=
      (eq_div_iff hp1).mpr (by linarith)
    rw [hdiv]; ring
  have h_dig_err : |∑ p ∈ S_low, ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ)| ≤ (n : ℝ) := by
    have h_each : ∀ p ∈ S_low, 0 ≤ ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ) ∧
        ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ) ≤ 2 * Real.log (n : ℝ) := by
      intro p hp
      have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
      have hp3 : 3 ≤ p := (Finset.mem_filter.mp hp).2.1
      have hpn : p ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2
      have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < p))
      have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
      constructor
      · positivity
      · have hdig_len : (Nat.digits p n).length ≤ Nat.floor (Real.log (n : ℝ) / Real.log (p : ℝ)) + 1 := by
          have h1 : p ^ ((Nat.digits p n).length - 1) ≤ n := by
            rcases eq_or_ne (Nat.digits p n).length 0 with hl0 | hlne
            · simp [hl0]; omega
            · have h_mul : p * p ^ ((Nat.digits p n).length - 1) ≤ p * n := by
                rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hlne)]
                exact Nat.base_pow_length_digits_le p n hp_pr.one_lt (by omega)
              exact Nat.le_of_mul_le_mul_left h_mul hp_pr.pos
          have h2 : (((Nat.digits p n).length - 1 : ℕ) : ℝ) * Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
            have : ((p ^ ((Nat.digits p n).length - 1) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
            have hlog := Real.log_le_log (by positivity) this
            rwa [Nat.cast_pow, Real.log_pow] at hlog
          have h3 : (((Nat.digits p n).length - 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) / Real.log (p : ℝ) :=
            (le_div_iff₀ hlogp_pos).mpr h2
          have h4 : (Nat.digits p n).length - 1 ≤ Nat.floor (Real.log (n : ℝ) / Real.log (p : ℝ)) :=
            (Nat.le_floor_iff (div_nonneg hlogn_nn hlogp_pos.le)).mpr h3
          omega
        have hdig_sum : (Nat.digits p n).sum ≤ (Nat.digits p n).length * (p - 1) := by
          have h_list : ∀ L : List ℕ, (∀ d ∈ L, d ≤ p - 1) → L.sum ≤ L.length * (p - 1) := by
            intro L hL
            induction L with
            | nil => simp
            | cons a l ih =>
              simp only [List.sum_cons, List.length_cons]
              have ha := hL a (by simp)
              have hl := ih (fun d hd => hL d (by simp [hd]))
              nlinarith
          exact h_list (Nat.digits p n) (fun d hd => Nat.le_sub_one_of_lt (Nat.digits_lt_base hp_pr.one_lt hd))
        have hsum_R : ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) ≤ Real.log (n : ℝ) / Real.log (p : ℝ) + 1 := by
          have h1 : ((Nat.digits p n).sum : ℝ) ≤ ((Nat.digits p n).length : ℝ) * ((p : ℝ) - 1) := by
            have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring
            rw [← this]; exact_mod_cast hdig_sum
          have h2 : ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) ≤ ((Nat.digits p n).length : ℝ) := by
            rw [div_le_iff₀ hp1_pos]; exact h1
          have h3 : ((Nat.digits p n).length : ℝ) ≤ (Nat.floor (Real.log (n : ℝ) / Real.log (p : ℝ)) : ℝ) + 1 := by
            exact_mod_cast hdig_len
          have h4 : (Nat.floor (Real.log (n : ℝ) / Real.log (p : ℝ)) : ℝ) ≤ Real.log (n : ℝ) / Real.log (p : ℝ) :=
            Nat.floor_le (div_nonneg hlogn_nn hlogp_pos.le)
          linarith
        have hlogp_le : Real.log (p : ℝ) ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hpn)
        have h_mul_le : ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ) ≤
            (Real.log (n : ℝ) / Real.log (p : ℝ) + 1) * Real.log (p : ℝ) :=
          mul_le_mul_of_nonneg_right hsum_R hlogp_pos.le
        have h_eq_add : (Real.log (n : ℝ) / Real.log (p : ℝ) + 1) * Real.log (p : ℝ) =
            Real.log (n : ℝ) + Real.log (p : ℝ) := by
          field_simp [hlogp_pos.ne']
        linarith
    have hnn : 0 ≤ ∑ p ∈ S_low, ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ) :=
      Finset.sum_nonneg (fun p hp => (h_each p hp).1)
    rw [abs_of_nonneg hnn]
    have hcard : (S_low.card : ℝ) ≤ (Nat.sqrt n : ℝ) := by
      have hsub : S_low ⊆ Finset.Icc 1 (Nat.sqrt n) := fun p hp =>
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_filter.mp hp).2.1; omega, (Finset.mem_filter.mp hp).2.2⟩
      exact_mod_cast le_trans (Finset.card_le_card hsub) (by simp)
    calc ∑ p ∈ S_low, ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ)
        ≤ ∑ _p ∈ S_low, 2 * Real.log (n : ℝ) := Finset.sum_le_sum (fun p hp => (h_each p hp).2)
      _ = (S_low.card : ℝ) * (2 * Real.log (n : ℝ)) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Nat.sqrt n : ℝ) * (2 * Real.log (n : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (n : ℝ) := by linarith
  -- Now split by α ≤ 1/2 vs α > 1/2
  have h_nα_le_n : (n : ℝ) ^ α ≤ (n : ℝ) := by
    calc (n : ℝ) ^ α ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) hα1
      _ = (n : ℝ) := Real.rpow_one _
  have h_mert_bound : ∀ X : ℝ, 1 ≤ X →
      |∑ p ∈ (Finset.Icc 3 (Nat.floor X)).filter Nat.Prime, Real.log (p : ℝ) / ((p : ℝ) - 1) - Real.log X| ≤
        Real.log 3 + Cm := by
    intro X hX
    rcases lt_or_ge X 3 with hlt | hge
    · have hemp : (Finset.Icc 3 (Nat.floor X)).filter Nat.Prime = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        have h1 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
        have h2 : p ≤ Nat.floor X := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
        have h3 : (p : ℝ) ≤ X := le_trans (by exact_mod_cast h2) (Nat.floor_le (by linarith))
        have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h1
        linarith
      rw [hemp, Finset.sum_empty, zero_sub, abs_neg, abs_of_nonneg (Real.log_nonneg hX)]
      have : Real.log X ≤ Real.log 3 := Real.log_le_log (by linarith) hlt.le
      linarith [hCm_pos]
    · exact le_trans (hMertens X hge) (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)])
  have h_nα_ge1 : 1 ≤ (n : ℝ) ^ α := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) hα0
  have h_sqrt_ge3 : (3 : ℝ) ≤ (Nat.sqrt n : ℝ) := by
    have : 4 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
    exact_mod_cast (by omega : 3 ≤ Nat.sqrt n)
  have h_p_le_sqrt_of_le_rpow : ∀ p : ℕ, (p : ℝ) ≤ (n : ℝ) ^ α → α ≤ 1 / 2 → p ≤ Nat.sqrt n := by
    intro p hp hα_le
    have h1 : (p : ℝ) ≤ Real.sqrt (n : ℝ) := by
      calc (p : ℝ) ≤ (n : ℝ) ^ α := hp
        _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) hα_le
        _ = Real.sqrt (n : ℝ) := (Real.sqrt_eq_rpow (n : ℝ)).symm
    have h2 : (p : ℝ) ^ 2 ≤ (n : ℝ) := by
      calc (p : ℝ) ^ 2 ≤ (Real.sqrt (n : ℝ)) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) p]
        _ = (n : ℝ) := Real.sq_sqrt hn_pos.le
    rw [Nat.le_sqrt]
    exact_mod_cast (by simpa [sq] using h2 : ((p * p : ℕ) : ℝ) ≤ (n : ℝ))
  rcases le_or_gt α (1 / 2 : ℝ) with hα_lo | hα_hi
  · -- Case α ≤ 1/2: S_hi is empty and S_low = (Icc 3 ⌊n^α⌋).filter Prime
    have hS_hi_empty : S_hi = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      have hp1 := (Finset.mem_filter.mp hp).1
      have hp2 := (Finset.mem_filter.mp hp).2
      have hpa := (Finset.mem_filter.mp hp1).2.2
      have hle := h_p_le_sqrt_of_le_rpow p hpa hα_lo
      omega
    have hS_low_eq_Icc : S_low = (Finset.Icc 3 (Nat.floor ((n : ℝ) ^ α))).filter Nat.Prime := by
      ext p
      simp only [S_low, S, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨_, hpn⟩, hp_pr, hpa⟩, hp3, _⟩
        exact ⟨⟨hp3, (Nat.le_floor_iff (by positivity)).mpr hpa⟩, hp_pr⟩
      · rintro ⟨⟨hp3, hpfl⟩, hp_pr⟩
        have hpa : (p : ℝ) ≤ (n : ℝ) ^ α := le_trans (by exact_mod_cast hpfl) (Nat.floor_le (by positivity))
        have hpn : p ≤ n := by exact_mod_cast le_trans hpa h_nα_le_n
        exact ⟨⟨⟨by omega, hpn⟩, hp_pr, hpa⟩, hp3, h_p_le_sqrt_of_le_rpow p hpa hα_lo⟩
    have hmert := h_mert_bound ((n : ℝ) ^ α) h_nα_ge1
    rw [← hS_low_eq_Icc, Real.log_rpow hn_pos] at hmert
    have hS_hi_sum : ∑ p ∈ S_hi, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) = 0 := by
      rw [hS_hi_empty, Finset.sum_empty]
    have h_diff : (∑ p ∈ S, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) -
          α * ((n : ℝ) * Real.log (n : ℝ)) =
        (∑ p ∈ S_2, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) +
        (n : ℝ) * ((∑ p ∈ S_low, Real.log (p : ℝ) / ((p : ℝ) - 1)) - α * Real.log (n : ℝ)) -
        (∑ p ∈ S_low, ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ)) := by
      rw [hS_sum, hS_hi_sum, add_zero, hS_low_eq]; ring
    rw [h_diff]
    have h_abs3 : ∀ a b c : ℝ, |a + b - c| ≤ |a| + |b| + |c| := fun a b c =>
      by linarith [abs_sub (a + b) c, abs_add_le a b]
    calc |(∑ p ∈ S_2, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) +
          (n : ℝ) * ((∑ p ∈ S_low, Real.log (p : ℝ) / ((p : ℝ) - 1)) - α * Real.log (n : ℝ)) -
          (∑ p ∈ S_low, ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ))|
        ≤ |∑ p ∈ S_2, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)| +
          |(n : ℝ) * ((∑ p ∈ S_low, Real.log (p : ℝ) / ((p : ℝ) - 1)) - α * Real.log (n : ℝ))| +
          |∑ p ∈ S_low, ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ)| := h_abs3 _ _ _
      _ ≤ Real.log 2 * (n : ℝ) +
          (n : ℝ) * (Real.log 3 + Cm) + (n : ℝ) := by
            refine add_le_add (add_le_add hS2_bound ?_) h_dig_err
            rw [abs_mul, abs_of_nonneg hn_pos.le]
            exact mul_le_mul_of_nonneg_left hmert hn_pos.le
      _ ≤ M * (n : ℝ) := by
            dsimp only [M]
            nlinarith [hCm_pos, hCθ_pos]
  · -- Case α > 1/2: S_low = (Icc 3 (Nat.sqrt n)).filter Prime, S_hi = (Icc (Nat.sqrt n + 1) ⌊n^α⌋).filter Prime
    have h_sqrt_le_nα : (Nat.sqrt n : ℝ) ≤ (n : ℝ) ^ α := by
      calc (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
            rw [Real.le_sqrt (by positivity) hn_pos.le]; exact_mod_cast Nat.sqrt_le' n
        _ = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (n : ℝ)
        _ ≤ (n : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) hα_hi.le
    have hS_low_eq_Icc : S_low = (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime := by
      ext p
      simp only [S_low, S, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨_, hp_pr, _⟩, hp3, hsq⟩; exact ⟨⟨hp3, hsq⟩, hp_pr⟩
      · rintro ⟨⟨hp3, hsq⟩, hp_pr⟩
        have hpa : (p : ℝ) ≤ (n : ℝ) ^ α := le_trans (by exact_mod_cast hsq) h_sqrt_le_nα
        have hpn : p ≤ n := by exact_mod_cast le_trans hpa h_nα_le_n
        exact ⟨⟨⟨by omega, hpn⟩, hp_pr, hpa⟩, hp3, hsq⟩
    have hS_hi_eq_Icc : S_hi = ((Finset.Icc 3 (Nat.floor ((n : ℝ) ^ α))).filter Nat.Prime).filter (fun p => Nat.sqrt n < p) := by
      ext p
      simp only [S_hi, S, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hp2, _⟩, hp_pr, hpa⟩, hsq⟩
        have hsq4 : 4 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
        have hp3 : 3 ≤ p := by omega
        exact ⟨⟨⟨hp3, (Nat.le_floor_iff (by positivity)).mpr hpa⟩, hp_pr⟩, hsq⟩
      · rintro ⟨⟨⟨hp3, hpfl⟩, hp_pr⟩, hsq⟩
        have hpa : (p : ℝ) ≤ (n : ℝ) ^ α := le_trans (by exact_mod_cast hpfl) (Nat.floor_le (by positivity))
        have hpn : p ≤ n := by exact_mod_cast le_trans hpa h_nα_le_n
        exact ⟨⟨⟨by omega, hpn⟩, hp_pr, hpa⟩, hsq⟩
    -- Mertens on S_low and S_hi
    have hmert_sqrt := h_mert_bound (Nat.sqrt n : ℝ) (by linarith)
    rw [Nat.floor_natCast, ← hS_low_eq_Icc] at hmert_sqrt
    have hmert_nα := h_mert_bound ((n : ℝ) ^ α) h_nα_ge1
    rw [Real.log_rpow hn_pos] at hmert_nα
    -- Split (Icc 3 ⌊n^α⌋).filter Prime into S_low ∪ S_hi
    have h_all_eq : (Finset.Icc 3 (Nat.floor ((n : ℝ) ^ α))).filter Nat.Prime = S_low ∪ S_hi := by
      rw [hS_low_eq_Icc, hS_hi_eq_Icc]
      ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hp3, hpfl⟩, hp_pr⟩
        by_cases hsq : p ≤ Nat.sqrt n
        · left; exact ⟨⟨hp3, hsq⟩, hp_pr⟩
        · right; exact ⟨⟨⟨hp3, hpfl⟩, hp_pr⟩, by omega⟩
      · rintro (⟨⟨hp3, hsq⟩, hp_pr⟩ | ⟨⟨⟨hp3, hpfl⟩, hp_pr⟩, _⟩)
        · have hpfl : p ≤ Nat.floor ((n : ℝ) ^ α) :=
            (Nat.le_floor_iff (by positivity)).mpr (le_trans (by exact_mod_cast hsq) h_sqrt_le_nα)
          exact ⟨⟨hp3, hpfl⟩, hp_pr⟩
        · exact ⟨⟨hp3, hpfl⟩, hp_pr⟩
    have hdisj_lh : Disjoint S_low S_hi := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      have hle := (Finset.mem_filter.mp hp1).2.2
      have hgt := (Finset.mem_filter.mp hp2).2
      omega
    have h_mert_sum : (∑ p ∈ S_low, Real.log (p : ℝ) / ((p : ℝ) - 1)) +
        (∑ p ∈ S_hi, Real.log (p : ℝ) / ((p : ℝ) - 1)) =
        ∑ p ∈ (Finset.Icc 3 (Nat.floor ((n : ℝ) ^ α))).filter Nat.Prime, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
      rw [h_all_eq, Finset.sum_union hdisj_lh]
    -- On S_hi, v_p(n!) = n / p, so v_p(n!) * log p = (n / p : ℕ) * log p
    have hS_hi_val : ∑ p ∈ S_hi, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) =
        ∑ p ∈ S_hi, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
      have hgt : Nat.sqrt n < p := (Finset.mem_filter.mp hp).2
      have hn_lt : n < p ^ 2 := by
        have := Nat.lt_succ_sqrt' n
        have : Nat.sqrt n + 1 ≤ p := hgt
        nlinarith
      rw [padicValNat_factorial_eq_div_of_lt_sq hp_pr hn_lt]
    -- Compare (n / p : ℕ) * log p with (n / p) * log p
    have h_frac_err : |(∑ p ∈ S_hi, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ)) -
          (n : ℝ) * (∑ p ∈ S_hi, Real.log (p : ℝ) / (p : ℝ))| ≤ Cθ * (n : ℝ) := by
      have h_eq : (n : ℝ) * (∑ p ∈ S_hi, Real.log (p : ℝ) / (p : ℝ)) -
            (∑ p ∈ S_hi, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ)) =
          ∑ p ∈ S_hi, (((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun p _ => by ring)
      rw [abs_sub_comm, h_eq]
      have h_each : ∀ p ∈ S_hi,
          0 ≤ ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ) ∧
          ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ) ≤ Real.log (p : ℝ) := by
        intro p hp
        have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
        have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
        have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
        have h1 : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / (p : ℝ) := by
          have : (p : ℝ) * ((n / p : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.mul_div_le n p
          exact (le_div_iff₀ hp_pos).mpr (by linarith)
        have h2 : (n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ) < 1 := by
          have hlt : n < p * (n / p + 1) := by
            have := Nat.div_add_mod n p
            have := Nat.mod_lt n (by omega : 0 < p)
            nlinarith
          have hltR : (n : ℝ) < (p : ℝ) * (((n / p : ℕ) : ℝ) + 1) := by exact_mod_cast hlt
          have := (div_lt_iff₀ hp_pos).mpr (by linarith : (n : ℝ) < (((n / p : ℕ) : ℝ) + 1) * (p : ℝ))
          linarith
        constructor
        · exact mul_nonneg (by linarith) hlogp_nn
        · nlinarith
      rw [abs_of_nonneg (Finset.sum_nonneg (fun p hp => (h_each p hp).1))]
      have hsub : S_hi ⊆ (Finset.Icc 2 n).filter Nat.Prime := fun p hp =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1,
          (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1⟩
      calc ∑ p ∈ S_hi, (((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ))
          ≤ ∑ p ∈ S_hi, Real.log (p : ℝ) := Finset.sum_le_sum (fun p hp => (h_each p hp).2)
        _ ≤ ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, Real.log (p : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => Real.log_nonneg (by exact_mod_cast (by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; omega : 1 ≤ p)))
        _ = thetaPrime (n : ℝ) := by
            unfold thetaPrime
            congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_Icc, Nat.floor_natCast]
        _ ≤ Cθ * (n : ℝ) := hCθ (n : ℝ) (by exact_mod_cast (by omega : 1 ≤ n))
    -- Compare ∑_{S_hi} log p / p with ∑_{S_hi} log p / (p - 1) via telescoping ∑ 1/(k*(k-1))
    have h_p_p1 : |∑ p ∈ S_hi, Real.log (p : ℝ) / ((p : ℝ) - 1) - ∑ p ∈ S_hi, Real.log (p : ℝ) / (p : ℝ)| ≤ 1 := by
      have h_eq : ∑ p ∈ S_hi, Real.log (p : ℝ) / ((p : ℝ) - 1) - ∑ p ∈ S_hi, Real.log (p : ℝ) / (p : ℝ) =
          ∑ p ∈ S_hi, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
        have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
        have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : p ≠ 1))
        field_simp [hp0, hp1]; ring
      rw [h_eq]
      have h_nn : 0 ≤ ∑ p ∈ S_hi, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        refine Finset.sum_nonneg (fun p hp => ?_)
        have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
        have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
        have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast (by omega : 1 ≤ p))
        positivity
      rw [abs_of_nonneg h_nn]
      have hsub : S_hi ⊆ Finset.Icc (Nat.sqrt n + 1) n := fun p hp =>
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_filter.mp hp).2; omega,
          (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2⟩
      have h_tele : ∑ k ∈ Finset.Icc (Nat.sqrt n + 1) n, ((1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ)) ≤
          1 / (Nat.sqrt n : ℝ) := by
        have h_Ico : Finset.Icc (Nat.sqrt n + 1) n = Finset.Ico (Nat.sqrt n + 1) (n + 1) := rfl
        rw [h_Ico]
        have h_le : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
        have h_eq_tele : ∑ k ∈ Finset.Ico (Nat.sqrt n + 1) (n + 1),
              ((1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ)) =
            (1 : ℝ) / (Nat.sqrt n : ℝ) - (1 : ℝ) / (n : ℝ) := by
          have h1 : ∀ k ∈ Finset.Ico (Nat.sqrt n + 1) (n + 1),
              ((1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ)) =
              ((1 : ℝ) / ((k - 1 : ℕ) : ℝ) - (1 : ℝ) / (k : ℝ)) := by
            intro k hk
            have hk1 : 1 ≤ k := by have := (Finset.mem_Ico.mp hk).1; omega
            rw [Nat.cast_sub hk1, Nat.cast_one]
          rw [Finset.sum_congr rfl h1]
          have h2 : ∑ k ∈ Finset.Ico (Nat.sqrt n + 1) (n + 1),
                ((1 : ℝ) / ((k - 1 : ℕ) : ℝ) - (1 : ℝ) / (k : ℝ)) =
              ∑ k ∈ Finset.Ico (Nat.sqrt n) n, ((1 : ℝ) / (k : ℝ) - (1 : ℝ) / ((k + 1 : ℕ) : ℝ)) := by
            rw [← Finset.sum_Ico_add (fun k : ℕ => (1 : ℝ) / ((k - 1 : ℕ) : ℝ) - (1 : ℝ) / (k : ℝ)) (Nat.sqrt n) n 1]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            have h_k : ∀ m : ℕ, m + 1 - 1 = m := fun m => by omega
            have h_k' : ∀ m : ℕ, 1 + m - 1 = m := fun m => by omega
            simp only [h_k, h_k', Nat.cast_add, Nat.cast_one]
            ring
          rw [h2, Finset.sum_Ico_eq_sum_range]
          have h3 : ∑ k ∈ Finset.range (n - Nat.sqrt n),
                ((1 : ℝ) / ((Nat.sqrt n + k : ℕ) : ℝ) - (1 : ℝ) / ((Nat.sqrt n + k + 1 : ℕ) : ℝ)) =
              (1 : ℝ) / ((Nat.sqrt n + 0 : ℕ) : ℝ) - (1 : ℝ) / ((Nat.sqrt n + (n - Nat.sqrt n) : ℕ) : ℝ) :=
            Finset.sum_range_sub' (fun k : ℕ => (1 : ℝ) / ((Nat.sqrt n + k : ℕ) : ℝ)) (n - Nat.sqrt n)
          rw [h3]
          simp [Nat.add_sub_of_le h_le]
        linarith [show (0 : ℝ) ≤ 1 / (n : ℝ) from by positivity]
      calc ∑ p ∈ S_hi, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
          ≤ ∑ p ∈ S_hi, Real.log (n : ℝ) * ((1 : ℝ) / ((p : ℝ) - 1) - (1 : ℝ) / (p : ℝ)) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
            have hpn : p ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2
            have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
            have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : p ≠ 1))
            have h_id : (1 : ℝ) / ((p : ℝ) - 1) - (1 : ℝ) / (p : ℝ) = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
              field_simp [hp0, hp1]; ring
            rw [h_id, ← mul_div_assoc, mul_one]
            apply div_le_div_of_nonneg_right (Real.log_le_log (by positivity) (by exact_mod_cast hpn))
            have : (0 : ℝ) ≤ (p : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast (by omega : 1 ≤ p))
            positivity
        _ ≤ ∑ k ∈ Finset.Icc (Nat.sqrt n + 1) n, Real.log (n : ℝ) * ((1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => ?_)
            have hk2 : 2 ≤ k := by
              have : 4 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
              have := (Finset.mem_Icc.mp hk).1; omega
            have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
            have hk1 : (0 : ℝ) < (k : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < k))
            have : (1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ) = 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
              field_simp [hk0.ne', hk1.ne']; ring
            rw [this]; positivity
        _ = Real.log (n : ℝ) * ∑ k ∈ Finset.Icc (Nat.sqrt n + 1) n, ((1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ)) := by
            rw [← Finset.mul_sum]
        _ ≤ Real.log (n : ℝ) * (1 / (Nat.sqrt n : ℝ)) := mul_le_mul_of_nonneg_left h_tele hlogn_nn
        _ ≤ 1 := by
            have hsq4_nat : 4 ≤ Nat.sqrt n := by rw [Nat.le_sqrt]; omega
            rw [mul_one_div, div_le_one (by exact_mod_cast (by omega : 0 < Nat.sqrt n))]
            exact log_le_sqrt_of_two_mul_sqrt_log hn hsq_log
    -- Combine everything for α > 1/2
    have h_diff : (∑ p ∈ S, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) -
          α * ((n : ℝ) * Real.log (n : ℝ)) =
        (∑ p ∈ S_2, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) +
        (n : ℝ) * ((∑ p ∈ (Finset.Icc 3 (Nat.floor ((n : ℝ) ^ α))).filter Nat.Prime,
            Real.log (p : ℝ) / ((p : ℝ) - 1)) - α * Real.log (n : ℝ)) -
        (n : ℝ) * (∑ p ∈ S_hi, Real.log (p : ℝ) / ((p : ℝ) - 1) - ∑ p ∈ S_hi, Real.log (p : ℝ) / (p : ℝ)) +
        ((∑ p ∈ S_hi, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ)) - (n : ℝ) * (∑ p ∈ S_hi, Real.log (p : ℝ) / (p : ℝ))) -
        (∑ p ∈ S_low, ((Nat.digits p n).sum : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ)) := by
      rw [hS_sum, hS_hi_val, hS_low_eq, ← h_mert_sum]; ring
    rw [h_diff]
    refine abs5_bound hS2_bound ?_ ?_ h_frac_err h_dig_err ?_
    · rw [abs_mul, abs_of_nonneg hn_pos.le]
      exact mul_le_mul_of_nonneg_left hmert_nα hn_pos.le
    · rw [abs_mul, abs_of_nonneg hn_pos.le]
      exact mul_le_mul_of_nonneg_left h_p_p1 hn_pos.le
    · dsimp only [M]
      nlinarith [hCm_pos, hCθ_pos]

theorem band_total_weight_isBigO (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (fun n : ℕ =>
      (∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
        p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b),
        (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) -
      (b - a) * ((n : ℝ) * Real.log (n : ℝ)))
      =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  have ha1 : a ≤ 1 := le_trans hab.le hb
  have hb0 : 0 ≤ b := le_trans ha hab.le
  have hA := prefix_weight_isBigO a ha ha1
  have hB := prefix_weight_isBigO b hb0 hb
  have hsub := hB.sub hA
  refine hsub.congr' ?_ EventuallyEq.rfl
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  let Sb := (Finset.Icc 2 n).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ (n : ℝ) ^ b)
  let Sa := (Finset.Icc 2 n).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) ≤ (n : ℝ) ^ a)
  let Sab := (Finset.Icc 2 n).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ b)
  have hSb_eq : Sb = Sa ∪ Sab := by
    ext p
    simp only [Sb, Sa, Sab, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hp, hp_pr, hpb⟩
      by_cases hpa : (p : ℝ) ≤ (n : ℝ) ^ a
      · left; exact ⟨hp, hp_pr, hpa⟩
      · right; exact ⟨hp, hp_pr, lt_of_not_ge hpa, hpb⟩
    · rintro (⟨hp, hp_pr, hpa⟩ | ⟨hp, hp_pr, _, hpb⟩)
      · refine ⟨hp, hp_pr, le_trans hpa (Real.rpow_le_rpow_of_exponent_le hn_ge1 hab.le)⟩
      · exact ⟨hp, hp_pr, hpb⟩
  have hdisj : Disjoint Sa Sab := by
    rw [Finset.disjoint_left]; intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2.2
    have h2 := (Finset.mem_filter.mp hp2).2.2.1
    linarith
  have hsum : ∑ p ∈ Sb, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) =
      (∑ p ∈ Sa, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) +
      (∑ p ∈ Sab, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) := by
    rw [hSb_eq, Finset.sum_union hdisj]
  change (∑ p ∈ Sb, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) -
      b * ((n : ℝ) * Real.log (n : ℝ)) -
      ((∑ p ∈ Sa, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) -
      a * ((n : ℝ) * Real.log (n : ℝ))) =
      (∑ p ∈ Sab, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) -
      (b - a) * ((n : ℝ) * Real.log (n : ℝ))
  rw [hsum]; ring

lemma prod_sub_prod_norm_le {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f g : ι → ℂ) (E : ι → ℝ) (M : ℝ) (hM1 : 1 ≤ M)
    (hf : ∀ s ∈ S, ‖f s‖ = 1)
    (hg : ∀ s ∈ S, ‖g s‖ ≤ M)
    (hE : ∀ s ∈ S, ‖f s - g s‖ ≤ E s) :
    ‖∏ s ∈ S, f s - ∏ s ∈ S, g s‖ ≤ M ^ S.card * ∑ s ∈ S, E s := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      Finset.sum_insert ha]
    have h_id : f a * ∏ s ∈ S, f s - g a * ∏ s ∈ S, g s =
        (f a - g a) * ∏ s ∈ S, f s + g a * (∏ s ∈ S, f s - ∏ s ∈ S, g s) := by ring
    rw [h_id]
    have hfa_mem : a ∈ insert a S := Finset.mem_insert_self a S
    have hfS : ∀ s ∈ S, ‖f s‖ = 1 := fun s hs => hf s (Finset.mem_insert_of_mem hs)
    have hgS : ∀ s ∈ S, ‖g s‖ ≤ M := fun s hs => hg s (Finset.mem_insert_of_mem hs)
    have hES : ∀ s ∈ S, ‖f s - g s‖ ≤ E s := fun s hs => hE s (Finset.mem_insert_of_mem hs)
    have hprod_f : ‖∏ s ∈ S, f s‖ = 1 := by
      rw [norm_prod]
      exact Finset.prod_eq_one (fun s hs => hfS s hs)
    have h1 : ‖(f a - g a) * ∏ s ∈ S, f s‖ ≤ E a * M ^ (S.card + 1) := by
      rw [norm_mul, hprod_f, mul_one]
      have hEa0 : 0 ≤ E a := le_trans (norm_nonneg _) (hE a hfa_mem)
      have hMp : 1 ≤ M ^ (S.card + 1) := one_le_pow₀ hM1
      calc ‖f a - g a‖ ≤ E a := hE a hfa_mem
        _ = E a * 1 := (mul_one _).symm
        _ ≤ E a * M ^ (S.card + 1) := mul_le_mul_of_nonneg_left hMp hEa0
    have h2 : ‖g a * (∏ s ∈ S, f s - ∏ s ∈ S, g s)‖ ≤ M ^ (S.card + 1) * ∑ s ∈ S, E s := by
      rw [norm_mul]
      calc ‖g a‖ * ‖∏ s ∈ S, f s - ∏ s ∈ S, g s‖
          ≤ M * (M ^ S.card * ∑ s ∈ S, E s) :=
            mul_le_mul (hg a hfa_mem) (ih hfS hgS hES) (norm_nonneg _) (by positivity)
        _ = M ^ (S.card + 1) * ∑ s ∈ S, E s := by rw [pow_succ']; ring
    calc ‖(f a - g a) * ∏ s ∈ S, f s + g a * (∏ s ∈ S, f s - ∏ s ∈ S, g s)‖
        ≤ ‖(f a - g a) * ∏ s ∈ S, f s‖ + ‖g a * (∏ s ∈ S, f s - ∏ s ∈ S, g s)‖ := norm_add_le _ _
      _ ≤ E a * M ^ (S.card + 1) + M ^ (S.card + 1) * ∑ s ∈ S, E s := add_le_add h1 h2
      _ = M ^ (S.card + 1) * (E a + ∑ s ∈ S, E s) := by ring


end GrasGreenbergBrocard
