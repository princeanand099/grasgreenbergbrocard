import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false

/-!
# Lemma 2.2: Exact Legendre Base-`p` Reduction on `3 ≤ p ≤ √n`

Formalizes Section 2.2 of the manuscript:
- `legendre_base_p_identity`: `(p - 1) * v_p(n!) = n - s_p(n)`
- `exact_legendre_base_p_reduction` (eq. 2.6)
- `E_digit_bound` (eq. 2.7): `|E_digit(n)| ≤ 2 * π(√n) * log n` and `E_digit(n) = O(√n)`.
-/

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard

/-- Base-`p` digit sum `s_p(n) := (Nat.digits p n).sum`. -/
def basePDigitSum (p n : ℕ) : ℕ :=
  (Nat.digits p n).sum

/-- Digit-sum remainder `E_digit(n) := ∑_{3 ≤ p ≤ √n} (-1)^{v_p(n!)-1} s_p(n) log p / (p - 1)`. -/
def E_digit (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
    ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) *
      (((basePDigitSum p n : ℝ) * Real.log (p : ℝ)) / ((p : ℝ) - 1))

/-- Legendre's base-`p` identity: `(p - 1) * v_p(n!) = n - s_p(n)`. -/
theorem legendre_base_p_identity {p n : ℕ} (hp : p.Prime) :
    (p - 1) * padicValNat p (Nat.factorial n) = n - basePDigitSum p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact sub_one_mul_padicValNat_factorial n

/-- `s_p(n) ≤ n`. -/
theorem basePDigitSum_le (p n : ℕ) : basePDigitSum p n ≤ n := by
  unfold basePDigitSum
  rcases lt_or_ge p 2 with hp | hp
  · rcases eq_or_ne p 0 with rfl | hp0
    · rcases eq_or_ne n 0 with rfl | hn0
      · decide
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        simp [Nat.digits_zero_succ]
    · have hp1 : p = 1 := by omega
      subst hp1
      simp [Nat.digits_one]
  · induction n using Nat.strongRecOn with
    | ind m ih =>
      rcases eq_or_ne m 0 with rfl | hm0
      · simp
      · rw [Nat.digits_of_two_le_of_pos hp (Nat.pos_of_ne_zero hm0), List.sum_cons]
        have hlt : m / p < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm0) (by omega)
        have hih := ih (m / p) hlt
        have hdm := Nat.div_add_mod m p
        have h1 : 1 * (m / p) ≤ p * (m / p) := Nat.mul_le_mul_right _ (by omega)
        omega

/-- Eq. (2.6): `∑_{3 ≤ p ≤ √n} (-1)^{v_p(n!)} v_p(n!) log p = -n Σ*_parity(n) + E_digit(n)`. -/
theorem exact_legendre_base_p_reduction (n : ℕ) :
    ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
      (-1 : ℝ) ^ (padicValNat p (Nat.factorial n)) *
        (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) =
      -(n : ℝ) * Sigma_star_parity n + E_digit n := by
  unfold Sigma_star_parity E_digit
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hp_pos : (p : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    linarith
  have hleg := legendre_base_p_identity (n := n) hprime
  have hsle : basePDigitSum p n ≤ n := basePDigitSum_le p n
  have hlegR : ((p : ℝ) - 1) * (padicValNat p (Nat.factorial n) : ℝ) =
      (n : ℝ) - (basePDigitSum p n : ℝ) := by
    have h1 : ((p - 1 : ℕ) : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) =
        ((n - basePDigitSum p n : ℕ) : ℝ) := by
      exact_mod_cast hleg
    have hp1 : 1 ≤ p := by omega
    rw [Nat.cast_sub hp1, Nat.cast_sub hsle] at h1
    simpa using h1
  have hv_pos : 1 ≤ padicValNat p (Nat.factorial n) := by
    have hle_n : p ≤ n := by
      have hsq : p ≤ Nat.sqrt n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      exact le_trans hsq (Nat.sqrt_le_self n)
    have hdvd : p ∣ Nat.factorial n := hprime.dvd_factorial.mpr hle_n
    haveI : Fact p.Prime := ⟨hprime⟩
    exact one_le_padicValNat_of_dvd (Nat.factorial_ne_zero n) hdvd
  have hpow : (-1 : ℝ) ^ (padicValNat p (Nat.factorial n)) =
      -((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) := by
    have hne : padicValNat p (Nat.factorial n) = (padicValNat p (Nat.factorial n) - 1) + 1 := by
      omega
    conv_lhs => rw [hne, pow_succ]
    ring
  have hv_eq : (padicValNat p (Nat.factorial n) : ℝ) =
      ((n : ℝ) - (basePDigitSum p n : ℝ)) / ((p : ℝ) - 1) := by
    field_simp [hp_pos]
    linarith [hlegR]
  rw [hpow, hv_eq]
  ring

private theorem list_sum_le_length_mul {l : List ℕ} {M : ℕ} (h : ∀ d ∈ l, d ≤ M) :
    l.sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.sum_cons, List.length_cons]
    have ha : a ≤ M := h a (by simp)
    have ht : t.sum ≤ t.length * M := ih (fun d hd => h d (by simp [hd]))
    nlinarith

/-- Upper bound on `s_p(n) / (p - 1)` for `p ≥ 2`: `s_p(n) / (p - 1) ≤ (Nat.digits p n).length`. -/
theorem basePDigitSum_div_sub_one_le {p n : ℕ} (hp : 2 ≤ p) :
    (basePDigitSum p n : ℝ) / ((p : ℝ) - 1) ≤ ((Nat.digits p n).length : ℝ) := by
  unfold basePDigitSum
  have hp_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  rw [div_le_iff₀ hp_pos]
  have hsum : (Nat.digits p n).sum ≤ (Nat.digits p n).length * (p - 1) := by
    apply list_sum_le_length_mul
    intro d hd
    have hlt : d < p := Nat.digits_lt_base hp hd
    omega
  have hsumR : ((Nat.digits p n).sum : ℝ) ≤ ((Nat.digits p n).length : ℝ) * ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have hp1 : 1 ≤ p := by omega
  rw [Nat.cast_sub hp1] at hsumR
  simpa using hsumR

/-- Bound on `(Nat.digits p n).length`: for `p ≥ 2` and `n ≥ 1`,
`((Nat.digits p n).length : ℝ) ≤ Real.log n / Real.log p + 1`. -/
theorem digits_length_le_log {p n : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) :
    ((Nat.digits p n).length : ℝ) ≤ Real.log (n : ℝ) / Real.log (p : ℝ) + 1 := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  induction n using Nat.strongRecOn with
  | ind m ih =>
    rcases lt_or_ge m p with hlt | hge
    · have hdig : Nat.digits p m = [m] := by
        rw [Nat.digits_of_two_le_of_pos hp (by omega),
          Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
        simp
      rw [hdig, List.length_singleton, Nat.cast_one]
      have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
      have hdiv : 0 ≤ Real.log (m : ℝ) / Real.log (p : ℝ) := div_nonneg hlogm hlogp.le
      linarith
    · rw [Nat.digits_of_two_le_of_pos hp (by omega), List.length_cons, Nat.cast_add, Nat.cast_one]
      have hdiv_pos : 1 ≤ m / p := Nat.div_pos hge (by omega)
      have hdiv_lt : m / p < m := Nat.div_lt_self (by omega) (by omega)
      have hih := ih (m / p) hdiv_lt hdiv_pos
      have hm_ge : (p : ℝ) * ((m / p : ℕ) : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.mul_div_le m p
      have hlog_div : Real.log ((m / p : ℕ) : ℝ) ≤ Real.log (m : ℝ) - Real.log (p : ℝ) := by
        have h1 : Real.log ((p : ℝ) * ((m / p : ℕ) : ℝ)) ≤ Real.log (m : ℝ) :=
          Real.log_le_log (by positivity) hm_ge
        rw [Real.log_mul (by positivity) (by positivity)] at h1
        linarith
      have hdiv_le : Real.log ((m / p : ℕ) : ℝ) / Real.log (p : ℝ) ≤
          Real.log (m : ℝ) / Real.log (p : ℝ) - 1 := by
        calc Real.log ((m / p : ℕ) : ℝ) / Real.log (p : ℝ)
            ≤ (Real.log (m : ℝ) - Real.log (p : ℝ)) / Real.log (p : ℝ) :=
              div_le_div_of_nonneg_right hlog_div hlogp.le
          _ = Real.log (m : ℝ) / Real.log (p : ℝ) - 1 := by
              field_simp [hlogp.ne']
      linarith

/-- Eq. (2.7) explicit bound: `|E_digit(n)| ≤ 2 * π(√n) * log n` for `n ≥ 4`. -/
theorem E_digit_le_two_pi_sqrt_mul_log {n : ℕ} (hn : 4 ≤ n) :
    |E_digit n| ≤ 2 * piPrime (Real.sqrt (n : ℝ)) * Real.log (n : ℝ) := by
  unfold E_digit piPrime
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hsub : (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime ⊆
      (Finset.Icc 2 (Nat.floor (Real.sqrt (n : ℝ)))).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    refine ⟨⟨by omega, ?_⟩, hp.2⟩
    have hsq : Nat.sqrt n = Nat.floor (Real.sqrt (n : ℝ)) := by
      symm
      rw [Nat.floor_eq_iff (Real.sqrt_nonneg _)]
      constructor
      · rw [Real.le_sqrt (by positivity) (by positivity)]
        exact_mod_cast Nat.sqrt_le' n
      · rw [Real.sqrt_lt' (by positivity)]
        exact_mod_cast Nat.lt_succ_sqrt' n
    omega
  have hterm : ∀ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
      |((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) *
        (((basePDigitSum p n : ℝ) * Real.log (p : ℝ)) / ((p : ℝ) - 1))| ≤ 2 * Real.log (n : ℝ) := by
    intro p hp
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
    have hp_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    have hp3 : 3 ≤ p := hp_icc.1
    have hp2 : 2 ≤ p := by omega
    have hpsq : p ≤ Nat.sqrt n := hp_icc.2
    have hp_le_sqrt : (p : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      exact_mod_cast le_trans (Nat.pow_le_pow_left hpsq 2) (Nat.sqrt_le' n)
    have hlogp_pos : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
    have hlogp_gt : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
    have hlogp_le : Real.log (p : ℝ) ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) := by
      calc Real.log (p : ℝ) ≤ Real.log (Real.sqrt (n : ℝ)) := Real.log_le_log (by positivity) hp_le_sqrt
      _ = (1 / 2 : ℝ) * Real.log (n : ℝ) := by rw [Real.log_sqrt (by positivity)]; ring
    have hp_sub_pos : 0 ≤ (p : ℝ) - 1 := by
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      linarith
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (by positivity)]
    calc ((basePDigitSum p n : ℝ) * Real.log (p : ℝ)) / ((p : ℝ) - 1)
        = ((basePDigitSum p n : ℝ) / ((p : ℝ) - 1)) * Real.log (p : ℝ) := by ring
      _ ≤ ((Nat.digits p n).length : ℝ) * Real.log (p : ℝ) :=
          mul_le_mul_of_nonneg_right (basePDigitSum_div_sub_one_le hp2) hlogp_pos
      _ ≤ (Real.log (n : ℝ) / Real.log (p : ℝ) + 1) * Real.log (p : ℝ) :=
          mul_le_mul_of_nonneg_right (digits_length_le_log hp2 (by omega)) hlogp_pos
      _ = Real.log (n : ℝ) + Real.log (p : ℝ) := by field_simp [hlogp_gt.ne']
      _ ≤ Real.log (n : ℝ) + (1 / 2 : ℝ) * Real.log (n : ℝ) := add_le_add le_rfl hlogp_le
      _ ≤ 2 * Real.log (n : ℝ) := by linarith
  calc |∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
        ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) *
          (((basePDigitSum p n : ℝ) * Real.log (p : ℝ)) / ((p : ℝ) - 1))|
      ≤ ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
          |((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) *
            (((basePDigitSum p n : ℝ) * Real.log (p : ℝ)) / ((p : ℝ) - 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime, 2 * Real.log (n : ℝ) :=
        Finset.sum_le_sum hterm
    _ = (((Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime).card : ℝ) * (2 * Real.log (n : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((Finset.Icc 2 (Nat.floor (Real.sqrt (n : ℝ)))).filter Nat.Prime).card : ℝ) *
          (2 * Real.log (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Finset.card_le_card hsub
    _ = 2 * (((Finset.Icc 2 (Nat.floor (Real.sqrt (n : ℝ)))).filter Nat.Prime).card : ℝ) *
          Real.log (n : ℝ) := by ring

/-- Eq. (2.7) asymptotic bound: `E_digit(n) = O(√n)`. -/
theorem E_digit_isBigO_sqrt :
    E_digit =O[atTop] (fun n : ℕ => Real.sqrt (n : ℝ)) := by
  obtain ⟨C, hC_pos, hC⟩ := chebyshev_pi_upper
  refine Asymptotics.IsBigO.of_bound (4 * C) ?_
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  have hsqrt2 : (2 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    norm_num
    exact_mod_cast hn
  have hpi := hC (Real.sqrt (n : ℝ)) hsqrt2
  have hlog_sqrt : Real.log (Real.sqrt (n : ℝ)) = (1 / 2 : ℝ) * Real.log (n : ℝ) := by
    rw [Real.log_sqrt (by positivity)]; ring
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlog_sqrt_pos : 0 < Real.log (Real.sqrt (n : ℝ)) := by rw [hlog_sqrt]; positivity
  have hle := E_digit_le_two_pi_sqrt_mul_log hn
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc |E_digit n|
      ≤ 2 * piPrime (Real.sqrt (n : ℝ)) * Real.log (n : ℝ) := hle
    _ ≤ 2 * (C * (Real.sqrt (n : ℝ) / Real.log (Real.sqrt (n : ℝ)))) * Real.log (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hpi (by positivity)
        · exact hlogn_pos.le
    _ = 4 * C * Real.sqrt (n : ℝ) := by
        rw [hlog_sqrt]
        field_simp [hlogn_pos.ne']
        ring

end GrasGreenbergBrocard
