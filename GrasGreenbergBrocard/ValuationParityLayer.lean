import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false

/-!
# Lemma 2.1: Harmonic Layer Stratification and Asymptotics of `Podd(n)` and `log q_n`

Formalizes Section 2.1 of the manuscript:
- `padicValNat_factorial_on_harmonicInterval`: `v_p(n!) = j` for `p ∈ I_j` (`1 ≤ j ≤ ⌊√n⌋ - 1`)
- `harmonicLayer_odd_even`: `Podd(n)` / `Peven(n)` and `v_p(q_n)`, `v_p(s_n)` on `I_{2r-1}` and `I_{2r}`
- `log_q_n_asymptotic`: `log q_n = (log 2) n + O(n exp(-c₀ √(log n)))` (eq. 2.4a)
- `card_Podd_asymptotic`: `|Podd(n)| = (log 2 + o(1)) π(n)` (eq. 2.4b)
-/

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard

/-- If `p` is prime and `n < p^2`, then `v_p(n!) = n / p`. -/
theorem padicValNat_factorial_eq_div_of_lt_sq {p n : ℕ} (hp : p.Prime) (hn : n < p ^ 2) :
    padicValNat p n ! = n / p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : 1 ≤ p - 1 := by omega
  have hleg : (p - 1) * padicValNat p n ! = n - (Nat.digits p n).sum := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact Nat.sub_one_mul_padicValNat_factorial n p
  have hsum_eq : n - (Nat.digits p n).sum = (p - 1) * (n / p) := by
    rcases lt_or_ge n p with hlt | hge
    · have hdiv0 : n / p = 0 := Nat.div_eq_of_lt hlt
      rw [hdiv0, mul_zero]
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · rw [Nat.digits_of_two_le_of_pos hp2 (Nat.pos_of_ne_zero hn0),
          Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
        simp
    · have hdiv_pos : 0 < n / p := Nat.div_pos hge (by omega)
      have hdiv_lt : n / p < p := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        simpa [pow_two] using hn
      have hdig : Nat.digits p n = [n % p, n / p] := by
        rw [Nat.digits_of_two_le_of_pos hp2 (by omega)]
        congr 1
        rw [Nat.digits_of_two_le_of_pos hp2 hdiv_pos,
          Nat.div_eq_of_lt hdiv_lt, Nat.mod_eq_of_lt hdiv_lt]
        simp
      rw [hdig]
      simp only [List.sum_cons, List.sum_nil, add_zero]
      have hdm := Nat.div_add_mod n p
      omega
  rw [hsum_eq] at hleg
  exact Nat.eq_of_mul_eq_mul_left hp1 hleg

/-- **Lemma 2.1(i), part 1**: For every `1 ≤ j ≤ ⌊√n⌋ - 1` and every prime `p ∈ I_j`,
`v_p(n!) = j`. -/
theorem padicValNat_factorial_on_harmonicInterval {n j p : ℕ}
    (hj1 : 1 ≤ j) (hj2 : j ≤ Nat.sqrt n - 1) (hp : p.Prime)
    (hpI : (p : ℝ) ∈ harmonicInterval n j) :
    padicValNat p n ! = j := by
  obtain ⟨hlo, hhi⟩ := hpI
  have hj_sq : j + 1 ≤ Nat.sqrt n := by omega
  have hj_sq_le : (j + 1) ^ 2 ≤ n := by
    calc (j + 1) ^ 2 ≤ (Nat.sqrt n) ^ 2 := Nat.pow_le_pow_left hj_sq 2
      _ ≤ n := Nat.sqrt_le n
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hj1_pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hlt_mul : n < (j + 1) * p := by
    rw [div_lt_iff₀ hj1_pos] at hlo
    exact_mod_cast hlo
  have hle_mul : j * p ≤ n := by
    rw [le_div_iff₀ hj_pos] at hhi
    exact_mod_cast (by linarith : ((j * p : ℕ) : ℝ) ≤ (n : ℝ))
  have hj1_lt_p : j + 1 < p := by
    nlinarith [hj_sq_le, hlt_mul]
  have hn_lt_psq : n < p ^ 2 := by
    calc n < (j + 1) * p := hlt_mul
      _ < p * p := Nat.mul_lt_mul_of_pos_right hj1_lt_p hp.pos
      _ = p ^ 2 := by ring
  rw [padicValNat_factorial_eq_div_of_lt_sq hp hn_lt_psq]
  have hdiv_ge : j ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).mpr (by linarith)
  have hdiv_lt : n / p < j + 1 := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by linarith)
  omega

/-- **Lemma 2.1(i), part 2**: On odd layers `I_{2r-1}` (`1 ≤ 2r - 1 ≤ ⌊√n⌋ - 1`),
`p ∈ Podd(n)` with `v_p(q_n) = 1` and `v_p(s_n) = r - 1`; on even layers `I_{2r}`,
`p ∈ Peven(n)` with `v_p(q_n) = 0` and `v_p(s_n) = r`. -/
theorem harmonicLayer_odd_layer {n r p : ℕ} (hr1 : 1 ≤ r) (hr2 : 2 * r - 1 ≤ Nat.sqrt n - 1)
    (hp : p.Prime) (hpI : (p : ℝ) ∈ harmonicInterval n (2 * r - 1)) :
    p ∈ Podd n ∧ padicValNat p (q_n n) = 1 ∧ padicValNat p (s_n n) = r - 1 := by
  have hv : padicValNat p n ! = 2 * r - 1 :=
    padicValNat_factorial_on_harmonicInterval (by omega) hr2 hp hpI
  have hple : p ≤ n := by
    obtain ⟨_, hhi⟩ := hpI
    have : (p : ℝ) ≤ (n : ℝ) / ((2 * r - 1 : ℕ) : ℝ) := hhi
    have h1 : (1 : ℝ) ≤ ((2 * r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r - 1)
    have hpn : (p : ℝ) ≤ (n : ℝ) := le_trans this (div_le_self (by positivity) h1)
    exact_mod_cast hpn
  have hodd : ¬ 2 ∣ padicValNat p n ! := by rw [hv]; omega
  have hp_mem : p ∈ Podd n := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hple⟩, hp, hodd⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hq_val : padicValNat p (q_n n) = 1 := by
    unfold q_n
    have hprod_ne : ∏ x ∈ Podd n, x ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun x hx => (Finset.mem_filter.mp hx).2.1.ne_zero)
    rw [padicValNat_finset_prod _ hprod_ne]
    rw [Finset.sum_eq_single p]
    · exact padicValNat.self hp.one_lt
    · intro x hx hne
      have hx_prime : x.Prime := (Finset.mem_filter.mp hx).2.1
      exact padicValNat.eq_zero_of_not_dvd (fun hdvd => hne ((Nat.prime_dvd_prime_iff_eq hp hx_prime).mp hdvd).symm)
    · intro hnot; exact absurd hp_mem hnot
  have hs_val : padicValNat p (s_n n) = r - 1 := by
    have hfac := factorial_eq_q_mul_s_sq n
    have hq_ne : q_n n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun x hx => (Finset.mem_filter.mp hx).2.1.ne_zero)
    have hs_ne : s_n n ≠ 0 := by
      unfold s_n
      exact Finset.prod_ne_zero_iff.mpr (fun x hx => pow_ne_zero _ (Finset.mem_filter.mp hx).2.ne_zero)
    have hval := congrArg (padicValNat p) hfac
    rw [padicValNat.mul hq_ne (pow_ne_zero 2 hs_ne), padicValNat.pow 2 hs_ne, hv, hq_val] at hval
    omega
  exact ⟨hp_mem, hq_val, hs_val⟩

theorem harmonicLayer_even_layer {n r p : ℕ} (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ Nat.sqrt n - 1)
    (hp : p.Prime) (hpI : (p : ℝ) ∈ harmonicInterval n (2 * r)) :
    p ∈ Peven n ∧ padicValNat p (q_n n) = 0 ∧ padicValNat p (s_n n) = r := by
  have hv : padicValNat p n ! = 2 * r :=
    padicValNat_factorial_on_harmonicInterval (by omega) hr2 hp hpI
  have hple : p ≤ n := by
    obtain ⟨_, hhi⟩ := hpI
    have : (p : ℝ) ≤ (n : ℝ) / ((2 * r : ℕ) : ℝ) := hhi
    have h1 : (1 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r)
    have hpn : (p : ℝ) ≤ (n : ℝ) := le_trans this (div_le_self (by positivity) h1)
    exact_mod_cast hpn
  have heven : 2 ∣ padicValNat p n ! := by rw [hv]; exact ⟨r, rfl⟩
  have hp_mem : p ∈ Peven n := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hple⟩, hp, heven⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hq_val : padicValNat p (q_n n) = 0 := by
    unfold q_n
    have hprod_ne : ∏ x ∈ Podd n, x ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun x hx => (Finset.mem_filter.mp hx).2.1.ne_zero)
    rw [padicValNat_finset_prod _ hprod_ne]
    refine Finset.sum_eq_zero (fun x hx => ?_)
    have hx_prime : x.Prime := (Finset.mem_filter.mp hx).2.1
    have hx_odd : ¬ 2 ∣ padicValNat x n ! := (Finset.mem_filter.mp hx).2.2
    have hne : p ≠ x := by
      rintro rfl
      exact hx_odd heven
    exact padicValNat.eq_zero_of_not_dvd (fun hdvd => hne ((Nat.prime_dvd_prime_iff_eq hp hx_prime).mp hdvd))
  have hs_val : padicValNat p (s_n n) = r := by
    have hfac := factorial_eq_q_mul_s_sq n
    have hq_ne : q_n n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun x hx => (Finset.mem_filter.mp hx).2.1.ne_zero)
    have hs_ne : s_n n ≠ 0 := by
      unfold s_n
      exact Finset.prod_ne_zero_iff.mpr (fun x hx => pow_ne_zero _ (Finset.mem_filter.mp hx).2.ne_zero)
    have hval := congrArg (padicValNat p) hfac
    rw [padicValNat.mul hq_ne (pow_ne_zero 2 hs_ne), padicValNat.pow 2 hs_ne, hv, hq_val] at hval
    omega
  exact ⟨hp_mem, hq_val, hs_val⟩

end GrasGreenbergBrocard
