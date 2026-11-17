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
- `harmonicLayer_odd_layer`, `harmonicLayer_even_layer`
- `alt_harmonic_sum_diff_log_two`: `|∑_{r=1}^N (1/(2r-1) - 1/(2r)) - log 2| ≤ 1 / (2N)`
- `log_q_n_asymptotic`: `log q_n = (log 2) n + O(n exp(-c₀ √(log n)))` (eq. 2.4a)
- `card_Podd_asymptotic`: `|Podd(n)| = (log 2 + o(1)) π(n)` (eq. 2.4b)
-/

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard

/-- If `p` is prime and `n < p^2`, then `v_p(n!) = n / p`. -/
theorem padicValNat_factorial_eq_div_of_lt_sq {p n : ℕ} (hp : p.Prime) (hn : n < p ^ 2) :
    padicValNat p (Nat.factorial n) = n / p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : 1 ≤ p - 1 := by omega
  have hleg : (p - 1) * padicValNat p (Nat.factorial n) = n - (Nat.digits p n).sum := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact sub_one_mul_padicValNat_factorial n
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
      have hdm : p * (n / p) + n % p = n := Nat.div_add_mod n p
      have hle1 : n % p + n / p ≤ n := by
        have : 1 * (n / p) ≤ p * (n / p) := Nat.mul_le_mul_right _ (by omega)
        omega
      zify [hle1, (by omega : 1 ≤ p)]
      have hdmZ : (p : ℤ) * ((n / p : ℕ) : ℤ) + ((n % p : ℕ) : ℤ) = (n : ℤ) := by exact_mod_cast hdm
      linarith
  rw [hsum_eq] at hleg
  exact Nat.eq_of_mul_eq_mul_left hp1 hleg

/-- **Lemma 2.1(i), part 1**: For every `1 ≤ j ≤ ⌊√n⌋ - 1` and every prime `p ∈ I_j`,
`v_p(n!) = j`. -/
theorem padicValNat_factorial_on_harmonicInterval {n j p : ℕ}
    (hj1 : 1 ≤ j) (hj2 : j ≤ Nat.sqrt n - 1) (hp : p.Prime)
    (hpI : (p : ℝ) ∈ harmonicInterval n j) :
    padicValNat p (Nat.factorial n) = j := by
  obtain ⟨hlo, hhi⟩ := hpI
  have hj_sq : j + 1 ≤ Nat.sqrt n := by omega
  have hj_sq_le : (j + 1) ^ 2 ≤ n := by
    calc (j + 1) ^ 2 ≤ (Nat.sqrt n) ^ 2 := Nat.pow_le_pow_left hj_sq 2
      _ ≤ n := Nat.sqrt_le' n
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hj1_pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hlt_mul : n < (j + 1) * p := by
    rw [div_lt_iff₀ hj1_pos] at hlo
    have hcast : (n : ℝ) < ((j + 1 : ℕ) : ℝ) * (p : ℝ) := by
      push_cast; linarith
    exact_mod_cast hcast
  have hle_mul : j * p ≤ n := by
    rw [le_div_iff₀ hj_pos] at hhi
    exact_mod_cast (by linarith : ((j : ℝ) * (p : ℝ)) ≤ (n : ℝ))
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
`p ∈ Podd(n)` with `v_p(q_n) = 1` and `v_p(s_n) = r - 1`. -/
theorem harmonicLayer_odd_layer {n r p : ℕ} (hr1 : 1 ≤ r) (hr2 : 2 * r - 1 ≤ Nat.sqrt n - 1)
    (hp : p.Prime) (hpI : (p : ℝ) ∈ harmonicInterval n (2 * r - 1)) :
    p ∈ Podd n ∧ padicValNat p (q_n n) = 1 ∧ padicValNat p (s_n n) = r - 1 := by
  have hv : padicValNat p (Nat.factorial n) = 2 * r - 1 :=
    padicValNat_factorial_on_harmonicInterval (by omega) hr2 hp hpI
  have hple : p ≤ n := by
    obtain ⟨_, hhi⟩ := hpI
    have : (p : ℝ) ≤ (n : ℝ) / ((2 * r - 1 : ℕ) : ℝ) := hhi
    have h1 : (1 : ℝ) ≤ ((2 * r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r - 1)
    have hpn : (p : ℝ) ≤ (n : ℝ) := le_trans this (div_le_self (by positivity) h1)
    exact_mod_cast hpn
  have hodd : ¬ 2 ∣ padicValNat p (Nat.factorial n) := by rw [hv]; omega
  have hp_mem : p ∈ Podd n := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hple⟩, hp, hodd⟩
  have hq_ne : q_n n ≠ 0 := by
    unfold q_n Podd
    exact Finset.prod_ne_zero_iff.mpr (fun x hx => (Finset.mem_filter.mp hx).2.1.ne_zero)
  have hs_ne : s_n n ≠ 0 := by
    unfold s_n
    exact Finset.prod_ne_zero_iff.mpr (fun x hx => pow_ne_zero _ (Finset.mem_filter.mp hx).2.ne_zero)
  have hq_val : padicValNat p (q_n n) = 1 := by
    rw [← Nat.factorization_def (q_n n) hp]
    unfold q_n
    rw [Nat.factorization_prod (fun x hx => (Finset.mem_filter.mp hx).2.1.ne_zero)]
    simp only [Finset.sum_apply']
    rw [Finset.sum_eq_single p]
    · exact hp.factorization_self
    · intro x hx hne
      have hx_prime : x.Prime := (Finset.mem_filter.mp hx).2.1
      exact Nat.factorization_eq_zero_of_not_dvd
        (fun hdvd => hne ((Nat.prime_dvd_prime_iff_eq hp hx_prime).mp hdvd).symm)
    · intro hnot; exact absurd hp_mem hnot
  have hs_val : padicValNat p (s_n n) = r - 1 := by
    have hfac := factorial_eq_q_mul_s_sq n
    have hfv : (Nat.factorial n).factorization p = padicValNat p (Nat.factorial n) :=
      Nat.factorization_def _ hp
    have hfq : (q_n n).factorization p = padicValNat p (q_n n) := Nat.factorization_def _ hp
    have hfs : (s_n n).factorization p = padicValNat p (s_n n) := Nat.factorization_def _ hp
    have hval := congrArg (fun m : ℕ => m.factorization p) hfac
    rw [Nat.factorization_mul hq_ne (pow_ne_zero 2 hs_ne), Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      hfv, hfq, hfs, hv, hq_val] at hval
    omega
  exact ⟨hp_mem, hq_val, hs_val⟩

theorem harmonicLayer_even_layer {n r p : ℕ} (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ Nat.sqrt n - 1)
    (hp : p.Prime) (hpI : (p : ℝ) ∈ harmonicInterval n (2 * r)) :
    p ∈ Peven n ∧ padicValNat p (q_n n) = 0 ∧ padicValNat p (s_n n) = r := by
  have hv : padicValNat p (Nat.factorial n) = 2 * r :=
    padicValNat_factorial_on_harmonicInterval (by omega) hr2 hp hpI
  have hple : p ≤ n := by
    obtain ⟨_, hhi⟩ := hpI
    have : (p : ℝ) ≤ (n : ℝ) / ((2 * r : ℕ) : ℝ) := hhi
    have h1 : (1 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r)
    have hpn : (p : ℝ) ≤ (n : ℝ) := le_trans this (div_le_self (by positivity) h1)
    exact_mod_cast hpn
  have heven : 2 ∣ padicValNat p (Nat.factorial n) := by rw [hv]; exact ⟨r, rfl⟩
  have hp_mem : p ∈ Peven n := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hple⟩, hp, heven⟩
  have hq_ne : q_n n ≠ 0 := by
    unfold q_n Podd
    exact Finset.prod_ne_zero_iff.mpr (fun x hx => (Finset.mem_filter.mp hx).2.1.ne_zero)
  have hs_ne : s_n n ≠ 0 := by
    unfold s_n
    exact Finset.prod_ne_zero_iff.mpr (fun x hx => pow_ne_zero _ (Finset.mem_filter.mp hx).2.ne_zero)
  have hq_val : padicValNat p (q_n n) = 0 := by
    rw [← Nat.factorization_def (q_n n) hp]
    unfold q_n
    rw [Nat.factorization_prod (fun x hx => (Finset.mem_filter.mp hx).2.1.ne_zero)]
    simp only [Finset.sum_apply']
    refine Finset.sum_eq_zero (fun x hx => ?_)
    have hx_prime : x.Prime := (Finset.mem_filter.mp hx).2.1
    have hx_odd : ¬ 2 ∣ padicValNat x (Nat.factorial n) := (Finset.mem_filter.mp hx).2.2
    have hne : p ≠ x := by
      rintro rfl
      exact hx_odd heven
    exact Nat.factorization_eq_zero_of_not_dvd
      (fun hdvd => hne ((Nat.prime_dvd_prime_iff_eq hp hx_prime).mp hdvd))
  have hs_val : padicValNat p (s_n n) = r := by
    have hfac := factorial_eq_q_mul_s_sq n
    have hfv : (Nat.factorial n).factorization p = padicValNat p (Nat.factorial n) :=
      Nat.factorization_def _ hp
    have hfq : (q_n n).factorization p = padicValNat p (q_n n) := Nat.factorization_def _ hp
    have hfs : (s_n n).factorization p = padicValNat p (s_n n) := Nat.factorization_def _ hp
    have hval := congrArg (fun m : ℕ => m.factorization p) hfac
    rw [Nat.factorization_mul hq_ne (pow_ne_zero 2 hs_ne), Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      hfv, hfq, hfs, hv, hq_val] at hval
    omega
  exact ⟨hp_mem, hq_val, hs_val⟩

/-- Elementary identity: `∑_{r=1}^N (1/(2r-1) - 1/(2r)) = ∑_{k=N+1}^{2N} 1/k`. -/
theorem alt_harmonic_eq_tail_harmonic (N : ℕ) :
    ∑ r ∈ Finset.Icc 1 N, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) =
      ∑ k ∈ Finset.Icc (N + 1) (2 * N), (1 : ℝ) / (k : ℝ) := by
  induction N with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
    have h_lhs_rhs :
        ∑ k ∈ Finset.Icc (m + 2) (2 * (m + 1)), (1 : ℝ) / (k : ℝ) =
        (∑ k ∈ Finset.Icc (m + 1) (2 * m), (1 : ℝ) / (k : ℝ)) -
          (1 : ℝ) / ((m + 1 : ℕ) : ℝ) +
          (1 : ℝ) / ((2 * m + 1 : ℕ) : ℝ) +
          (1 : ℝ) / ((2 * m + 2 : ℕ) : ℝ) := by
      have h1 : Finset.Icc (m + 1) (2 * m + 2) =
          insert (m + 1) (Finset.Icc (m + 2) (2 * m + 2)) := by
        ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have h2 : Finset.Icc (m + 1) (2 * m + 2) =
          insert (2 * m + 2) (insert (2 * m + 1) (Finset.Icc (m + 1) (2 * m))) := by
        ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have hm1 : m + 1 ∉ Finset.Icc (m + 2) (2 * m + 2) := by simp
      have hm21 : 2 * m + 1 ∉ Finset.Icc (m + 1) (2 * m) := by simp
      have hm22 : 2 * m + 2 ∉ insert (2 * m + 1) (Finset.Icc (m + 1) (2 * m)) := by
        simp; omega
      have hs1 := congrArg (Finset.sum · (fun k : ℕ => (1 : ℝ) / (k : ℝ))) h1
      have hs2 := congrArg (Finset.sum · (fun k : ℕ => (1 : ℝ) / (k : ℝ))) h2
      rw [Finset.sum_insert hm1] at hs1
      rw [Finset.sum_insert hm22, Finset.sum_insert hm21] at hs2
      rw [show 2 * (m + 1) = 2 * m + 2 from by omega]
      linarith
    rw [h_lhs_rhs]
    push_cast
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    have hm2 : 2 * ((m : ℝ) + 1) - 1 ≠ 0 := by positivity
    have hm3 : 2 * ((m : ℝ) + 1) ≠ 0 := by positivity
    have hm21 : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
    have hm22 : 2 * (m : ℝ) + 2 ≠ 0 := by positivity
    field_simp [hm1, hm2, hm3, hm21, hm22]
    try ring

/-- Quantitative alternating harmonic bound: `|∑_{r=1}^N (1/(2r-1) - 1/(2r)) - log 2| ≤ 1 / (2N)`. -/
theorem alt_harmonic_sum_diff_log_two {N : ℕ} (hN : 1 ≤ N) :
    |∑ r ∈ Finset.Icc 1 N, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2| ≤
      1 / (2 * (N : ℝ)) := by
  rw [alt_harmonic_eq_tail_harmonic]
  have htel : ∑ k ∈ Finset.Icc N (2 * N - 1), (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) = Real.log 2 := by
    have htel_gen : ∀ (a b : ℕ), a ≤ b →
        ∑ k ∈ Finset.Ico a b, (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) =
          Real.log (b : ℝ) - Real.log (a : ℝ) := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => simp
      | succ k hk ihk =>
        rw [Finset.sum_Ico_succ_top hk, ihk]
        ring
    have hcon := htel_gen N (2 * N) (by omega)
    have hicc : Finset.Icc N (2 * N - 1) = Finset.Ico N (2 * N) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hicc]
    have hsum_eq : ∑ k ∈ Finset.Ico N (2 * N), (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) =
        ∑ k ∈ Finset.Ico N (2 * N), (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) := by
      refine Finset.sum_congr rfl (fun k _ => by push_cast; rfl)
    rw [hsum_eq, hcon]
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hN_pos.ne']
    ring
  have hlo : ∑ k ∈ Finset.Icc (N + 1) (2 * N), (1 : ℝ) / (k : ℝ) ≤ Real.log 2 := by
    rw [← htel]
    have hshift : ∑ k ∈ Finset.Icc (N + 1) (2 * N), (1 : ℝ) / (k : ℝ) =
        ∑ k ∈ Finset.Icc N (2 * N - 1), (1 : ℝ) / ((k : ℝ) + 1) := by
      refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
      · intro k1 hk1 k2 hk2 heq; simp only [Finset.mem_Icc] at hk1 hk2; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk
        refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk; simp only [Finset.mem_Icc] at hk
        have : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ k)]; push_cast; ring
        rw [this]
    rw [hshift]
    refine Finset.sum_le_sum (fun k hk => ?_)
    have hk1 : 1 ≤ k := le_trans hN (Finset.mem_Icc.mp hk).1
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have h1 : Real.log ((k : ℝ) / ((k : ℝ) + 1)) ≤ (k : ℝ) / ((k : ℝ) + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h1
    have h2 : (k : ℝ) / ((k : ℝ) + 1) - 1 = -(1 / ((k : ℝ) + 1)) := by field_simp; ring
    linarith
  have hhi : Real.log 2 ≤ ∑ k ∈ Finset.Icc (N + 1) (2 * N), (1 : ℝ) / (k : ℝ) + 1 / (2 * (N : ℝ)) := by
    rw [← htel]
    have hsum_le : ∑ k ∈ Finset.Icc N (2 * N - 1), (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) ≤
        ∑ k ∈ Finset.Icc N (2 * N - 1), (1 : ℝ) / (k : ℝ) := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      have hk1 : 1 ≤ k := le_trans hN (Finset.mem_Icc.mp hk).1
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      have h1 : Real.log (((k : ℝ) + 1) / (k : ℝ)) ≤ ((k : ℝ) + 1) / (k : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h1
      have heq : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by field_simp [hk_pos.ne']; ring
      linarith
    have hdiff_eq : ∑ k ∈ Finset.Icc N (2 * N - 1), (1 : ℝ) / (k : ℝ) =
        ∑ k ∈ Finset.Icc (N + 1) (2 * N), (1 : ℝ) / (k : ℝ) + (1 / (N : ℝ) - 1 / (2 * (N : ℝ))) := by
      have h1 : Finset.Icc N (2 * N) = insert N (Finset.Icc (N + 1) (2 * N)) := by
        ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have h2 : Finset.Icc N (2 * N) = insert (2 * N) (Finset.Icc N (2 * N - 1)) := by
        ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      have hn1 : N ∉ Finset.Icc (N + 1) (2 * N) := by simp
      have hn2 : 2 * N ∉ Finset.Icc N (2 * N - 1) := by simp; omega
      have hs1 := congrArg (Finset.sum · (fun k : ℕ => (1 : ℝ) / (k : ℝ))) h1
      have hs2 := congrArg (Finset.sum · (fun k : ℕ => (1 : ℝ) / (k : ℝ))) h2
      rw [Finset.sum_insert hn1] at hs1
      rw [Finset.sum_insert hn2] at hs2
      push_cast at hs2
      linarith
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h_half : 1 / (N : ℝ) - 1 / (2 * (N : ℝ)) = 1 / (2 * (N : ℝ)) := by
      field_simp [hN_pos.ne']; ring
    linarith
  rw [abs_le]
  constructor <;> linarith

private theorem harmonic_sum_le_log_add_one_aux {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ≤ Real.log (N : ℝ) + 1 := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hlog : (1 : ℝ) / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) := by
      have h1 : Real.log ((m : ℝ) / ((m : ℝ) + 1)) ≤ (m : ℝ) / ((m : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h1
      have h2 : (m : ℝ) / ((m : ℝ) + 1) - 1 = -(1 / ((m : ℝ) + 1)) := by field_simp; ring
      linarith
    push_cast
    linarith

theorem thetaPrime_nonneg (x : ℝ) : 0 ≤ thetaPrime x := by
  unfold thetaPrime
  refine Finset.sum_nonneg (fun p hp => ?_)
  have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))

theorem thetaPrime_mono {x y : ℝ} (hxy : x ≤ y) : thetaPrime x ≤ thetaPrime y := by
  unfold thetaPrime
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p hp _ => ?_)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_mono hxy)⟩, hp.2⟩
  · have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))

theorem thetaPrime_le_linear : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → thetaPrime x ≤ C * x := by
  obtain ⟨c₁, hc₁, hbig⟩ := de_la_vallee_poussin_theta
  obtain ⟨C₁, hC₁⟩ := hbig.bound
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hC₁
  let X₁ := max X₀ 1
  have hX₁_pos : 1 ≤ X₁ := le_max_right _ _
  let C := max (1 + |C₁|) (thetaPrime X₁ + 1)
  refine ⟨C, by positivity, fun x hx => ?_⟩
  rcases le_or_gt X₁ x with hge | hlt
  · have hb := hX₀ x (le_trans (le_max_left _ _) hge)
    have hx_pos : 0 < x := by linarith
    have hexp : Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)] at hb
    have h1 : thetaPrime x ≤ x + C₁ * (x * Real.exp (-c₁ * Real.sqrt (Real.log x))) := by
      linarith [(abs_le.mp hb).2]
    have h2 : C₁ * (x * Real.exp (-c₁ * Real.sqrt (Real.log x))) ≤ |C₁| * x := by
      calc C₁ * (x * Real.exp (-c₁ * Real.sqrt (Real.log x)))
          ≤ |C₁| * (x * Real.exp (-c₁ * Real.sqrt (Real.log x))) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |C₁| * (x * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hx_pos.le) (abs_nonneg _)
        _ = |C₁| * x := by ring
    have hC_ge : 1 + |C₁| ≤ C := le_max_left _ _
    calc thetaPrime x ≤ (1 + |C₁|) * x := by linarith
      _ ≤ C * x := mul_le_mul_of_nonneg_right hC_ge hx_pos.le
  · have hC_ge : thetaPrime X₁ + 1 ≤ C := le_max_right _ _
    calc thetaPrime x ≤ thetaPrime X₁ := thetaPrime_mono hlt.le
      _ ≤ C := by linarith
      _ ≤ C * x := le_mul_of_one_le_right (by positivity) hx

theorem log_q_n_eq_sum_log (n : ℕ) :
    Real.log (q_n n : ℝ) = ∑ p ∈ Podd n, Real.log (p : ℝ) := by
  unfold q_n
  push_cast [Nat.cast_prod]
  exact Real.log_prod (fun p hp => by
    have hprime : p.Prime := (Finset.mem_filter.mp hp).2.1
    exact_mod_cast hprime.ne_zero)

theorem Podd_upper_partition (n K : ℕ) (hn : 4 ≤ n) (hK : 1 ≤ K) (hKsq : 2 * K + 1 ≤ Nat.sqrt n) :
    (∑ p ∈ (Podd n).filter (fun p : ℕ => (n : ℝ) / (2 * (K : ℝ) + 1) < (p : ℝ)), Real.log (p : ℝ) =
      ∑ r ∈ Finset.Icc 1 K,
        (thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - thetaPrime ((n : ℝ) / (2 * (r : ℝ))))) ∧
    ((((Podd n).filter (fun p : ℕ => (n : ℝ) / (2 * (K : ℝ) + 1) < (p : ℝ))).card : ℝ) =
      ∑ r ∈ Finset.Icc 1 K,
        (piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - piPrime ((n : ℝ) / (2 * (r : ℝ))))) := by
  let L : ℕ → Finset ℕ := fun r =>
    ((Finset.Icc 2 (Nat.floor ((n : ℝ) / (2 * (r : ℝ) - 1)))).filter Nat.Prime).filter
      (fun p : ℕ => (n : ℝ) / (2 * (r : ℝ)) < (p : ℝ))
  have hL_part : (Podd n).filter (fun p : ℕ => (n : ℝ) / (2 * (K : ℝ) + 1) < (p : ℝ)) =
      (Finset.Icc 1 K).biUnion L := by
    ext p
    unfold Podd
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Icc, L]
    constructor
    · rintro ⟨⟨hp_icc, hp_prime, hp_odd⟩, hp_gt⟩
      have hK_sq : (2 * K + 1) ^ 2 ≤ n := le_trans (Nat.pow_le_pow_left hKsq 2) (Nat.sqrt_le' n)
      have hn_lt_psq : n < p ^ 2 := by
        have hmul : (n : ℝ) < (p : ℝ) * (2 * (K : ℝ) + 1) := by
          rw [div_lt_iff₀ (by positivity)] at hp_gt; exact hp_gt
        have hmulN : n < p * (2 * K + 1) := by
          exact_mod_cast (by push_cast; exact hmul : (n : ℝ) < ((p * (2 * K + 1) : ℕ) : ℝ))
        have hp_gt_K : 2 * K + 1 < p := by nlinarith
        calc n < p * (2 * K + 1) := hmulN
          _ < p * p := Nat.mul_lt_mul_of_pos_left hp_gt_K hp_prime.pos
          _ = p ^ 2 := by ring
      have hv : padicValNat p (Nat.factorial n) = n / p :=
        padicValNat_factorial_eq_div_of_lt_sq hp_prime hn_lt_psq
      rw [hv] at hp_odd
      have hdiv_ge : 1 ≤ n / p := Nat.div_pos hp_icc.2 hp_prime.pos
      have hdiv_lt : n / p < 2 * K + 1 := by
        rw [Nat.div_lt_iff_lt_mul hp_prime.pos]
        have hmul : (n : ℝ) < (p : ℝ) * (2 * (K : ℝ) + 1) := by
          rw [div_lt_iff₀ (by positivity)] at hp_gt; exact hp_gt
        have hmulN : n < p * (2 * K + 1) := by
          exact_mod_cast (by push_cast; exact hmul : (n : ℝ) < ((p * (2 * K + 1) : ℕ) : ℝ))
        linarith
      let r := (n / p + 1) / 2
      have hr_eq : n / p = 2 * r - 1 := by omega
      have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
      refine ⟨r, ⟨by omega, by omega⟩, ⟨⟨hp_icc.1, ?_⟩, hp_prime⟩, ?_⟩
      · rw [Nat.le_floor_iff (by positivity)]
        rw [le_div_iff₀ (by linarith)]
        have hmul : (2 * r - 1) * p ≤ n := by rw [← hr_eq]; exact Nat.div_mul_le_self n p
        have hmulR : ((2 * r - 1 : ℕ) : ℝ) * (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmul
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)] at hmulR
        push_cast at hmulR; linarith
      · rw [div_lt_iff₀ (by linarith)]
        have hlt : n < (2 * r) * p := by
          have : n / p < 2 * r := by omega
          exact (Nat.div_lt_iff_lt_mul hp_prime.pos).mp this
        have hltR : (n : ℝ) < ((2 * r : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast hlt
        push_cast at hltR; linarith
    · rintro ⟨r, ⟨hr1, hrK⟩, ⟨⟨hp2, hp_hi⟩, hp_prime⟩, hp_lo⟩
      have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
      have hp_gt : (n : ℝ) / (2 * (K : ℝ) + 1) < (p : ℝ) := by
        calc (n : ℝ) / (2 * (K : ℝ) + 1) < (n : ℝ) / (2 * (r : ℝ)) := by
              apply div_lt_div_of_pos_left (by exact_mod_cast (by omega : 0 < n)) (by positivity)
              exact_mod_cast (by omega : 2 * r < 2 * K + 1)
          _ < (p : ℝ) := hp_lo
      have hK_sq : (2 * K + 1) ^ 2 ≤ n := le_trans (Nat.pow_le_pow_left hKsq 2) (Nat.sqrt_le' n)
      have hn_lt_psq : n < p ^ 2 := by
        have hmul : (n : ℝ) < (p : ℝ) * (2 * (K : ℝ) + 1) := by
          rw [div_lt_iff₀ (by positivity)] at hp_gt; exact hp_gt
        have hmulN : n < p * (2 * K + 1) := by
          exact_mod_cast (by push_cast; exact hmul : (n : ℝ) < ((p * (2 * K + 1) : ℕ) : ℝ))
        have hp_gt_K : 2 * K + 1 < p := by nlinarith
        calc n < p * (2 * K + 1) := hmulN
          _ < p * p := Nat.mul_lt_mul_of_pos_left hp_gt_K hp_prime.pos
          _ = p ^ 2 := by ring
      have hv : padicValNat p (Nat.factorial n) = n / p :=
        padicValNat_factorial_eq_div_of_lt_sq hp_prime hn_lt_psq
      have hdiv_ge : 2 * r - 1 ≤ n / p := by
        rw [Nat.le_floor_iff (by positivity), le_div_iff₀ (by linarith [hr1R])] at hp_hi
        rw [Nat.le_div_iff_mul_le hp_prime.pos]
        have h1 : ((2 * r - 1 : ℕ) : ℝ) * (p : ℝ) ≤ (n : ℝ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]; push_cast; linarith
        exact_mod_cast h1
      have hdiv_lt : n / p < 2 * r := by
        rw [div_lt_iff₀ (by linarith)] at hp_lo
        rw [Nat.div_lt_iff_lt_mul hp_prime.pos]
        exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((2 * r : ℕ) : ℝ) * (p : ℝ))
      have hdiv_eq : n / p = 2 * r - 1 := by omega
      have hp_le_n : p ≤ n := by
        have := Nat.div_mul_le_self n p
        rw [hdiv_eq] at this
        have h1 : 1 ≤ 2 * r - 1 := by omega
        calc p = 1 * p := (one_mul p).symm
          _ ≤ (2 * r - 1) * p := Nat.mul_le_mul_right p h1
          _ ≤ n := this
      refine ⟨⟨⟨hp2, hp_le_n⟩, hp_prime, ?_⟩, hp_gt⟩
      rw [hv, hdiv_eq]; omega
  have hdisj : (Finset.Icc 1 K : Set ℕ).PairwiseDisjoint L := by
    intro r₁ hr₁ r₂ hr₂ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_coe, Finset.mem_Icc] at hr₁ hr₂
    simp only [L, Finset.mem_filter, Finset.mem_Icc] at hp1 hp2
    have hr₁_1 : (1 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁.1
    have hr₂_1 : (1 : ℝ) ≤ (r₂ : ℝ) := by exact_mod_cast hr₂.1
    have hp1_hi := hp1.1.1.2
    have hp2_hi := hp2.1.1.2
    rw [Nat.le_floor_iff (by positivity), le_div_iff₀ (by linarith [hr₁_1])] at hp1_hi
    rw [Nat.le_floor_iff (by positivity), le_div_iff₀ (by linarith [hr₂_1])] at hp2_hi
    have hp1_lo := hp1.2
    have hp2_lo := hp2.2
    rw [div_lt_iff₀ (by linarith [hr₁_1])] at hp1_lo
    rw [div_lt_iff₀ (by linarith [hr₂_1])] at hp2_lo
    have hle1 : (2 * r₁ - 1) * p ≤ n := by
      have h1 : ((2 * r₁ - 1 : ℕ) : ℝ) * (p : ℝ) ≤ (n : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * r₁)]; push_cast; linarith
      exact_mod_cast h1
    have hle2 : (2 * r₂ - 1) * p ≤ n := by
      have h2 : ((2 * r₂ - 1 : ℕ) : ℝ) * (p : ℝ) ≤ (n : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * r₂)]; push_cast; linarith
      exact_mod_cast h2
    have hlt1 : n < (2 * r₁) * p := by
      exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((2 * r₁ : ℕ) : ℝ) * (p : ℝ))
    have hlt2 : n < (2 * r₂) * p := by
      exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((2 * r₂ : ℕ) : ℝ) * (p : ℝ))
    have h12 : (2 * r₁ - 1) * p < (2 * r₂) * p := lt_of_le_of_lt hle1 hlt2
    have h21 : (2 * r₂ - 1) * p < (2 * r₁) * p := lt_of_le_of_lt hle2 hlt1
    have hlt_12 : 2 * r₁ - 1 < 2 * r₂ := lt_of_mul_lt_mul_right h12 (Nat.zero_le p)
    have hlt_21 : 2 * r₂ - 1 < 2 * r₁ := lt_of_mul_lt_mul_right h21 (Nat.zero_le p)
    omega
  have hL_sdiff : ∀ r ∈ Finset.Icc 1 K,
      L r = (Finset.Icc 2 (Nat.floor ((n : ℝ) / (2 * (r : ℝ) - 1)))).filter Nat.Prime \
            (Finset.Icc 2 (Nat.floor ((n : ℝ) / (2 * (r : ℝ))))).filter Nat.Prime := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    ext p
    simp only [L, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp_icc, hp_prime⟩, hp_lo⟩
      refine ⟨⟨hp_icc, hp_prime⟩, ?_⟩
      intro ⟨hp_icc2, _⟩
      rw [Nat.le_floor_iff (by positivity)] at hp_icc2
      linarith
    · rintro ⟨⟨hp_icc, hp_prime⟩, hnot⟩
      refine ⟨⟨hp_icc, hp_prime⟩, ?_⟩
      by_contra hle
      push Not at hle
      apply hnot
      refine ⟨⟨hp_icc.1, ?_⟩, hp_prime⟩
      rw [Nat.le_floor_iff (by positivity)]
      exact hle
  have hL_sub : ∀ r ∈ Finset.Icc 1 K,
      (Finset.Icc 2 (Nat.floor ((n : ℝ) / (2 * (r : ℝ))))).filter Nat.Prime ⊆
      (Finset.Icc 2 (Nat.floor ((n : ℝ) / (2 * (r : ℝ) - 1)))).filter Nat.Prime := by
    intro r hr p hp
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    refine ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_mono ?_)⟩, hp.2⟩
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  constructor
  · rw [hL_part, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hs : (∑ p ∈ L r, Real.log (p : ℝ)) + thetaPrime ((n : ℝ) / (2 * (r : ℝ))) =
        thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) := by
      rw [hL_sdiff r hr]
      unfold thetaPrime
      exact Finset.sum_sdiff (hL_sub r hr)
    linarith
  · rw [hL_part, Finset.card_biUnion hdisj, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [hL_sdiff r hr, Finset.card_sdiff_of_subset (hL_sub r hr)]
    unfold piPrime
    rw [Nat.cast_sub (Finset.card_le_card (hL_sub r hr))]

/-- **Lemma 2.1(ii), part 1**: `log q_n = (log 2) n + O(n exp(-c₀ √(log n)))` (eq. 2.4). -/
theorem log_q_n_asymptotic :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      (fun n : ℕ => Real.log (q_n n : ℝ) - Real.log 2 * (n : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ)))) := by
  obtain ⟨c₁, hc₁, hdlvp⟩ := de_la_vallee_poussin_theta
  obtain ⟨C₁, hC₁⟩ := hdlvp.bound
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp hC₁
  obtain ⟨Cθ, hCθ_pos, hCθ⟩ := thetaPrime_le_linear
  let c₀ : ℝ := c₁ / 3
  refine ⟨c₀, by positivity, ?_⟩
  have hlog_sqrt_ratio : Tendsto (fun t : ℝ => Real.sqrt t / t) atTop (nhds 0) := by
    have h1 : (fun t : ℝ => Real.sqrt t / t) =ᶠ[atTop] (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have ht_pos : 0 < t := by linarith
      calc Real.sqrt t / t = t ^ (1 / 2 : ℝ) * t ^ (-1 : ℝ) := by
            rw [Real.sqrt_eq_rpow, div_eq_mul_inv, Real.rpow_neg_one]
        _ = t ^ ((1 / 2 : ℝ) + (-1 : ℝ)) := (Real.rpow_add ht_pos _ _).symm
        _ = t ^ (-(1 / 2 : ℝ)) := by norm_num
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr' h1.symm
  have hsqrt_small : ∀ᶠ n : ℕ in atTop,
      (c₁ / 2) * Real.sqrt (Real.log (n : ℝ)) ≤ (1 / 4 : ℝ) * Real.log (n : ℝ) := by
    have ht : Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (nhds 0) :=
      hlog_sqrt_ratio.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have hev : ∀ᶠ n : ℕ in atTop,
        Real.sqrt (Real.log (n : ℝ)) / Real.log (n : ℝ) ≤ 1 / (2 * c₁ + 1) :=
      (ht.eventually (Iio_mem_nhds (by positivity : 0 < 1 / (2 * c₁ + 1)))).mono (fun _ h => h.le)
    have hlog1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) :=
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
    filter_upwards [hev, hlog1] with n hn hln
    rw [div_le_iff₀ (by linarith)] at hn
    have hmul : (c₁ / 2) * Real.sqrt (Real.log (n : ℝ)) ≤
        (c₁ / 2) * ((1 / (2 * c₁ + 1)) * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    have hcoef : (c₁ / 2) * (1 / (2 * c₁ + 1)) ≤ 1 / 4 := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    calc (c₁ / 2) * Real.sqrt (Real.log (n : ℝ))
        ≤ ((c₁ / 2) * (1 / (2 * c₁ + 1))) * Real.log (n : ℝ) := by linarith
      _ ≤ (1 / 4 : ℝ) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right hcoef (by linarith)
  have hlog_exp_small : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ) + 1) * Real.exp (-(c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * Real.sqrt (Real.log (n : ℝ))) ≤ 1 := by
    have hdiff_pos : 0 < c₁ * Real.sqrt (3 / 4 : ℝ) - c₀ := by
      have hsq34 : (1 / 2 : ℝ) < Real.sqrt (3 / 4 : ℝ) := by
        rw [Real.lt_sqrt (by norm_num)]
        norm_num
      unfold c₀
      nlinarith
    have hlo : Tendsto (fun t : ℝ => (t ^ 2 + 1) * Real.exp (-(c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * t))
        atTop (nhds 0) := by
      have h_pow : Tendsto (fun t : ℝ => t ^ 2 * Real.exp (-(c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * t))
          atTop (nhds 0) := by
        have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
        have hcomp := this.comp (tendsto_id.const_mul_atTop hdiff_pos)
        have heq : (fun t : ℝ => t ^ 2 * Real.exp (-(c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * t)) =
            (fun t : ℝ => (1 / (c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) ^ 2) *
              (((c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * t) ^ 2 *
                Real.exp (-((c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * t)))) := by
          ext t; field_simp [hdiff_pos.ne']
        rw [heq]
        have hmul := hcomp.const_mul (1 / (c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) ^ 2)
        rw [mul_zero] at hmul
        exact hmul
      have h_one : Tendsto (fun t : ℝ => Real.exp (-(c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * t))
          atTop (nhds 0) := by
        have heq1 : (fun t : ℝ => Real.exp (-(c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * t)) =
            (fun t : ℝ => Real.exp (-((c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * t))) := by
          ext t; ring_nf
        rw [heq1]
        exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hdiff_pos)
      have heq2 : (fun t : ℝ => (t ^ 2 + 1) * Real.exp (-(c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * t)) =
          (fun t : ℝ => t ^ 2 * Real.exp (-(c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * t) +
            Real.exp (-(c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * t)) := by
        ext t; ring
      rw [heq2]
      simpa using h_pow.add h_one
    have ht_comp := hlo.comp (Real.tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
    have hlog0 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ Real.log (n : ℝ) :=
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 0)
    filter_upwards [(ht_comp.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le),
      hlog0] with n hn hln
    dsimp only [Function.comp_def] at hn hln
    have hsq : Real.sqrt (Real.log (n : ℝ)) ^ 2 = Real.log (n : ℝ) := Real.sq_sqrt hln
    simpa [hsq] using hn
  have hn_large_X1 : ∀ᶠ n : ℕ in atTop, max X₁ 4 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by
    have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (3 / 4 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop (max X₁ 4))
  have hexp_large : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ Real.exp ((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := by
    have ht : Tendsto (fun n : ℕ => Real.exp ((c₁ / 2) * Real.sqrt (Real.log (n : ℝ)))) atTop atTop :=
      Real.tendsto_exp_atTop.comp ((Real.tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop (by positivity))
    exact ht.eventually (eventually_ge_atTop 4)
  let M : ℝ := Cθ * 4 + 4 * |C₁| + 2
  refine Asymptotics.IsBigO.of_bound M ?_
  filter_upwards [Filter.eventually_ge_atTop 16, hsqrt_small, hlog_exp_small, hn_large_X1, hexp_large] with
    n hn hsq_sm hle_sm hnX1 hexp4
  let J := Nat.floor (Real.exp ((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))))
  let K := J / 2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hJ_ge4 : 4 ≤ J := by
    rw [Nat.le_floor_iff (by positivity)]
    exact_mod_cast hexp4
  have hK_ge2 : 2 ≤ K := by omega
  have hK_ge1 : 1 ≤ K := by omega
  have hJ_le_rpow : (J : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    calc (J : ℝ) ≤ Real.exp ((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := Nat.floor_le (by positivity)
      _ ≤ Real.exp ((1 / 4 : ℝ) * Real.log (n : ℝ)) := Real.exp_le_exp.mpr hsq_sm
      _ = Real.exp (Real.log (n : ℝ) * (1 / 4 : ℝ)) := by ring_nf
      _ = (n : ℝ) ^ (1 / 4 : ℝ) := (Real.rpow_def_of_pos hn_pos (1 / 4 : ℝ)).symm
  have h2K1_le_sqrt : 2 * K + 1 ≤ Nat.sqrt n := by
    have h2K1_le : (2 * K + 1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) + 1 := by
      have : (2 * K : ℝ) ≤ (J : ℝ) := by exact_mod_cast (by omega : 2 * K ≤ J)
      linarith
    have h_rpow_le : (n : ℝ) ^ (1 / 4 : ℝ) + 1 ≤ Real.sqrt (n : ℝ) := by
      have hn16 : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 4)]
        rw [← Real.rpow_mul hn_pos.le]
        norm_num
        exact_mod_cast hn
      have hsq_eq : Real.sqrt (n : ℝ) = ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]
        congr 1; norm_num
      rw [hsq_eq]
      nlinarith
    have h_nat : ((2 * K + 1 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by push_cast; linarith
    rw [← Nat.le_floor_iff (Real.sqrt_nonneg _)] at h_nat
    have hsq_fl : Nat.floor (Real.sqrt (n : ℝ)) = Nat.sqrt n := by
      rw [Nat.floor_eq_iff (Real.sqrt_nonneg _)]
      exact ⟨by rw [Real.le_sqrt (by positivity) (by positivity)]; exact_mod_cast Nat.sqrt_le' n,
             by rw [Real.sqrt_lt' (by positivity)]; exact_mod_cast Nat.lt_succ_sqrt' n⟩
    omega
  have hpart := (Podd_upper_partition n K (by omega) hK_ge1 h2K1_le_sqrt).1
  have hsplit : (Podd n) =
      (Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (K : ℝ) + 1)) ∪
      (Podd n).filter (fun p : ℕ => (n : ℝ) / (2 * (K : ℝ) + 1) < (p : ℝ)) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      rcases le_or_gt (p : ℝ) ((n : ℝ) / (2 * (K : ℝ) + 1)) with hle | hgt
      · left; exact ⟨hp, hle⟩
      · right; exact ⟨hp, hgt⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hdisj : Disjoint
      ((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (K : ℝ) + 1)))
      ((Podd n).filter (fun p : ℕ => (n : ℝ) / (2 * (K : ℝ) + 1) < (p : ℝ))) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    linarith
  have hlog_eq := log_q_n_eq_sum_log n
  rw [hsplit, Finset.sum_union hdisj, hpart] at hlog_eq
  have hlo_bound : 0 ≤ ∑ p ∈ (Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (K : ℝ) + 1)), Real.log (p : ℝ) ∧
      ∑ p ∈ (Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (K : ℝ) + 1)), Real.log (p : ℝ) ≤
        thetaPrime ((n : ℝ) / (2 * (K : ℝ) + 1)) := by
    have hsub : (Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (K : ℝ) + 1)) ⊆
        (Finset.Icc 2 (Nat.floor ((n : ℝ) / (2 * (K : ℝ) + 1)))).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      unfold Podd at hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      exact ⟨⟨hp.1.1.1, (Nat.le_floor_iff (by positivity)).mpr hp.2⟩, hp.1.2.1⟩
    constructor
    · refine Finset.sum_nonneg (fun p hp => ?_)
      have hp2 : 2 ≤ p := by
        have := (Finset.mem_filter.mp hp).1
        unfold Podd at this
        exact (Finset.mem_Icc.mp (Finset.mem_filter.mp this).1).1
      exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
    · unfold thetaPrime
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_)
      have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  have h2K1_ge_exp : (1 / 4 : ℝ) * Real.exp ((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) ≤ 2 * (K : ℝ) + 1 := by
    have hJ1 : Real.exp ((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) ≤ (J : ℝ) + 1 := by
      linarith [Nat.lt_floor_add_one (Real.exp ((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))))]
    have hJK : (J : ℝ) ≤ 2 * (K : ℝ) + 1 := by exact_mod_cast (by omega : J ≤ 2 * K + 1)
    have hexp_ge4 : (4 : ℝ) ≤ Real.exp ((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := hexp4
    linarith
  have hc0_le : Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) ≤
      Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    unfold c₀
    nlinarith [Real.sqrt_nonneg (Real.log (n : ℝ))]
  have hlo_err : thetaPrime ((n : ℝ) / (2 * (K : ℝ) + 1)) ≤
      Cθ * 4 * (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by
    have hge1 : 1 ≤ (n : ℝ) / (2 * (K : ℝ) + 1) := by
      rw [le_div_iff₀ (by positivity), one_mul]
      have hsq_le : ((2 * K + 1 : ℕ) : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast h2K1_le_sqrt
      have hsqrt_le_n : (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le_self n
      push_cast at hsq_le; linarith
    calc thetaPrime ((n : ℝ) / (2 * (K : ℝ) + 1))
        ≤ Cθ * ((n : ℝ) / (2 * (K : ℝ) + 1)) := hCθ _ hge1
      _ ≤ Cθ * ((n : ℝ) / ((1 / 4 : ℝ) * Real.exp ((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))))) := by
          apply mul_le_mul_of_nonneg_left _ hCθ_pos.le
          exact div_le_div_of_nonneg_left hn_pos.le (by positivity) h2K1_ge_exp
      _ = Cθ * 4 * (n : ℝ) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := by
          rw [show -(c₁ / 2) * Real.sqrt (Real.log (n : ℝ)) = -((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) from by ring,
            Real.exp_neg]
          field_simp
      _ ≤ Cθ * 4 * (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_left hc0_le (by positivity)
  have h34_eq : (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [show (3 / 4 : ℝ) = 1 - 1 / 4 from by norm_num, Real.rpow_sub hn_pos, Real.rpow_one]
  have hr_err : ∀ r ∈ Finset.Icc 1 K,
      |(thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - thetaPrime ((n : ℝ) / (2 * (r : ℝ)))) -
        (n : ℝ) * (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))| ≤
      2 * |C₁| * ((n : ℝ) / (2 * (r : ℝ) - 1)) *
        Real.exp (-c₁ * Real.sqrt (3 / 4 : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrK : r ≤ K := (Finset.mem_Icc.mp hr).2
    have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have h2r1_pos : (0 : ℝ) < 2 * (r : ℝ) - 1 := by linarith
    have h2r_le : 2 * (r : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
      calc 2 * (r : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast (by omega : 2 * r ≤ 2 * K)
        _ ≤ (J : ℝ) := by exact_mod_cast (by omega : 2 * K ≤ J)
        _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) := hJ_le_rpow
    have h_div2_ge : max X₁ 4 ≤ (n : ℝ) / (2 * (r : ℝ)) := by
      calc max X₁ 4 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := hnX1
        _ = (n : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) := h34_eq
        _ ≤ (n : ℝ) / (2 * (r : ℝ)) :=
            div_le_div_of_nonneg_left hn_pos.le (by positivity) h2r_le
    have h_div1_ge : (n : ℝ) / (2 * (r : ℝ)) ≤ (n : ℝ) / (2 * (r : ℝ) - 1) :=
      div_le_div_of_nonneg_left hn_pos.le h2r1_pos (by linarith)
    have h_b1 := hX₁ ((n : ℝ) / (2 * (r : ℝ) - 1)) (le_trans (le_max_left _ _) (le_trans h_div2_ge h_div1_ge))
    have h_b2 := hX₁ ((n : ℝ) / (2 * (r : ℝ))) (le_trans (le_max_left _ _) h_div2_ge)
    have hnn1 : 0 ≤ (n : ℝ) / (2 * (r : ℝ) - 1) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ) - 1)))) :=
      mul_nonneg (div_nonneg hn_pos.le h2r1_pos.le) (Real.exp_pos _).le
    have hnn2 : 0 ≤ (n : ℝ) / (2 * (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ))))) :=
      mul_nonneg (div_nonneg hn_pos.le (by positivity)) (Real.exp_pos _).le
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hnn1] at h_b1
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hnn2] at h_b2
    have hlog_ge : (3 / 4 : ℝ) * Real.log (n : ℝ) ≤ Real.log ((n : ℝ) / (2 * (r : ℝ))) := by
      have h34 : (n : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / (2 * (r : ℝ)) := by
        calc (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) := h34_eq
          _ ≤ (n : ℝ) / (2 * (r : ℝ)) := div_le_div_of_nonneg_left hn_pos.le (by positivity) h2r_le
      calc (3 / 4 : ℝ) * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ (3 / 4 : ℝ)) := by
            rw [Real.log_rpow hn_pos]
        _ ≤ Real.log ((n : ℝ) / (2 * (r : ℝ))) := Real.log_le_log (by positivity) h34
    have hexp_b : ∀ x : ℝ, (n : ℝ) / (2 * (r : ℝ)) ≤ x →
        Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤
          Real.exp (-c₁ * Real.sqrt (3 / 4 : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by
      intro x hx
      apply Real.exp_le_exp.mpr
      have hsq_le : Real.sqrt ((3 / 4 : ℝ) * Real.log (n : ℝ)) ≤ Real.sqrt (Real.log x) := by
        apply Real.sqrt_le_sqrt
        exact le_trans hlog_ge (Real.log_le_log (by positivity) hx)
      rw [Real.sqrt_mul (by norm_num)] at hsq_le
      nlinarith
    have h_e1 : |thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - (n : ℝ) / (2 * (r : ℝ) - 1)| ≤
        |C₁| * ((n : ℝ) / (2 * (r : ℝ) - 1)) *
          Real.exp (-c₁ * Real.sqrt (3 / 4 : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by
      calc |thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - (n : ℝ) / (2 * (r : ℝ) - 1)|
          ≤ C₁ * (((n : ℝ) / (2 * (r : ℝ) - 1)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ) - 1))))) := h_b1
        _ ≤ |C₁| * (((n : ℝ) / (2 * (r : ℝ) - 1)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ) - 1))))) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hnn1
        _ ≤ |C₁| * (((n : ℝ) / (2 * (r : ℝ) - 1)) *
              Real.exp (-c₁ * Real.sqrt (3 / 4 : ℝ) * Real.sqrt (Real.log (n : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hexp_b _ h_div1_ge) (div_nonneg hn_pos.le h2r1_pos.le)) (abs_nonneg _)
        _ = |C₁| * ((n : ℝ) / (2 * (r : ℝ) - 1)) *
              Real.exp (-c₁ * Real.sqrt (3 / 4 : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by ring
    have h_e2 : |thetaPrime ((n : ℝ) / (2 * (r : ℝ))) - (n : ℝ) / (2 * (r : ℝ))| ≤
        |C₁| * ((n : ℝ) / (2 * (r : ℝ) - 1)) *
          Real.exp (-c₁ * Real.sqrt (3 / 4 : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by
      calc |thetaPrime ((n : ℝ) / (2 * (r : ℝ))) - (n : ℝ) / (2 * (r : ℝ))|
          ≤ C₁ * (((n : ℝ) / (2 * (r : ℝ))) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ)))))) := h_b2
        _ ≤ |C₁| * (((n : ℝ) / (2 * (r : ℝ))) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (2 * (r : ℝ)))))) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hnn2
        _ ≤ |C₁| * (((n : ℝ) / (2 * (r : ℝ) - 1)) *
              Real.exp (-c₁ * Real.sqrt (3 / 4 : ℝ) * Real.sqrt (Real.log (n : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h_div1_ge (hexp_b _ le_rfl) (Real.exp_pos _).le (div_nonneg hn_pos.le h2r1_pos.le)) (abs_nonneg _)
        _ = |C₁| * ((n : ℝ) / (2 * (r : ℝ) - 1)) *
              Real.exp (-c₁ * Real.sqrt (3 / 4 : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by ring
    have h_tri : (thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - thetaPrime ((n : ℝ) / (2 * (r : ℝ)))) -
        (n : ℝ) * (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) =
        (thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - (n : ℝ) / (2 * (r : ℝ) - 1)) -
        (thetaPrime ((n : ℝ) / (2 * (r : ℝ))) - (n : ℝ) / (2 * (r : ℝ))) := by ring
    rw [h_tri]
    calc |(thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - (n : ℝ) / (2 * (r : ℝ) - 1)) -
          (thetaPrime ((n : ℝ) / (2 * (r : ℝ))) - (n : ℝ) / (2 * (r : ℝ)))|
        ≤ |thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - (n : ℝ) / (2 * (r : ℝ) - 1)| +
          |thetaPrime ((n : ℝ) / (2 * (r : ℝ))) - (n : ℝ) / (2 * (r : ℝ))| := abs_sub _ _
      _ ≤ 2 * |C₁| * ((n : ℝ) / (2 * (r : ℝ) - 1)) *
            Real.exp (-c₁ * Real.sqrt (3 / 4 : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by linarith
  have hexp_prod : Real.exp (-c₁ * Real.sqrt (3 / 4 : ℝ) * Real.sqrt (Real.log (n : ℝ))) =
      Real.exp (-(c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * Real.sqrt (Real.log (n : ℝ))) *
      Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsum_err : |∑ r ∈ Finset.Icc 1 K,
        (thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - thetaPrime ((n : ℝ) / (2 * (r : ℝ)))) -
      (n : ℝ) * ∑ r ∈ Finset.Icc 1 K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))| ≤
      2 * |C₁| * (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc |∑ r ∈ Finset.Icc 1 K,
            ((thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - thetaPrime ((n : ℝ) / (2 * (r : ℝ)))) -
              (n : ℝ) * (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))))|
        ≤ ∑ r ∈ Finset.Icc 1 K,
            |(thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - thetaPrime ((n : ℝ) / (2 * (r : ℝ)))) -
              (n : ℝ) * (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Finset.Icc 1 K,
            2 * |C₁| * ((n : ℝ) / (2 * (r : ℝ) - 1)) *
              Real.exp (-c₁ * Real.sqrt (3 / 4 : ℝ) * Real.sqrt (Real.log (n : ℝ))) := Finset.sum_le_sum hr_err
      _ = 2 * |C₁| * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (3 / 4 : ℝ) * Real.sqrt (Real.log (n : ℝ))) *
            ∑ r ∈ Finset.Icc 1 K, (1 : ℝ) / (2 * (r : ℝ) - 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun r _ => by ring)
      _ ≤ 2 * |C₁| * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (3 / 4 : ℝ) * Real.sqrt (Real.log (n : ℝ))) *
            (Real.log (n : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ∑ r ∈ Finset.Icc 1 K, (1 : ℝ) / (2 * (r : ℝ) - 1)
              ≤ ∑ r ∈ Finset.Icc 1 K, (1 : ℝ) / (r : ℝ) := by
                refine Finset.sum_le_sum (fun r hr => ?_)
                have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hr).1
                have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hr).1
                exact one_div_le_one_div_of_le hr_pos (by linarith)
            _ ≤ Real.log (K : ℝ) + 1 := harmonic_sum_le_log_add_one_aux hK_ge1
            _ ≤ Real.log (n : ℝ) + 1 := by
                have hKn : (K : ℝ) ≤ (n : ℝ) := by
                  have hK_le : (K : ℝ) ≤ (J : ℝ) := by exact_mod_cast (by omega : K ≤ J)
                  have hn14 : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) := by
                    calc (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
                          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
                      _ = (n : ℝ) := Real.rpow_one _
                  linarith [hJ_le_rpow]
                linarith [Real.log_le_log (by exact_mod_cast hK_ge1) hKn]
      _ = 2 * |C₁| * (n : ℝ) *
            ((Real.log (n : ℝ) + 1) * Real.exp (-(c₁ * Real.sqrt (3 / 4 : ℝ) - c₀) * Real.sqrt (Real.log (n : ℝ)))) *
            Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by
          rw [hexp_prod]; ring
      _ ≤ 2 * |C₁| * (n : ℝ) * 1 * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hle_sm (by positivity)
      _ = 2 * |C₁| * (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by ring
  have hK_exp_half : (1 / 2 : ℝ) * Real.exp ((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) ≤ 2 * (K : ℝ) := by
    have hJ1 : Real.exp ((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) ≤ (J : ℝ) + 1 := by
      linarith [Nat.lt_floor_add_one (Real.exp ((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))))]
    have hJK : (J : ℝ) ≤ 2 * (K : ℝ) + 1 := by exact_mod_cast (by omega : J ≤ 2 * K + 1)
    linarith [hexp4]
  have halt_err2 : |(n : ℝ) * (∑ r ∈ Finset.Icc 1 K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2)| ≤
      2 * (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by
    rw [abs_mul, abs_of_pos hn_pos]
    calc (n : ℝ) * |∑ r ∈ Finset.Icc 1 K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2|
        ≤ (n : ℝ) * (1 / (2 * (K : ℝ))) :=
          mul_le_mul_of_nonneg_left (alt_harmonic_sum_diff_log_two hK_ge1) hn_pos.le
      _ ≤ (n : ℝ) * (1 / ((1 / 2 : ℝ) * Real.exp ((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))))) := by
          apply mul_le_mul_of_nonneg_left _ hn_pos.le
          exact one_div_le_one_div_of_le (by positivity) hK_exp_half
      _ = 2 * (n : ℝ) * Real.exp (-(c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) := by
          rw [show -(c₁ / 2) * Real.sqrt (Real.log (n : ℝ)) = -((c₁ / 2) * Real.sqrt (Real.log (n : ℝ))) from by ring,
            Real.exp_neg]
          field_simp
      _ ≤ 2 * (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_left hc0_le (by positivity)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity), hlog_eq]
  have hlo_abs : |∑ p ∈ (Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (K : ℝ) + 1)), Real.log (p : ℝ)| ≤
      Cθ * 4 * (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by
    rw [abs_of_nonneg hlo_bound.1]
    exact le_trans hlo_bound.2 hlo_err
  have h_id : (∑ p ∈ (Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (K : ℝ) + 1)), Real.log (p : ℝ) +
        ∑ r ∈ Finset.Icc 1 K, (thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - thetaPrime ((n : ℝ) / (2 * (r : ℝ))))) -
      Real.log 2 * (n : ℝ) =
      (∑ p ∈ (Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (K : ℝ) + 1)), Real.log (p : ℝ)) +
      (∑ r ∈ Finset.Icc 1 K, (thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - thetaPrime ((n : ℝ) / (2 * (r : ℝ)))) -
        (n : ℝ) * ∑ r ∈ Finset.Icc 1 K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) +
      (n : ℝ) * (∑ r ∈ Finset.Icc 1 K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2) := by ring
  rw [h_id]
  have htri1 := abs_add_le
    ((∑ p ∈ (Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (K : ℝ) + 1)), Real.log (p : ℝ)) +
      (∑ r ∈ Finset.Icc 1 K, (thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - thetaPrime ((n : ℝ) / (2 * (r : ℝ)))) -
        (n : ℝ) * ∑ r ∈ Finset.Icc 1 K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))))
    ((n : ℝ) * (∑ r ∈ Finset.Icc 1 K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2))
  have htri2 := abs_add_le
    (∑ p ∈ (Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (K : ℝ) + 1)), Real.log (p : ℝ))
    (∑ r ∈ Finset.Icc 1 K, (thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - thetaPrime ((n : ℝ) / (2 * (r : ℝ)))) -
      (n : ℝ) * ∑ r ∈ Finset.Icc 1 K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))))
  calc |((∑ p ∈ (Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (K : ℝ) + 1)), Real.log (p : ℝ)) +
          (∑ r ∈ Finset.Icc 1 K, (thetaPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - thetaPrime ((n : ℝ) / (2 * (r : ℝ)))) -
            (n : ℝ) * ∑ r ∈ Finset.Icc 1 K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))))) +
          (n : ℝ) * (∑ r ∈ Finset.Icc 1 K, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2)|
      ≤ (Cθ * 4 + 2 * |C₁| + 2) * ((n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ)))) := by
          linarith [htri1, htri2, hlo_abs, hsum_err, halt_err2]
    _ ≤ M * ((n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ)))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          unfold M; linarith [abs_nonneg C₁]

private theorem piPrime_div_asymptotic (d : ℕ) (hd : 1 ≤ d) :
    (fun n : ℕ => piPrime ((n : ℝ) / (d : ℝ)) - ((1 : ℝ) / (d : ℝ)) * ((n : ℝ) / Real.log (n : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have htend_div : Tendsto (fun n : ℕ => (n : ℝ) / (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hd_pos
  have h1 : (fun n : ℕ => piPrime ((n : ℝ) / (d : ℝ)) - ((n : ℝ) / (d : ℝ)) / Real.log ((n : ℝ) / (d : ℝ)))
      =o[atTop] (fun n : ℕ => ((n : ℝ) / (d : ℝ)) / Real.log ((n : ℝ) / (d : ℝ))) :=
    pnt_pi_asymptotic.comp_tendsto htend_div
  have h_ratio : Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.log ((n : ℝ) / (d : ℝ))) atTop (nhds 1) := by
    have hlog : Tendsto (fun n : ℕ => 1 - Real.log (d : ℝ) / Real.log (n : ℝ)) atTop (nhds 1) := by
      have h0 : Tendsto (fun n : ℕ => Real.log (d : ℝ) / Real.log (n : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      simpa using tendsto_const_nhds.sub h0
    have hev : (fun n : ℕ => Real.log ((n : ℝ) / (d : ℝ)) / Real.log (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ => 1 - Real.log (d : ℝ) / Real.log (n : ℝ)) := by
      filter_upwards [(tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1),
        Filter.eventually_ge_atTop 2] with n hln hn2
      dsimp only [Function.comp_def] at hln
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hln0 : Real.log (n : ℝ) ≠ 0 := by linarith
      rw [Real.log_div hn_pos.ne' hd_pos.ne']
      field_simp [hln0]
    have hinv := (hlog.congr' hev.symm).inv₀ (by norm_num)
    simpa [inv_div] using hinv
  have h2 : (fun n : ℕ => ((n : ℝ) / (d : ℝ)) / Real.log ((n : ℝ) / (d : ℝ)))
      =O[atTop] (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound (2 / (d : ℝ)) ?_
    filter_upwards [(h_ratio.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))).mono (fun _ h => h.le),
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1),
      Filter.eventually_ge_atTop (max 2 (2 * d))] with n hr hln hn
    dsimp only [Function.comp_def] at hln
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnd_ge : (2 : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hd_pos]
      exact_mod_cast (by omega : 2 * d ≤ n)
    have hlog_nd_pos : 0 < Real.log ((n : ℝ) / (d : ℝ)) := Real.log_pos (by linarith)
    have hln0 : Real.log (n : ℝ) ≠ 0 := by linarith
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    calc ((n : ℝ) / (d : ℝ)) / Real.log ((n : ℝ) / (d : ℝ))
        = (1 / (d : ℝ)) * (Real.log (n : ℝ) / Real.log ((n : ℝ) / (d : ℝ))) * ((n : ℝ) / Real.log (n : ℝ)) := by
          field_simp [hd_pos.ne', hlog_nd_pos.ne', hln0]
      _ ≤ (1 / (d : ℝ)) * 2 * ((n : ℝ) / Real.log (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hr (by positivity)
      _ = (2 / (d : ℝ)) * ((n : ℝ) / Real.log (n : ℝ)) := by ring
  have h1' : (fun n : ℕ => piPrime ((n : ℝ) / (d : ℝ)) - ((n : ℝ) / (d : ℝ)) / Real.log ((n : ℝ) / (d : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := h1.trans_isBigO h2
  have h3 : (fun n : ℕ => ((n : ℝ) / (d : ℝ)) / Real.log ((n : ℝ) / (d : ℝ)) -
        ((1 : ℝ) / (d : ℝ)) * ((n : ℝ) / Real.log (n : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have h_diff0 : Tendsto (fun n : ℕ => (1 / (d : ℝ)) * (Real.log (n : ℝ) / Real.log ((n : ℝ) / (d : ℝ)) - 1))
        atTop (nhds 0) := by
      have hsub := (h_ratio.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))).const_mul (1 / (d : ℝ))
      rw [sub_self, mul_zero] at hsub
      exact hsub
    filter_upwards [h_diff0.eventually (Metric.ball_mem_nhds 0 hc),
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1),
      Filter.eventually_ge_atTop (max 2 (2 * d))] with n hn hln hn_ge
    dsimp only [Function.comp_def] at hln
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnd_ge : (2 : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
      rw [le_div_iff₀ hd_pos]; exact_mod_cast (by omega : 2 * d ≤ n)
    have hlog_nd_pos : 0 < Real.log ((n : ℝ) / (d : ℝ)) := Real.log_pos (by linarith)
    have hln0 : Real.log (n : ℝ) ≠ 0 := by linarith
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hn
    have heq : ((n : ℝ) / (d : ℝ)) / Real.log ((n : ℝ) / (d : ℝ)) - ((1 : ℝ) / (d : ℝ)) * ((n : ℝ) / Real.log (n : ℝ)) =
        ((1 / (d : ℝ)) * (Real.log (n : ℝ) / Real.log ((n : ℝ) / (d : ℝ)) - 1)) * ((n : ℝ) / Real.log (n : ℝ)) := by
      field_simp [hd_pos.ne', hlog_nd_pos.ne', hln0]
    rw [heq, _root_.norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right hn.le (by positivity)
  simpa [sub_add_sub_cancel] using h1'.add h3

/-- **Lemma 2.1(ii), part 2**: `|Podd(n)| = (log 2 + o(1)) π(n)` (eq. 2.4). -/
theorem card_Podd_asymptotic :
    (fun n : ℕ => ((Podd n).card : ℝ) - Real.log 2 * piPrime (n : ℝ))
      =o[atTop] (fun n : ℕ => piPrime (n : ℝ)) := by
  obtain ⟨Cpi, hCpi_pos, hCpi⟩ := chebyshev_pi_upper
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨M, hM1, hM_alt, hM_lo⟩ : ∃ M : ℕ, 1 ≤ M ∧
      1 / (2 * (M : ℝ)) ≤ ε / 8 ∧ Cpi / (2 * (M : ℝ) + 1) ≤ ε / 8 := by
    obtain ⟨M0, hM0⟩ := exists_nat_gt (max (4 / ε) (8 * Cpi / ε))
    refine ⟨max M0 1, le_max_right _ _, ?_, ?_⟩
    · have hM_le : (M0 : ℝ) ≤ ((max M0 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left M0 1
      have hM_gt : 4 / ε < ((max M0 1 : ℕ) : ℝ) :=
        lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hM0) hM_le
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h1 : 4 < ((max M0 1 : ℕ) : ℝ) * ε := (div_lt_iff₀ hε).mp hM_gt
      linarith
    · have hM_le : (M0 : ℝ) ≤ ((max M0 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left M0 1
      have hM_gt : 8 * Cpi / ε < ((max M0 1 : ℕ) : ℝ) :=
        lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hM0) hM_le
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h1 : 8 * Cpi < ((max M0 1 : ℕ) : ℝ) * ε := (div_lt_iff₀ hε).mp hM_gt
      linarith
  let η : ℝ := min (ε / (8 * (M : ℝ))) (min (ε / (8 * Real.log 2 + 1)) (1 / 4))
  have hη_pos : 0 < η := by positivity
  have h_pnt1 := (Asymptotics.isLittleO_iff.mp (piPrime_div_asymptotic 1 (by norm_num))) hη_pos
  have h_pnt_all : ∀ᶠ n : ℕ in atTop, ∀ r ∈ Finset.Icc 1 M,
      ‖piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - (1 / (2 * (r : ℝ) - 1)) * ((n : ℝ) / Real.log (n : ℝ))‖ ≤
        η * ((n : ℝ) / Real.log (n : ℝ)) ∧
      ‖piPrime ((n : ℝ) / (2 * (r : ℝ))) - (1 / (2 * (r : ℝ))) * ((n : ℝ) / Real.log (n : ℝ))‖ ≤
        η * ((n : ℝ) / Real.log (n : ℝ)) := by
    rw [Filter.eventually_all_finset]
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have h2r1 := (Asymptotics.isLittleO_iff.mp (piPrime_div_asymptotic (2 * r - 1) (by omega))) hη_pos
    have h2r := (Asymptotics.isLittleO_iff.mp (piPrime_div_asymptotic (2 * r) (by omega))) hη_pos
    filter_upwards [h2r1, h2r, (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)] with n ha hb hln
    dsimp only [Function.comp_def] at hln
    have hn_pos : 0 ≤ (n : ℝ) / Real.log (n : ℝ) := by positivity
    rw [Real.norm_of_nonneg hn_pos] at ha hb
    have hcast1 : ((2 * r - 1 : ℕ) : ℝ) = 2 * (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]; push_cast; ring
    have hcast2 : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
    rw [hcast1] at ha; rw [hcast2] at hb
    exact ⟨ha, hb⟩
  have hlog_ratio_lo : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ 2 * Real.log ((n : ℝ) / (2 * (M : ℝ) + 1)) := by
    have ht : Tendsto (fun n : ℕ => Real.log ((n : ℝ) / (2 * (M : ℝ) + 1)) / Real.log (n : ℝ)) atTop (nhds 1) := by
      have h0 : Tendsto (fun n : ℕ => 1 - Real.log (2 * (M : ℝ) + 1) / Real.log (n : ℝ)) atTop (nhds 1) := by
        simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
      have hev : (fun n : ℕ => Real.log ((n : ℝ) / (2 * (M : ℝ) + 1)) / Real.log (n : ℝ)) =ᶠ[atTop]
          (fun n : ℕ => 1 - Real.log (2 * (M : ℝ) + 1) / Real.log (n : ℝ)) := by
        filter_upwards [(tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1),
          Filter.eventually_ge_atTop 2] with n hln hn2
        dsimp only [Function.comp_def] at hln
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hln0 : Real.log (n : ℝ) ≠ 0 := by linarith
        rw [Real.log_div hn_pos.ne' (by positivity)]
        field_simp [hln0]
      exact h0.congr' hev.symm
    filter_upwards [(ht.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))),
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)] with n hr hln
    dsimp only [Function.comp_def] at hln
    rw [lt_div_iff₀ (by linarith)] at hr
    linarith [hr.le]
  filter_upwards [Filter.eventually_ge_atTop ((2 * M + 1) ^ 2 + 4), h_pnt1, h_pnt_all, hlog_ratio_lo,
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)] with
    n hn hpnt1 hpnt_all hlog_rat hln
  dsimp only [Function.comp_def] at hln
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h2M1_sq : 2 * M + 1 ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt]; nlinarith
  have hpart := (Podd_upper_partition n M (by omega) hM1 h2M1_sq).2
  have hsplit : (Podd n).card =
      ((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1))).card +
      ((Podd n).filter (fun p : ℕ => (n : ℝ) / (2 * (M : ℝ) + 1) < (p : ℝ))).card := by
    have hU : Podd n =
        (Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1)) ∪
        (Podd n).filter (fun p : ℕ => (n : ℝ) / (2 * (M : ℝ) + 1) < (p : ℝ)) := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hp; rcases le_or_gt (p : ℝ) ((n : ℝ) / (2 * (M : ℝ) + 1)) with h | h
        · left; exact ⟨hp, h⟩
        · right; exact ⟨hp, h⟩
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    have hD : Disjoint
        ((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1)))
        ((Podd n).filter (fun p : ℕ => (n : ℝ) / (2 * (M : ℝ) + 1) < (p : ℝ))) := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      simp only [Finset.mem_filter] at hp1 hp2; linarith
    rw [← Finset.card_union_of_disjoint hD, ← hU]
  have hcard_eq : ((Podd n).card : ℝ) =
      (((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1))).card : ℝ) +
      ∑ r ∈ Finset.Icc 1 M,
        (piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - piPrime ((n : ℝ) / (2 * (r : ℝ)))) := by
    rw [hsplit, Nat.cast_add, hpart]
  have hlo_le : (((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1))).card : ℝ) ≤
      (ε / 4) * ((n : ℝ) / Real.log (n : ℝ)) := by
    have hsub : (Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1)) ⊆
        (Finset.Icc 2 (Nat.floor ((n : ℝ) / (2 * (M : ℝ) + 1)))).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      unfold Podd at hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp
      exact ⟨⟨hp.1.1.1, (Nat.le_floor_iff (by positivity)).mpr hp.2⟩, hp.1.2.1⟩
    have hle_pi : (((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1))).card : ℝ) ≤
        piPrime ((n : ℝ) / (2 * (M : ℝ) + 1)) := by
      unfold piPrime; exact_mod_cast Finset.card_le_card hsub
    have hge2 : (2 : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1) := by
      rw [le_div_iff₀ (by positivity)]
      have : 2 * (2 * M + 1) ≤ (2 * M + 1) ^ 2 + 4 := by nlinarith
      exact_mod_cast (by omega : 2 * (2 * M + 1) ≤ n)
    have hcpi := hCpi ((n : ℝ) / (2 * (M : ℝ) + 1)) hge2
    have hlog_pos : 0 < Real.log ((n : ℝ) / (2 * (M : ℝ) + 1)) := Real.log_pos (by linarith)
    calc (((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1))).card : ℝ)
        ≤ Cpi * (((n : ℝ) / (2 * (M : ℝ) + 1)) / Real.log ((n : ℝ) / (2 * (M : ℝ) + 1))) := le_trans hle_pi hcpi
      _ ≤ Cpi * (((n : ℝ) / (2 * (M : ℝ) + 1)) / ((1 / 2 : ℝ) * Real.log (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hCpi_pos.le
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = 2 * (Cpi / (2 * (M : ℝ) + 1)) * ((n : ℝ) / Real.log (n : ℝ)) := by ring
      _ ≤ 2 * (ε / 8) * ((n : ℝ) / Real.log (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hM_lo (by norm_num)
      _ = (ε / 4) * ((n : ℝ) / Real.log (n : ℝ)) := by ring
  have hsum_err : |∑ r ∈ Finset.Icc 1 M,
        (piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - piPrime ((n : ℝ) / (2 * (r : ℝ)))) -
      (∑ r ∈ Finset.Icc 1 M, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) * ((n : ℝ) / Real.log (n : ℝ))| ≤
      (ε / 4) * ((n : ℝ) / Real.log (n : ℝ)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    calc |∑ r ∈ Finset.Icc 1 M,
            ((piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - piPrime ((n : ℝ) / (2 * (r : ℝ)))) -
              (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) * ((n : ℝ) / Real.log (n : ℝ)))|
        ≤ ∑ r ∈ Finset.Icc 1 M,
            |(piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - piPrime ((n : ℝ) / (2 * (r : ℝ)))) -
              (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) * ((n : ℝ) / Real.log (n : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ Finset.Icc 1 M, (2 * η) * ((n : ℝ) / Real.log (n : ℝ)) := by
          refine Finset.sum_le_sum (fun r hr => ?_)
          have ⟨ha, hb⟩ := hpnt_all r hr
          rw [Real.norm_eq_abs] at ha hb
          have h_id : (piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - piPrime ((n : ℝ) / (2 * (r : ℝ)))) -
              (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) * ((n : ℝ) / Real.log (n : ℝ)) =
              (piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - (1 / (2 * (r : ℝ) - 1)) * ((n : ℝ) / Real.log (n : ℝ))) -
              (piPrime ((n : ℝ) / (2 * (r : ℝ))) - (1 / (2 * (r : ℝ))) * ((n : ℝ) / Real.log (n : ℝ))) := by ring
          rw [h_id]
          linarith [abs_sub
            (piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - (1 / (2 * (r : ℝ) - 1)) * ((n : ℝ) / Real.log (n : ℝ)))
            (piPrime ((n : ℝ) / (2 * (r : ℝ))) - (1 / (2 * (r : ℝ))) * ((n : ℝ) / Real.log (n : ℝ)))]
      _ = (M : ℝ) * (2 * η) * ((n : ℝ) / Real.log (n : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (ε / 4) * ((n : ℝ) / Real.log (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hη_le : η ≤ ε / (8 * (M : ℝ)) := min_le_left _ _
          have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
          calc (M : ℝ) * (2 * η) ≤ (M : ℝ) * (2 * (ε / (8 * (M : ℝ)))) := by
                apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hη_le (by norm_num)) hM_pos.le
            _ = ε / 4 := by field_simp [hM_pos.ne']; ring
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ) / Real.log (n : ℝ))] at hpnt1
  simp only [Nat.cast_one, div_one, one_div, inv_one, one_mul] at hpnt1
  have hpi_lo : (3 / 4 : ℝ) * ((n : ℝ) / Real.log (n : ℝ)) ≤ piPrime (n : ℝ) := by
    have hη_le : η ≤ 1 / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
    have hη_mul : η * ((n : ℝ) / Real.log (n : ℝ)) ≤ (1 / 4 : ℝ) * ((n : ℝ) / Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hη_le (by positivity)
    linarith [(abs_le.mp hpnt1).1]
  have hpi_err : |Real.log 2 * (piPrime (n : ℝ) - (n : ℝ) / Real.log (n : ℝ))| ≤
      (ε / 8) * ((n : ℝ) / Real.log (n : ℝ)) := by
    rw [abs_mul, abs_of_pos hlog2_pos]
    have hη_le : η ≤ ε / (8 * Real.log 2 + 1) := le_trans (min_le_right _ _) (min_le_left _ _)
    calc Real.log 2 * |piPrime (n : ℝ) - (n : ℝ) / Real.log (n : ℝ)|
        ≤ Real.log 2 * (η * ((n : ℝ) / Real.log (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hpnt1 hlog2_pos.le
      _ ≤ Real.log 2 * ((ε / (8 * Real.log 2 + 1)) * ((n : ℝ) / Real.log (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hlog2_pos.le
          exact mul_le_mul_of_nonneg_right hη_le (by positivity)
      _ ≤ (ε / 8) * ((n : ℝ) / Real.log (n : ℝ)) := by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hlog2_pos]
  have halt_err : |(∑ r ∈ Finset.Icc 1 M, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2) *
        ((n : ℝ) / Real.log (n : ℝ))| ≤ (ε / 8) * ((n : ℝ) / Real.log (n : ℝ)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) / Real.log (n : ℝ))]
    exact mul_le_mul_of_nonneg_right (le_trans (alt_harmonic_sum_diff_log_two hM1) hM_alt) (by positivity)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by unfold piPrime; positivity), hcard_eq]
  have h_id : (((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1))).card : ℝ) +
        ∑ r ∈ Finset.Icc 1 M, (piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - piPrime ((n : ℝ) / (2 * (r : ℝ)))) -
      Real.log 2 * piPrime (n : ℝ) =
      (((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1))).card : ℝ) +
      (∑ r ∈ Finset.Icc 1 M, (piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - piPrime ((n : ℝ) / (2 * (r : ℝ)))) -
        (∑ r ∈ Finset.Icc 1 M, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) * ((n : ℝ) / Real.log (n : ℝ))) +
      (∑ r ∈ Finset.Icc 1 M, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2) * ((n : ℝ) / Real.log (n : ℝ)) -
      Real.log 2 * (piPrime (n : ℝ) - (n : ℝ) / Real.log (n : ℝ)) := by ring
  rw [h_id]
  have h1 := abs_sub
    ((((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1))).card : ℝ) +
      (∑ r ∈ Finset.Icc 1 M, (piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - piPrime ((n : ℝ) / (2 * (r : ℝ)))) -
        (∑ r ∈ Finset.Icc 1 M, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) * ((n : ℝ) / Real.log (n : ℝ))) +
      (∑ r ∈ Finset.Icc 1 M, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2) * ((n : ℝ) / Real.log (n : ℝ)))
    (Real.log 2 * (piPrime (n : ℝ) - (n : ℝ) / Real.log (n : ℝ)))
  have h2 := abs_add_le
    ((((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1))).card : ℝ) +
      (∑ r ∈ Finset.Icc 1 M, (piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - piPrime ((n : ℝ) / (2 * (r : ℝ)))) -
        (∑ r ∈ Finset.Icc 1 M, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) * ((n : ℝ) / Real.log (n : ℝ))))
    ((∑ r ∈ Finset.Icc 1 M, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2) * ((n : ℝ) / Real.log (n : ℝ)))
  have h3 := abs_add_le
    (((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1))).card : ℝ)
    (∑ r ∈ Finset.Icc 1 M, (piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - piPrime ((n : ℝ) / (2 * (r : ℝ)))) -
      (∑ r ∈ Finset.Icc 1 M, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) * ((n : ℝ) / Real.log (n : ℝ)))
  have hlo_abs : |(((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1))).card : ℝ)| ≤
      (ε / 4) * ((n : ℝ) / Real.log (n : ℝ)) := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hlo_le
  calc |(((Podd n).filter (fun p : ℕ => (p : ℝ) ≤ (n : ℝ) / (2 * (M : ℝ) + 1))).card : ℝ) +
          (∑ r ∈ Finset.Icc 1 M, (piPrime ((n : ℝ) / (2 * (r : ℝ) - 1)) - piPrime ((n : ℝ) / (2 * (r : ℝ)))) -
            (∑ r ∈ Finset.Icc 1 M, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ)))) * ((n : ℝ) / Real.log (n : ℝ))) +
          (∑ r ∈ Finset.Icc 1 M, (1 / (2 * (r : ℝ) - 1) - 1 / (2 * (r : ℝ))) - Real.log 2) * ((n : ℝ) / Real.log (n : ℝ)) -
          Real.log 2 * (piPrime (n : ℝ) - (n : ℝ) / Real.log (n : ℝ))|
      ≤ (3 * ε / 4) * ((n : ℝ) / Real.log (n : ℝ)) := by
          linarith [h1, h2, h3, hlo_abs, hsum_err, halt_err, hpi_err]
    _ = ε * ((3 / 4 : ℝ) * ((n : ℝ) / Real.log (n : ℝ))) := by ring
    _ ≤ ε * piPrime (n : ℝ) := mul_le_mul_of_nonneg_left hpi_lo hε.le

end GrasGreenbergBrocard
