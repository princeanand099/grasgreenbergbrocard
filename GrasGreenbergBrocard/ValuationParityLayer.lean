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
    have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hm2 : (2 * ((m + 1 : ℕ) : ℝ) - 1) ≠ 0 := by
      have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
      linarith
    have hm3 : (2 * ((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have h21 : ((2 * m + 1 : ℕ) : ℝ) = 2 * ((m + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
    have h22 : ((2 * m + 2 : ℕ) : ℝ) = 2 * ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [h21, h22]
    field_simp [hm1, hm2, hm3]
    ring

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

end GrasGreenbergBrocard
