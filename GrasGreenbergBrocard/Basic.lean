import Mathlib

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false

/-!
# Core Definitions for GrasGreenbergBrocard (Sections 1.2, 1.4, and 2)

This module defines the fundamental arithmetic functions for the Brocard–Ramanujan
manuscript: `Podd`, `Peven`, `q_n` (`core(n!)`), `s_n`, `piPrime`, `thetaPrime`,
`eExp`, `S_odd`, `S_even`, `Delta_parity`, `Sigma_star_parity`, harmonic layers `I_j`,
and transition collars `C_r(n)`.
-/

noncomputable section

open Real Finset BigOperators

namespace GrasGreenbergBrocard

/-- `Podd n` is the finset of primes `p ≤ n` with odd `p`-adic valuation in `n!`. -/
def Podd (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (Nat.factorial n))

/-- `Peven n` is the finset of primes `p ≤ n` with even `p`-adic valuation in `n!`. -/
def Peven (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter (fun p => p.Prime ∧ 2 ∣ padicValNat p (Nat.factorial n))

/-- `q_n := core(n!) = ∏_{p ∈ Podd(n)} p`, the square-free part of `n!`. -/
def q_n (n : ℕ) : ℕ :=
  ∏ p ∈ Podd n, p

/-- `s_n := ∏_{p ≤ n} p^{⌊v_p(n!)/2⌋}`, the square-full root of `n!`. -/
def s_n (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p ^ (padicValNat p (Nat.factorial n) / 2)

/-- Prime counting function `π(x) = ∑_{p ≤ x} 1`. -/
def piPrime (x : ℝ) : ℝ :=
  (((Finset.Icc 2 (Nat.floor x)).filter Nat.Prime).card : ℝ)

/-- Chebyshev theta function `ϑ(x) = ∑_{p ≤ x} log p`. -/
def thetaPrime (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 (Nat.floor x)).filter Nat.Prime, Real.log (p : ℝ)

/-- Complex exponential `e(t) := exp(2π i t)`. -/
def eExp (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))

/-- Odd-valuation prime weight `S_odd(n)` over odd primes `3 ≤ p ≤ n` (eq. 2.1). -/
def S_odd (n : ℕ) : ℝ :=
  ∑ p ∈ (Podd n).filter (fun p => 3 ≤ p),
    (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)

/-- Even-valuation prime weight `S_even(n)` over odd primes `3 ≤ p ≤ n` (eq. 2.1). -/
def S_even (n : ℕ) : ℝ :=
  ∑ p ∈ (Peven n).filter (fun p => 3 ≤ p),
    (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)

/-- Parity discrepancy `Δ_parity(n) := S_even(n) - S_odd(n)` (eq. 2.2). -/
def Delta_parity (n : ℕ) : ℝ :=
  S_even n - S_odd n

/-- Small-prime valuation-parity sum `Σ*_parity(n)` over `3 ≤ p ≤ √n` (eq. 2.3). -/
def Sigma_star_parity (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
    ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1))

/-- Harmonic interval `I_j = (n / (j + 1), n / j]` for `j ≥ 1`. -/
def harmonicInterval (n j : ℕ) : Set ℝ :=
  Set.Ioc ((n : ℝ) / ((j : ℝ) + 1)) ((n : ℝ) / (j : ℝ))

/-- Basic factorization identity `n! = q_n * s_n^2`. -/
theorem factorial_eq_q_mul_s_sq (n : ℕ) : Nat.factorial n = q_n n * (s_n n) ^ 2 := by
  have hfac : Nat.factorial n ≠ 0 := Nat.factorial_ne_zero n
  have hq_ne : q_n n ≠ 0 := by
    unfold q_n Podd
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => (Finset.mem_filter.mp hp).2.1.ne_zero)
  have hs_ne : s_n n ≠ 0 := by
    unfold s_n
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero)
  apply Nat.eq_of_factorization_eq hfac (mul_ne_zero hq_ne (pow_ne_zero 2 hs_ne))
  intro p
  rw [Nat.factorization_mul hq_ne (pow_ne_zero 2 hs_ne), Nat.factorization_pow]
  by_cases hp : p.Prime
  · have hfv : (Nat.factorial n).factorization p = padicValNat p (Nat.factorial n) :=
      Nat.factorization_def (Nat.factorial n) hp
    have hq_val : (q_n n).factorization p = if p ∈ Podd n then 1 else 0 := by
      unfold q_n
      rw [Nat.factorization_prod (fun x hx => (Finset.mem_filter.mp hx).2.1.ne_zero)]
      simp only [Finset.sum_apply']
      split_ifs with hmem
      · rw [Finset.sum_eq_single p]
        · exact hp.factorization_self
        · intro x hx hne
          have hx_prime : x.Prime := (Finset.mem_filter.mp hx).2.1
          exact Nat.factorization_eq_zero_of_not_dvd
            (fun hdvd => hne ((Nat.prime_dvd_prime_iff_eq hp hx_prime).mp hdvd).symm)
        · intro hnot; exact absurd hmem hnot
      · refine Finset.sum_eq_zero (fun x hx => ?_)
        have hx_prime : x.Prime := (Finset.mem_filter.mp hx).2.1
        have hne : p ≠ x := fun h => hmem (h ▸ hx)
        exact Nat.factorization_eq_zero_of_not_dvd
          (fun hdvd => hne ((Nat.prime_dvd_prime_iff_eq hp hx_prime).mp hdvd))
    have hs_val : (s_n n).factorization p =
        if p ∈ (Finset.Icc 2 n).filter Nat.Prime then padicValNat p (Nat.factorial n) / 2 else 0 := by
      unfold s_n
      rw [Nat.factorization_prod (fun x hx => pow_ne_zero _ (Finset.mem_filter.mp hx).2.ne_zero)]
      simp only [Finset.sum_apply']
      split_ifs with hmem
      · rw [Finset.sum_eq_single p]
        · rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
            hp.factorization_self, mul_one]
        · intro x hx hne
          have hx_prime : x.Prime := (Finset.mem_filter.mp hx).2
          rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
          have hz : x.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
            (fun hdvd => hne ((Nat.prime_dvd_prime_iff_eq hp hx_prime).mp hdvd).symm)
          rw [hz, mul_zero]
        · intro hnot; exact absurd hmem hnot
      · refine Finset.sum_eq_zero (fun x hx => ?_)
        have hx_prime : x.Prime := (Finset.mem_filter.mp hx).2
        have hne : p ≠ x := fun h => hmem (h ▸ hx)
        rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
        have hz : x.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
          (fun hdvd => hne ((Nat.prime_dvd_prime_iff_eq hp hx_prime).mp hdvd))
        rw [hz, mul_zero]
    rw [hfv, Finsupp.add_apply, hq_val, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hs_val]
    by_cases hle : p ≤ n
    · have hp_mem : p ∈ (Finset.Icc 2 n).filter Nat.Prime :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hle⟩, hp⟩
      have hp_odd : p ∈ Podd n ↔ ¬ 2 ∣ padicValNat p (Nat.factorial n) := by
        unfold Podd
        simp [hp_mem, hp, hp.two_le, hle]
      by_cases hodd : 2 ∣ padicValNat p (Nat.factorial n)
      · have hnot : p ∉ Podd n := fun h => (hp_odd.mp h) hodd
        simp [hp_mem, hnot]
        omega
      · have hyes : p ∈ Podd n := hp_odd.mpr hodd
        simp [hp_mem, hyes]
        omega
    · have hnot1 : p ∉ Podd n := by
        unfold Podd
        simp [hle]
      have hnot2 : p ∉ (Finset.Icc 2 n).filter Nat.Prime := by
        simp [hle]
      have hzero : padicValNat p (Nat.factorial n) = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun hdvd => hle (hp.dvd_factorial.mp hdvd))
      simp [hnot1, hnot2, hzero]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- `Delta_parity n = ∑_{3 ≤ p ≤ n} (-1)^{v_p(n!)} v_p(n!) log p` (eq. 2.2). -/
theorem Delta_parity_eq_sum (n : ℕ) :
    Delta_parity n = ∑ p ∈ (Finset.Icc 3 n).filter Nat.Prime,
      (-1 : ℝ) ^ (padicValNat p (Nat.factorial n)) *
        (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
  unfold Delta_parity S_even S_odd Peven Podd
  have hsplit : (Finset.Icc 3 n).filter Nat.Prime =
      (((Finset.Icc 2 n).filter (fun p => p.Prime ∧ 2 ∣ padicValNat p (Nat.factorial n))).filter (fun p => 3 ≤ p)) ∪
      (((Finset.Icc 2 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (Nat.factorial n))).filter (fun p => 3 ≤ p)) := by
    ext p
    by_cases hp : p.Prime <;> by_cases hd : 2 ∣ padicValNat p (Nat.factorial n) <;>
      simp [hp, hd] <;> omega
  have hdisj : Disjoint
      (((Finset.Icc 2 n).filter (fun p => p.Prime ∧ 2 ∣ padicValNat p (Nat.factorial n))).filter (fun p => 3 ≤ p))
      (((Finset.Icc 2 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (Nat.factorial n))).filter (fun p => 3 ≤ p)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    exact hp2.1.2.2 hp1.1.2.2
  rw [hsplit, Finset.sum_union hdisj]
  have hev : ∑ p ∈ ((Finset.Icc 2 n).filter (fun p => p.Prime ∧ 2 ∣ padicValNat p (Nat.factorial n))).filter (fun p => 3 ≤ p),
      (-1 : ℝ) ^ (padicValNat p (Nat.factorial n)) * (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) =
      ∑ p ∈ ((Finset.Icc 2 n).filter (fun p => p.Prime ∧ 2 ∣ padicValNat p (Nat.factorial n))).filter (fun p => 3 ≤ p),
      (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have h2 : 2 ∣ padicValNat p (Nat.factorial n) := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
    obtain ⟨k, hk⟩ := h2
    rw [hk, pow_mul, neg_one_sq, one_pow, one_mul]
  have hod : ∑ p ∈ ((Finset.Icc 2 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (Nat.factorial n))).filter (fun p => 3 ≤ p),
      (-1 : ℝ) ^ (padicValNat p (Nat.factorial n)) * (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) =
      - ∑ p ∈ ((Finset.Icc 2 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (Nat.factorial n))).filter (fun p => 3 ≤ p),
      (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have h2 : ¬ 2 ∣ padicValNat p (Nat.factorial n) := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
    have hmod : padicValNat p (Nat.factorial n) % 2 = 1 :=
      Nat.mod_two_ne_zero.mp (fun h => h2 (Nat.dvd_of_mod_eq_zero h))
    have hpow : (-1 : ℝ) ^ (padicValNat p (Nat.factorial n)) = -1 := by
      rw [← Nat.div_add_mod (padicValNat p (Nat.factorial n)) 2, hmod,
        pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
    rw [hpow]
    ring
  rw [hev, hod]
  ring

end GrasGreenbergBrocard
