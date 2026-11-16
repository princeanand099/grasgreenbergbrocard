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
  (Finset.Icc 2 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p n !)

/-- `Peven n` is the finset of primes `p ≤ n` with even `p`-adic valuation in `n!`. -/
def Peven (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter (fun p => p.Prime ∧ 2 ∣ padicValNat p n !)

/-- `q_n := core(n!) = ∏_{p ∈ Podd(n)} p`, the square-free part of `n!`. -/
def q_n (n : ℕ) : ℕ :=
  ∏ p ∈ Podd n, p

/-- `s_n := ∏_{p ≤ n} p^{⌊v_p(n!)/2⌋}`, the square-full root of `n!`. -/
def s_n (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p ^ (padicValNat p n ! / 2)

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
  ∑ p ∈ (Podd n).filter (fun p => 3 ≤ p), (padicValNat p n ! : ℝ) * Real.log (p : ℝ)

/-- Even-valuation prime weight `S_even(n)` over odd primes `3 ≤ p ≤ n` (eq. 2.1). -/
def S_even (n : ℕ) : ℝ :=
  ∑ p ∈ (Peven n).filter (fun p => 3 ≤ p), (padicValNat p n ! : ℝ) * Real.log (p : ℝ)

/-- Parity discrepancy `Δ_parity(n) := S_even(n) - S_odd(n)` (eq. 2.2). -/
def Delta_parity (n : ℕ) : ℝ :=
  S_even n - S_odd n

/-- Small-prime valuation-parity sum `Σ*_parity(n)` over `3 ≤ p ≤ √n` (eq. 2.3). -/
def Sigma_star_parity (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime,
    ((-1 : ℝ) ^ (padicValNat p n ! - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1))

/-- Harmonic interval `I_j = (n / (j + 1), n / j]` for `j ≥ 1`. -/
def harmonicInterval (n j : ℕ) : Set ℝ :=
  Set.Ioc ((n : ℝ) / ((j : ℝ) + 1)) ((n : ℝ) / (j : ℝ))

/-- Basic factorization identity `n! = q_n * s_n^2`. -/
theorem factorial_eq_q_mul_s_sq (n : ℕ) : n ! = q_n n * (s_n n) ^ 2 := by
  have hfac : n ! ≠ 0 := Nat.factorial_ne_zero n
  rw [← Nat.factorization_prod_pow_eq_self hfac]
  unfold q_n s_n Podd
  have hsupp : (n !).factorization.support ⊆ (Finset.Icc 2 n).filter Nat.Prime := by
    intro p hp
    simp only [Finsupp.mem_support_iff, ne_eq] at hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by simpa [Nat.primeFactors] using hp)
    have hdvd : p ∣ n ! := Nat.dvd_of_mem_primeFactors (by simpa [Nat.primeFactors] using hp)
    have hle : p ≤ n := hprime.dvd_factorial.mp hdvd
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hprime.two_le, hle⟩, hprime⟩
  rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => by simp)]
  have hq : ∏ p ∈ ((Finset.Icc 2 n).filter Nat.Prime).filter (fun p => ¬ 2 ∣ padicValNat p n !), p =
      ∏ p ∈ (Finset.Icc 2 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p n !), p := by
    congr 1
    ext p
    simp [and_comm, and_assoc]
  rw [← hq, ← Finset.prod_pow]
  rw [← Finset.prod_filter_mul_prod_filter_not ((Finset.Icc 2 n).filter Nat.Prime)
    (fun p => ¬ 2 ∣ padicValNat p n !) (fun p => p ^ (n !).factorization p)]
  have h1 : ∏ p ∈ ((Finset.Icc 2 n).filter Nat.Prime).filter (fun p => ¬ 2 ∣ padicValNat p n !),
      p ^ (n !).factorization p =
    (∏ p ∈ ((Finset.Icc 2 n).filter Nat.Prime).filter (fun p => ¬ 2 ∣ padicValNat p n !), p) *
    (∏ p ∈ ((Finset.Icc 2 n).filter Nat.Prime).filter (fun p => ¬ 2 ∣ padicValNat p n !),
      (p ^ (padicValNat p n ! / 2)) ^ 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hprime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hodd : ¬ 2 ∣ padicValNat p n ! := (Finset.mem_filter.mp hp).2
    have hfv : (n !).factorization p = padicValNat p n ! := by
      haveI : Fact p.Prime := ⟨hprime⟩
      exact (padicValNat_def hfac).symm ▸ rfl
    rw [hfv, ← pow_mul, ← pow_succ']
    congr 1
    omega
  have h2 : ∏ p ∈ ((Finset.Icc 2 n).filter Nat.Prime).filter (fun p => ¬ ¬ 2 ∣ padicValNat p n !),
      p ^ (n !).factorization p =
    ∏ p ∈ ((Finset.Icc 2 n).filter Nat.Prime).filter (fun p => ¬ ¬ 2 ∣ padicValNat p n !),
      (p ^ (padicValNat p n ! / 2)) ^ 2 := by
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hprime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have heven : 2 ∣ padicValNat p n ! := not_not.mp (Finset.mem_filter.mp hp).2
    have hfv : (n !).factorization p = padicValNat p n ! := by
      haveI : Fact p.Prime := ⟨hprime⟩
      exact (padicValNat_def hfac).symm ▸ rfl
    rw [hfv, ← pow_mul]
    congr 1
    omega
  rw [h1, h2]
  have hsplit := Finset.prod_filter_mul_prod_filter_not ((Finset.Icc 2 n).filter Nat.Prime)
    (fun p => ¬ 2 ∣ padicValNat p n !) (fun p => (p ^ (padicValNat p n ! / 2)) ^ 2)
  linarith [mul_assoc (∏ p ∈ ((Finset.Icc 2 n).filter Nat.Prime).filter (fun p => ¬ 2 ∣ padicValNat p n !), p)
    (∏ p ∈ ((Finset.Icc 2 n).filter Nat.Prime).filter (fun p => ¬ 2 ∣ padicValNat p n !), (p ^ (padicValNat p n ! / 2)) ^ 2)
    (∏ p ∈ ((Finset.Icc 2 n).filter Nat.Prime).filter (fun p => ¬ ¬ 2 ∣ padicValNat p n !), (p ^ (padicValNat p n ! / 2)) ^ 2)]

/-- `Delta_parity n = ∑_{3 ≤ p ≤ n} (-1)^{v_p(n!)} v_p(n!) log p` (eq. 2.2). -/
theorem Delta_parity_eq_sum (n : ℕ) :
    Delta_parity n = ∑ p ∈ (Finset.Icc 3 n).filter Nat.Prime,
      (-1 : ℝ) ^ (padicValNat p n !) * (padicValNat p n ! : ℝ) * Real.log (p : ℝ) := by
  unfold Delta_parity S_even S_odd Peven Podd
  have hsplit : (Finset.Icc 3 n).filter Nat.Prime =
      (((Finset.Icc 2 n).filter (fun p => p.Prime ∧ 2 ∣ padicValNat p n !)).filter (fun p => 3 ≤ p)) ∪
      (((Finset.Icc 2 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p n !)).filter (fun p => 3 ≤ p)) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hdisj : Disjoint
      (((Finset.Icc 2 n).filter (fun p => p.Prime ∧ 2 ∣ padicValNat p n !)).filter (fun p => 3 ≤ p))
      (((Finset.Icc 2 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p n !)).filter (fun p => 3 ≤ p)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    exact hp2.1.2.2 hp1.1.2.2
  rw [hsplit, Finset.sum_union hdisj]
  have hev : ∑ p ∈ ((Finset.Icc 2 n).filter (fun p => p.Prime ∧ 2 ∣ padicValNat p n !)).filter (fun p => 3 ≤ p),
      (-1 : ℝ) ^ (padicValNat p n !) * (padicValNat p n ! : ℝ) * Real.log (p : ℝ) =
      ∑ p ∈ ((Finset.Icc 2 n).filter (fun p => p.Prime ∧ 2 ∣ padicValNat p n !)).filter (fun p => 3 ≤ p),
      (padicValNat p n ! : ℝ) * Real.log (p : ℝ) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have h2 : 2 ∣ padicValNat p n ! := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
    obtain ⟨k, hk⟩ := h2
    rw [hk, pow_mul, neg_one_sq, one_pow, one_mul]
  have hod : ∑ p ∈ ((Finset.Icc 2 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p n !)).filter (fun p => 3 ≤ p),
      (-1 : ℝ) ^ (padicValNat p n !) * (padicValNat p n ! : ℝ) * Real.log (p : ℝ) =
      - ∑ p ∈ ((Finset.Icc 2 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p n !)).filter (fun p => 3 ≤ p),
      (padicValNat p n ! : ℝ) * Real.log (p : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have h2 : ¬ 2 ∣ padicValNat p n ! := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
    have hmod : padicValNat p n ! % 2 = 1 := Nat.mod_two_ne_zero.mp (fun h => h2 (Nat.dvd_of_mod_eq_zero h))
    have hpow : (-1 : ℝ) ^ (padicValNat p n !) = -1 := by
      rw [← Nat.div_add_mod (padicValNat p n !) 2, hmod, pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
    rw [hpow]
    ring
  rw [hev, hod]
  ring

end GrasGreenbergBrocard
