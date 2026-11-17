import Mathlib
import GrasGreenbergBrocard.Basic

/-!
# Lemma 3.2: Chebyshev–Lucas Factorization and p-Adic Lifting the Exponent

Formalizes Section 3.1 (eqs. 3.1–3.3) of the manuscript completely without external axioms:
- `lucasX`, `lucasY`: the Lucas–Pell sequence `(X_r, Y_r)` defined by `(X₁ + Y₁√D)^r` in `Zsqrtd D`
- `chebyshevU_eval`: explicit binomial representation of `U_{k-1}(X₁)` (eq. 3.1)
- `lucasY_eq_mul_chebyshevU`: `Y_k = Y₁ * U_{k-1}(X₁)`
- `gcd_pell_chebyshevU_dvd`: `gcd(X₁^2 - 1, U_{k-1}(X₁)^2) ∣ k^2`
- `padicValInt_chebyshevU`: `v_p(U_{k-1}(X₁)) = v_p(k)` for `p ∣ D * Y₁` under `p ≠ 3 ∨ ¬ 3 ∣ k ∨ 3 ∣ Y₁` (eq. 3.2)
- `factorial_eq_q_n_mul_s_n_sq`: `n! = q_n * s_n^2`
- `padicValNat_pell_absorption`: `v_p(q_n * Y₁^2) = v_p(n!) - 2 * v_p(k)` for `p ∈ Podd(n) \ {3}` (eq. 3.3)
-/

namespace GrasGreenbergBrocard

open Finset

/-- The `X`-coordinate of `(X₁ + Y₁ √D)^r` in `ℤ[√D]`. -/
def lucasX (D X₁ Y₁ : ℤ) (r : ℕ) : ℤ :=
  ((⟨X₁, Y₁⟩ : Zsqrtd D) ^ r).re

/-- The `Y`-coordinate of `(X₁ + Y₁ √D)^r` in `ℤ[√D]`. -/
def lucasY (D X₁ Y₁ : ℤ) (r : ℕ) : ℤ :=
  ((⟨X₁, Y₁⟩ : Zsqrtd D) ^ r).im

/-- Explicit binomial expansion of `U_{k-1}(X₁)` when `X₁^2 - D * Y₁^2 = 1` (eq. 3.1). -/
def chebyshevU_eval (D X₁ Y₁ : ℤ) (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range ((k + 1) / 2),
    (Nat.choose k (2 * j + 1) : ℤ) * X₁ ^ (k - 1 - 2 * j) * (D * Y₁ ^ 2) ^ j

@[simp] private lemma zsqrtd_mul_re (D : ℤ) (x y : Zsqrtd D) :
    (x * y).re = x.re * y.re + D * x.im * y.im := by ring_nf; rfl

@[simp] private lemma zsqrtd_mul_im (D : ℤ) (x y : Zsqrtd D) :
    (x * y).im = x.re * y.im + x.im * y.re := by ring_nf; rfl

private lemma zsqrtd_base_pow_even (D : ℤ) (j : ℕ) :
    ((⟨0, 1⟩ : Zsqrtd D) ^ (2 * j)) = ⟨D ^ j, 0⟩ := by
  induction j with
  | zero => ext <;> simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add, ih, pow_two]
    ext <;> simp <;> ring

private lemma zsqrtd_base_pow_odd (D : ℤ) (j : ℕ) :
    ((⟨0, 1⟩ : Zsqrtd D) ^ (2 * j + 1)) = ⟨0, D ^ j⟩ := by
  rw [pow_succ, zsqrtd_base_pow_even]
  ext <;> simp

private lemma zsqrtd_split (D X₁ Y₁ : ℤ) :
    (⟨X₁, Y₁⟩ : Zsqrtd D) = (⟨Y₁, 0⟩ : Zsqrtd D) * ⟨0, 1⟩ + (⟨X₁, 0⟩ : Zsqrtd D) := by
  ext <;> simp

private lemma zsqrtd_int_pow (D a : ℤ) (m : ℕ) :
    ((⟨a, 0⟩ : Zsqrtd D) ^ m) = ⟨a ^ m, 0⟩ := by
  induction m with
  | zero => ext <;> simp
  | succ m ih =>
    rw [pow_succ, ih]
    ext <;> simp [pow_succ]

private lemma zsqrtd_mul_int_base_pow (D Y₁ : ℤ) (i : ℕ) :
    ((⟨Y₁, 0⟩ : Zsqrtd D) * ⟨0, 1⟩) ^ i = ⟨Y₁ ^ i, 0⟩ * (⟨0, 1⟩ : Zsqrtd D) ^ i := by
  rw [mul_pow, zsqrtd_int_pow]

/-- **Equation (3.1) / Lemma 3.2 factorization**: `Y_k = Y₁ * U_{k-1}(X₁)`. -/
theorem lucasY_eq_mul_chebyshevU (D X₁ Y₁ : ℤ) (k : ℕ) :
    lucasY D X₁ Y₁ k = Y₁ * chebyshevU_eval D X₁ Y₁ k := by
  unfold lucasY chebyshevU_eval
  rw [zsqrtd_split D X₁ Y₁]
  have hcomm : Commute ((⟨Y₁, 0⟩ : Zsqrtd D) * ⟨0, 1⟩) (⟨X₁, 0⟩ : Zsqrtd D) :=
    Commute.all _ _
  rw [hcomm.add_pow]
  have him_sum : ∀ s : Finset ℕ, (∑ i ∈ s,
      ((⟨Y₁, 0⟩ : Zsqrtd D) * ⟨0, 1⟩) ^ i * (⟨X₁, 0⟩ : Zsqrtd D) ^ (k - i) *
        ((Nat.choose k i : ℕ) : Zsqrtd D)).im =
      ∑ i ∈ s, (((⟨Y₁, 0⟩ : Zsqrtd D) * ⟨0, 1⟩) ^ i * (⟨X₁, 0⟩ : Zsqrtd D) ^ (k - i) *
        ((Nat.choose k i : ℕ) : Zsqrtd D)).im := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.sum_insert ha, ih]
  rw [him_sum]
  have hcast : ∀ i : ℕ, ((Nat.choose k i : ℕ) : Zsqrtd D) = ⟨(Nat.choose k i : ℤ), 0⟩ := by
    intro i; ext <;> simp
  simp_rw [hcast, zsqrtd_int_pow, zsqrtd_mul_int_base_pow]
  have hterm_even : ∀ j : ℕ,
      (⟨Y₁ ^ (2 * j), 0⟩ * (⟨0, 1⟩ : Zsqrtd D) ^ (2 * j) *
        ⟨X₁ ^ (k - 2 * j), 0⟩ * ⟨(Nat.choose k (2 * j) : ℤ), 0⟩).im = 0 := by
    intro j
    rw [zsqrtd_base_pow_even]
    simp
  have hterm_odd : ∀ j : ℕ, 2 * j + 1 ≤ k →
      (⟨Y₁ ^ (2 * j + 1), 0⟩ * (⟨0, 1⟩ : Zsqrtd D) ^ (2 * j + 1) *
        ⟨X₁ ^ (k - (2 * j + 1)), 0⟩ * ⟨(Nat.choose k (2 * j + 1) : ℤ), 0⟩).im =
      Y₁ * ((Nat.choose k (2 * j + 1) : ℤ) * X₁ ^ (k - 1 - 2 * j) * (D * Y₁ ^ 2) ^ j) := by
    intro j hj
    rw [zsqrtd_base_pow_odd]
    simp only [zsqrtd_mul_im, zsqrtd_mul_re]
    rw [show k - (2 * j + 1) = k - 1 - 2 * j by omega]
    rw [pow_succ', mul_pow, show (Y₁ ^ 2) ^ j = Y₁ ^ (2 * j) by rw [← pow_mul]]
    ring
  have hsum_split :
      (∑ i ∈ Finset.range (k + 1),
        (⟨Y₁ ^ i, 0⟩ * (⟨0, 1⟩ : Zsqrtd D) ^ i *
          ⟨X₁ ^ (k - i), 0⟩ * ⟨(Nat.choose k i : ℤ), 0⟩).im) =
      ∑ j ∈ Finset.range ((k + 1) / 2),
        (⟨Y₁ ^ (2 * j + 1), 0⟩ * (⟨0, 1⟩ : Zsqrtd D) ^ (2 * j + 1) *
          ⟨X₁ ^ (k - (2 * j + 1)), 0⟩ * ⟨(Nat.choose k (2 * j + 1) : ℤ), 0⟩).im := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (k + 1)) (fun i => i % 2 = 1)]
    have heven_zero :
        ∑ i ∈ (Finset.range (k + 1)).filter (fun i => ¬ i % 2 = 1),
          (⟨Y₁ ^ i, 0⟩ * (⟨0, 1⟩ : Zsqrtd D) ^ i *
            ⟨X₁ ^ (k - i), 0⟩ * ⟨(Nat.choose k i : ℤ), 0⟩).im = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hmod : i % 2 = 0 := by
        have := (Finset.mem_filter.mp hi).2
        omega
      rcases Nat.even_iff.mpr hmod with ⟨j, rfl⟩
      rw [show j + j = 2 * j by omega]
      exact hterm_even j
    rw [heven_zero, add_zero]
    apply Finset.sum_bij (fun i _ => i / 2)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_range] at ha hb
      omega
    · intro j hj
      refine ⟨2 * j + 1, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      omega
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      have hi_eq : 2 * (i / 2) + 1 = i := by omega
      rw [hi_eq]
  rw [hsum_split, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  exact hterm_odd j (by omega)

/-- Helper: `chebyshevU_eval D X₁ Y₁ k ≡ k * X₁^(k-1) [ZMOD D * Y₁^2]`. -/
theorem chebyshevU_eval_mod_M (D X₁ Y₁ : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    (D * Y₁ ^ 2) ∣ (chebyshevU_eval D X₁ Y₁ k - (k : ℤ) * X₁ ^ (k - 1)) := by
  unfold chebyshevU_eval
  have h0_mem : 0 ∈ Finset.range ((k + 1) / 2) := by
    rw [Finset.mem_range]; omega
  rw [← Finset.add_sum_erase _ _ h0_mem]
  have h0_val : (Nat.choose k (2 * 0 + 1) : ℤ) * X₁ ^ (k - 1 - 2 * 0) * (D * Y₁ ^ 2) ^ 0 =
      (k : ℤ) * X₁ ^ (k - 1) := by
    simp
  rw [h0_val, add_sub_cancel_left]
  apply Finset.dvd_sum
  intro j hj
  have hj_pos : 1 ≤ j := by
    have := Finset.mem_erase.mp hj
    omega
  refine ⟨(Nat.choose k (2 * j + 1) : ℤ) * X₁ ^ (k - 1 - 2 * j) * (D * Y₁ ^ 2) ^ (j - 1), ?_⟩
  have hj_eq : (D * Y₁ ^ 2) ^ j = (D * Y₁ ^ 2) * (D * Y₁ ^ 2) ^ (j - 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ']
  rw [hj_eq]
  ring

/-- **Lemma 3.2 (gcd divisibility)**: `gcd(X₁^2 - 1, U_{k-1}(X₁)^2)` divides `k^2`
whenever `X₁^2 - D * Y₁^2 = 1`. -/
theorem gcd_pell_chebyshevU_dvd (D X₁ Y₁ : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (hpell : X₁ ^ 2 - D * Y₁ ^ 2 = 1) :
    Int.gcd (X₁ ^ 2 - 1) ((chebyshevU_eval D X₁ Y₁ k) ^ 2) ∣ k ^ 2 := by
  have hM : X₁ ^ 2 - 1 = D * Y₁ ^ 2 := by linarith
  set U := chebyshevU_eval D X₁ Y₁ k
  set M := D * Y₁ ^ 2
  have hdvd_U : (Int.gcd M (U ^ 2) : ℤ) ∣ (k : ℤ) ^ 2 * (X₁ ^ (k - 1)) ^ 2 := by
    have h1 : (Int.gcd M (U ^ 2) : ℤ) ∣ M := Int.gcd_dvd_left M (U ^ 2)
    have h2 : (Int.gcd M (U ^ 2) : ℤ) ∣ U ^ 2 := Int.gcd_dvd_right M (U ^ 2)
    have h3 : M ∣ U - (k : ℤ) * X₁ ^ (k - 1) := chebyshevU_eval_mod_M D X₁ Y₁ k hk
    have h4 : (Int.gcd M (U ^ 2) : ℤ) ∣ U - (k : ℤ) * X₁ ^ (k - 1) := dvd_trans h1 h3
    have h5 : (Int.gcd M (U ^ 2) : ℤ) ∣ U ^ 2 - ((k : ℤ) * X₁ ^ (k - 1)) ^ 2 := by
      have hid : U ^ 2 - ((k : ℤ) * X₁ ^ (k - 1)) ^ 2 =
          (U - (k : ℤ) * X₁ ^ (k - 1)) * (U + (k : ℤ) * X₁ ^ (k - 1)) := by ring
      rw [hid]
      exact dvd_mul_of_dvd_left h4 _
    have h6 : (Int.gcd M (U ^ 2) : ℤ) ∣ ((k : ℤ) * X₁ ^ (k - 1)) ^ 2 := by
      have := dvd_sub h2 h5
      simpa using this
    simpa [mul_pow] using h6
  have hcop : Nat.Coprime (Int.gcd M (U ^ 2)) ((X₁ ^ (k - 1)).natAbs ^ 2) := by
    have hcop1 : IsCoprime M X₁ := ⟨-1, X₁, by linarith⟩
    have hcop2 : IsCoprime (Int.gcd M (U ^ 2) : ℤ) X₁ := by
      rcases hcop1 with ⟨a, b, hab⟩
      obtain ⟨t, ht⟩ := Int.gcd_dvd_left M (U ^ 2)
      have h_eq : a * M = a * t * (Int.gcd M (U ^ 2) : ℤ) := by
        conv_lhs => rw [ht]
        ring
      exact ⟨a * t, b, by linarith⟩
    have hcop3 : IsCoprime (Int.gcd M (U ^ 2) : ℤ) (X₁ ^ (k - 1)) :=
      hcop2.pow_right
    have hcop4 : Nat.Coprime (Int.gcd M (U ^ 2)) (X₁ ^ (k - 1)).natAbs := by
      have h3 : IsCoprime ((Int.gcd M (U ^ 2) : ℕ) : ℤ) ((X₁ ^ (k - 1)).natAbs : ℤ) := by
        have h3' := hcop3.abs_right
        rw [Int.abs_eq_natAbs] at h3'
        exact h3'
      exact Int.isCoprime_iff_nat_coprime.mp h3
    exact hcop4.pow_right 2
  have hdvd_nat : Int.gcd M (U ^ 2) ∣ k ^ 2 * (X₁ ^ (k - 1)).natAbs ^ 2 := by
    rw [← Int.natCast_dvd_natCast]
    push_cast
    rw [sq_abs]
    exact hdvd_U
  rw [hM]
  exact hcop.dvd_of_dvd_mul_right hdvd_nat

private lemma five_pow_gt_two_mul_add_one (j : ℕ) (hj : 1 ≤ j) : 2 * j + 1 < 5 ^ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hj_pos
    · norm_num
    · have hih := ih hj_pos
      calc 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
        _ < 5 ^ j + 2 := by omega
        _ ≤ 5 ^ j * 5 := by omega
        _ = 5 ^ (j + 1) := (pow_succ 5 j).symm

private lemma three_pow_gt_two_mul_add_one (j : ℕ) (hj : 2 ≤ j) : 2 * j + 1 < 3 ^ j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hj with h2 | hj_gt
    · have : j = 1 := by omega
      subst this
      norm_num
    · have hih := ih (by omega)
      calc 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
        _ < 3 ^ j + 2 := by omega
        _ ≤ 3 ^ j * 3 := by omega
        _ = 3 ^ (j + 1) := (pow_succ 3 j).symm

private lemma three_pow_two_mul_gt (j : ℕ) (hj : 1 ≤ j) : 2 * j + 1 < 3 ^ (2 * j) := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hj_pos
    · norm_num
    · have hih := ih hj_pos
      calc 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
        _ < 3 ^ (2 * j) + 2 := by omega
        _ ≤ 3 ^ (2 * j) * 9 := by omega
        _ = 3 ^ (2 * (j + 1)) := by rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]; norm_num

private lemma mul_choose_eq_choose_mul (k j : ℕ) (hj : 2 * j + 1 ≤ k) :
    (2 * j + 1) * Nat.choose k (2 * j + 1) = k * Nat.choose (k - 1) (2 * j) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial hj
  have h2 := Nat.choose_mul_factorial_mul_factorial (show 2 * j ≤ k - 1 by omega)
  have hfac_k : Nat.factorial k = k * Nat.factorial (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, Nat.factorial_succ]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hfac_2j : Nat.factorial (2 * j + 1) = (2 * j + 1) * Nat.factorial (2 * j) :=
    Nat.factorial_succ (2 * j)
  have hsub : k - 1 - 2 * j = k - (2 * j + 1) := by omega
  rw [hsub] at h2
  have hpos : 0 < Nat.factorial (2 * j) * Nat.factorial (k - (2 * j + 1)) :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (2 * j + 1) * Nat.choose k (2 * j + 1) *
        (Nat.factorial (2 * j) * Nat.factorial (k - (2 * j + 1)))
      = Nat.choose k (2 * j + 1) * ((2 * j + 1) * Nat.factorial (2 * j)) *
          Nat.factorial (k - (2 * j + 1)) := by ring
    _ = Nat.choose k (2 * j + 1) * Nat.factorial (2 * j + 1) *
          Nat.factorial (k - (2 * j + 1)) := by rw [← hfac_2j]
    _ = Nat.factorial k := h1
    _ = k * Nat.factorial (k - 1) := hfac_k
    _ = k * (Nat.choose (k - 1) (2 * j) * Nat.factorial (2 * j) *
          Nat.factorial (k - (2 * j + 1))) := by rw [← h2]
    _ = k * Nat.choose (k - 1) (2 * j) *
          (Nat.factorial (2 * j) * Nat.factorial (k - (2 * j + 1))) := by ring

private lemma pow_dvd_choose_mul_M {p k j : ℕ} {M : ℤ}
    (hp : p.Prime) (hk : 1 ≤ k) (hj1 : 1 ≤ j) (hj2 : 2 * j + 1 ≤ k)
    (hpM : (p : ℤ) ∣ M)
    (hcond : p ≠ 3 ∨ ¬ 3 ∣ k ∨ (3 : ℤ) ^ 2 ∣ M) :
    (p : ℤ) ^ (padicValNat p k + 1) ∣ (Nat.choose k (2 * j + 1) : ℤ) * M ^ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hspec : p = 3 ∧ ¬ 3 ∣ k ∧ j = 1
  · rcases hspec with ⟨rfl, h3k, rfl⟩
    have hv0 : padicValNat 3 k = 0 := padicValNat.eq_zero_of_not_dvd h3k
    rw [hv0, zero_add, pow_one, pow_one]
    exact dvd_mul_of_dvd_right hpM _
  have hM_dvd : (p : ℤ) ^ (padicValNat p (2 * j + 1) + 1) ∣ M ^ j := by
    have hv_le : p ^ padicValNat p (2 * j + 1) ≤ 2 * j + 1 :=
      Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have hpow_gt : padicValNat p (2 * j + 1) + 1 ≤ (if p = 3 ∧ (3 : ℤ) ^ 2 ∣ M then 2 * j else j) := by
      split_ifs with h3m
      · have hgt : 2 * j + 1 < 3 ^ (2 * j) := three_pow_two_mul_gt j hj1
        have hlt : p ^ padicValNat p (2 * j + 1) < p ^ (2 * j) := by
          calc p ^ padicValNat p (2 * j + 1) ≤ 2 * j + 1 := hv_le
            _ < 3 ^ (2 * j) := hgt
            _ = p ^ (2 * j) := by rw [h3m.1]
        exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
      · by_cases hp2 : p = 2
        · subst hp2
          have hodd : ¬ 2 ∣ (2 * j + 1) := by omega
          rw [padicValNat.eq_zero_of_not_dvd hodd]
          omega
        · by_cases hp3 : p = 3
          · subst hp3
            have hj2_ge : 2 ≤ j := by
              rcases hcond with hne | h3k | h3m2
              · contradiction
              · by_contra hlt
                have hj_eq : j = 1 := by omega
                exact hspec ⟨rfl, h3k, hj_eq⟩
              · exact absurd ⟨rfl, h3m2⟩ h3m
            have hgt : 2 * j + 1 < 3 ^ j := three_pow_gt_two_mul_add_one j hj2_ge
            have hlt : 3 ^ padicValNat 3 (2 * j + 1) < 3 ^ j := lt_of_le_of_lt hv_le hgt
            exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
          · have hp4 : p ≠ 4 := fun h => by subst h; norm_num at hp
            have hp5 : 5 ≤ p := by
              have := hp.two_le
              omega
            have h5j : 2 * j + 1 < p ^ j :=
              lt_of_lt_of_le (five_pow_gt_two_mul_add_one j hj1) (Nat.pow_le_pow_left (by omega) j)
            have hlt : p ^ padicValNat p (2 * j + 1) < p ^ j := lt_of_le_of_lt hv_le h5j
            exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    split_ifs at hpow_gt with h3m
    · have h3M2 : (p : ℤ) ^ 2 ∣ M := by rw [h3m.1]; exact h3m.2
      have hpow2 : (p : ℤ) ^ (2 * j) ∣ M ^ j := by
        rw [pow_mul]
        exact pow_dvd_pow_of_dvd h3M2 j
      exact dvd_trans (pow_dvd_pow (p : ℤ) hpow_gt) hpow2
    · have hpowj : (p : ℤ) ^ j ∣ M ^ j := pow_dvd_pow_of_dvd hpM j
      exact dvd_trans (pow_dvd_pow (p : ℤ) hpow_gt) hpowj
  have hchoose_eq : (2 * j + 1) * Nat.choose k (2 * j + 1) = k * Nat.choose (k - 1) (2 * j) :=
    mul_choose_eq_choose_mul k j hj2
  set a := padicValNat p (2 * j + 1)
  set b := padicValNat p k
  obtain ⟨u, hu_eq, hu_ndvd⟩ : ∃ u : ℕ, 2 * j + 1 = p ^ a * u ∧ ¬ p ∣ u := by
    refine ⟨(2 * j + 1) / p ^ a, (Nat.mul_div_cancel' pow_padicValNat_dvd).symm, fun hdvd => ?_⟩
    have hpow_dvd : p ^ (a + 1) ∣ 2 * j + 1 := by
      rw [pow_succ, mul_comm]
      calc p * p ^ a ∣ ((2 * j + 1) / p ^ a) * p ^ a := Nat.mul_dvd_mul_right hdvd (p ^ a)
        _ = p ^ a * ((2 * j + 1) / p ^ a) := mul_comm _ _
        _ = 2 * j + 1 := by dsimp only [a]; exact (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
    have hle := (padicValNat_dvd_iff_le (by omega : 2 * j + 1 ≠ 0)).mp hpow_dvd
    dsimp only [a] at hle
    omega
  obtain ⟨k', hk'_eq⟩ : ∃ k' : ℕ, k = p ^ b * k' :=
    ⟨k / p ^ b, (Nat.mul_div_cancel' pow_padicValNat_dvd).symm⟩
  obtain ⟨m', hm'_eq⟩ : ∃ m' : ℤ, M ^ j = (p : ℤ) ^ (a + 1) * m' := hM_dvd
  have hprod : (p : ℤ) ^ a * (u : ℤ) * ((Nat.choose k (2 * j + 1) : ℤ) * M ^ j) =
      (p : ℤ) ^ a * ((p : ℤ) ^ (b + 1) * ((k' : ℤ) * (Nat.choose (k - 1) (2 * j) : ℤ) * m')) := by
    have hcz : ((2 * j + 1 : ℕ) : ℤ) * (Nat.choose k (2 * j + 1) : ℤ) =
        (k : ℤ) * (Nat.choose (k - 1) (2 * j) : ℤ) := by
      exact_mod_cast hchoose_eq
    have hu_z : (p : ℤ) ^ a * (u : ℤ) = ((2 * j + 1 : ℕ) : ℤ) := by
      exact_mod_cast hu_eq.symm
    calc (p : ℤ) ^ a * (u : ℤ) * ((Nat.choose k (2 * j + 1) : ℤ) * M ^ j)
        = ((p : ℤ) ^ a * (u : ℤ)) * (Nat.choose k (2 * j + 1) : ℤ) * M ^ j := by ring
      _ = ((k : ℤ) * (Nat.choose (k - 1) (2 * j) : ℤ)) * M ^ j := by rw [hu_z, hcz]
      _ = ((p ^ b * k' : ℕ) : ℤ) * (Nat.choose (k - 1) (2 * j) : ℤ) * ((p : ℤ) ^ (a + 1) * m') := by
          rw [← hk'_eq, hm'_eq]
      _ = (p : ℤ) ^ a * ((p : ℤ) ^ (b + 1) * ((k' : ℤ) * (Nat.choose (k - 1) (2 * j) : ℤ) * m')) := by
          push_cast; rw [pow_succ, pow_succ]; ring
  have hpa_ne : (p : ℤ) ^ a ≠ 0 := pow_ne_zero a (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hcancel : (u : ℤ) * ((Nat.choose k (2 * j + 1) : ℤ) * M ^ j) =
      (p : ℤ) ^ (b + 1) * ((k' : ℤ) * (Nat.choose (k - 1) (2 * j) : ℤ) * m') := by
    apply mul_left_cancel₀ hpa_ne
    linarith
  have hdvd_u : (p : ℤ) ^ (b + 1) ∣ (u : ℤ) * ((Nat.choose k (2 * j + 1) : ℤ) * M ^ j) :=
    ⟨_, hcancel⟩
  have hcop : IsCoprime ((p : ℤ) ^ (b + 1)) (u : ℤ) := by
    have hcop_nat : Nat.Coprime (p ^ (b + 1)) u :=
      (hp.coprime_iff_not_dvd.mpr hu_ndvd).pow_left (b + 1)
    exact_mod_cast hcop_nat.isCoprime
  exact hcop.dvd_of_dvd_mul_left hdvd_u

/-- **Equation (3.2) / Lemma 3.2**: For every prime `p` dividing `D * Y₁` with `X₁^2 - D * Y₁^2 = 1`
and `p ≠ 3 ∨ ¬ 3 ∣ k ∨ 3 ∣ Y₁`, `v_p(U_{k-1}(X₁)) = v_p(k)`. -/
theorem padicValInt_chebyshevU {D X₁ Y₁ : ℤ} {k p : ℕ}
    (hk : 1 ≤ k) (hp : p.Prime) (hpell : X₁ ^ 2 - D * Y₁ ^ 2 = 1)
    (hpDY : (p : ℤ) ∣ D * Y₁)
    (hcond : p ≠ 3 ∨ ¬ 3 ∣ k ∨ (3 : ℤ) ∣ Y₁) :
    padicValInt p (chebyshevU_eval D X₁ Y₁ k) = padicValNat p k := by
  haveI : Fact p.Prime := ⟨hp⟩
  set M := D * Y₁ ^ 2
  have hpM : (p : ℤ) ∣ M := by
    rcases (Int.Prime.dvd_mul' hp hpDY) with hD | hY
    · exact dvd_mul_of_dvd_left hD _
    · exact dvd_mul_of_dvd_right (dvd_pow hY (by norm_num)) _
  have hpX : ¬ (p : ℤ) ∣ X₁ := by
    intro hX
    have h1 : (p : ℤ) ∣ X₁ ^ 2 - M := dvd_sub (dvd_pow hX (by norm_num)) hpM
    rw [hpell] at h1
    exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp h1)
  have hcondM : p ≠ 3 ∨ ¬ 3 ∣ k ∨ (3 : ℤ) ^ 2 ∣ M := by
    rcases hcond with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd h3 2) D))
  have h0_mem : 0 ∈ Finset.range ((k + 1) / 2) := by
    rw [Finset.mem_range]; omega
  have hsplit : chebyshevU_eval D X₁ Y₁ k =
      (k : ℤ) * X₁ ^ (k - 1) +
      ∑ j ∈ (Finset.range ((k + 1) / 2)).erase 0,
        (Nat.choose k (2 * j + 1) : ℤ) * X₁ ^ (k - 1 - 2 * j) * M ^ j := by
    unfold chebyshevU_eval
    rw [← Finset.add_sum_erase _ _ h0_mem]
    simp [M]
  set v := padicValNat p k
  have htail_dvd : (p : ℤ) ^ (v + 1) ∣
      ∑ j ∈ (Finset.range ((k + 1) / 2)).erase 0,
        (Nat.choose k (2 * j + 1) : ℤ) * X₁ ^ (k - 1 - 2 * j) * M ^ j := by
    apply Finset.dvd_sum
    intro j hj
    have hj1 : 1 ≤ j := by
      have := Finset.mem_erase.mp hj
      omega
    have hj2 : 2 * j + 1 ≤ k := by
      have := (Finset.mem_erase.mp hj).2
      rw [Finset.mem_range] at this
      omega
    have hd := pow_dvd_choose_mul_M hp hk hj1 hj2 hpM hcondM
    rw [mul_assoc, mul_comm (X₁ ^ (k - 1 - 2 * j)) (M ^ j), ← mul_assoc]
    exact dvd_mul_of_dvd_left hd _
  have hhead_dvd : (p : ℤ) ^ v ∣ (k : ℤ) * X₁ ^ (k - 1) := by
    have hk_dvd : p ^ v ∣ k := pow_padicValNat_dvd
    exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hk_dvd) _
  have hhead_ndvd : ¬ (p : ℤ) ^ (v + 1) ∣ (k : ℤ) * X₁ ^ (k - 1) := by
    intro h
    have hpX_nat : ¬ p ∣ X₁.natAbs := fun hd => hpX (Int.natCast_dvd.mpr hd)
    have hcop_nat : Nat.Coprime (p ^ (v + 1)) (X₁.natAbs ^ (k - 1)) :=
      ((hp.coprime_iff_not_dvd.mpr hpX_nat).pow_left (v + 1)).pow_right (k - 1)
    have h_nat : p ^ (v + 1) ∣ k * X₁.natAbs ^ (k - 1) := by
      have h1 : (((p ^ (v + 1) : ℕ) : ℤ)) ∣ (k : ℤ) * X₁ ^ (k - 1) := by
        push_cast; exact h
      have h2 := Int.natCast_dvd.mp h1
      simpa [Int.natAbs_mul, Int.natAbs_pow] using h2
    have hk_dvd1_nat : p ^ (v + 1) ∣ k := hcop_nat.dvd_of_dvd_mul_right h_nat
    have hle := (padicValNat_dvd_iff_le (by omega : k ≠ 0)).mp hk_dvd1_nat
    omega
  have hU_dvd : (p : ℤ) ^ v ∣ chebyshevU_eval D X₁ Y₁ k := by
    rw [hsplit]
    exact dvd_add hhead_dvd (dvd_trans (pow_dvd_pow (p : ℤ) (Nat.le_succ v)) htail_dvd)
  have hU_ndvd : ¬ (p : ℤ) ^ (v + 1) ∣ chebyshevU_eval D X₁ Y₁ k := by
    intro h
    rw [hsplit] at h
    exact hhead_ndvd ((dvd_add_left htail_dvd).mp h)
  have hU_ne : chebyshevU_eval D X₁ Y₁ k ≠ 0 := by
    intro h0
    rw [h0] at hU_ndvd
    exact hU_ndvd (dvd_zero _)
  unfold padicValInt
  have hU_natAbs_ne : (chebyshevU_eval D X₁ Y₁ k).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hU_ne
  have h1 : p ^ v ∣ (chebyshevU_eval D X₁ Y₁ k).natAbs := by
    have h1' : (((p ^ v : ℕ) : ℤ)) ∣ chebyshevU_eval D X₁ Y₁ k := by push_cast; exact hU_dvd
    exact Int.natCast_dvd.mp h1'
  have h2 : ¬ p ^ (v + 1) ∣ (chebyshevU_eval D X₁ Y₁ k).natAbs := by
    intro h
    apply hU_ndvd
    have h2' := Int.natCast_dvd.mpr h
    push_cast at h2'
    exact h2'
  have hle1 := (padicValNat_dvd_iff_le hU_natAbs_ne).mp h1
  have hlt2 : padicValNat p (chebyshevU_eval D X₁ Y₁ k).natAbs < v + 1 := by
    by_contra hge
    push_neg at hge
    exact h2 ((padicValNat_dvd_iff_le hU_natAbs_ne).mpr hge)
  omega

/-- Canonical square-free / square factorization `n! = q_n * s_n^2` (eq. 1.4 / 2.1). -/
theorem factorial_eq_q_n_mul_s_n_sq (n : ℕ) : Nat.factorial n = q_n n * (s_n n) ^ 2 := by
  have hq_ne : q_n n ≠ 0 := by
    unfold q_n
    exact Finset.prod_ne_zero_iff.mpr (fun q hq => (Finset.mem_filter.mp hq).2.1.ne_zero)
  have hs_ne : s_n n ≠ 0 := by
    unfold s_n
    exact Finset.prod_ne_zero_iff.mpr (fun q hq => pow_ne_zero _ (Finset.mem_filter.mp hq).2.ne_zero)
  apply Nat.eq_of_factorization_eq (Nat.factorial_ne_zero n) (mul_ne_zero hq_ne (pow_ne_zero 2 hs_ne))
  intro q
  rw [Nat.factorization_mul hq_ne (pow_ne_zero 2 hs_ne), Nat.factorization_pow]
  unfold q_n s_n Podd
  rw [Nat.factorization_prod (fun r hr => (Finset.mem_filter.mp hr).2.1.ne_zero)]
  rw [Nat.factorization_prod (fun r hr => pow_ne_zero _ (Finset.mem_filter.mp hr).2.ne_zero)]
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  by_cases hq_mem : q ∈ (Finset.Icc 2 n).filter Nat.Prime
  · have hq_pr : q.Prime := (Finset.mem_filter.mp hq_mem).2
    haveI : Fact q.Prime := ⟨hq_pr⟩
    have hs_sum :
        (∑ x ∈ (Finset.Icc 2 n).filter Nat.Prime,
          (padicValNat x (Nat.factorial n) / 2) * x.factorization q) =
        padicValNat q (Nat.factorial n) / 2 := by
      rw [Finset.sum_eq_single q]
      · rw [hq_pr.factorization_self, mul_one]
      · intro r hr hrq
        have hr_pr : r.Prime := (Finset.mem_filter.mp hr).2
        have hnd : ¬ q ∣ r := fun h => hrq ((Nat.prime_dvd_prime_iff_eq hq_pr hr_pr).mp h).symm
        rw [Nat.factorization_eq_zero_of_not_dvd hnd, mul_zero]
      · intro habs; exact absurd hq_mem habs
    rw [hs_sum]
    by_cases hq_odd : ¬ 2 ∣ padicValNat q (Nat.factorial n)
    · have hmem1 : q ∈ (Finset.Icc 2 n).filter (fun r => r.Prime ∧ padicValNat r (Nat.factorial n) % 2 = 1) :=
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq_mem).1, hq_pr, by omega⟩
      have hq_sum :
          (∑ x ∈ (Finset.Icc 2 n).filter (fun r => r.Prime ∧ padicValNat r (Nat.factorial n) % 2 = 1),
            x.factorization q) = 1 := by
        rw [Finset.sum_eq_single q]
        · exact hq_pr.factorization_self
        · intro r hr hrq
          have hr_pr : r.Prime := (Finset.mem_filter.mp hr).2.1
          have hnd : ¬ q ∣ r := fun h => hrq ((Nat.prime_dvd_prime_iff_eq hq_pr hr_pr).mp h).symm
          exact Nat.factorization_eq_zero_of_not_dvd hnd
        · intro habs; exact absurd hmem1 habs
      have hq_sum' :
          (∑ x ∈ (Finset.Icc 2 n).filter (fun r => r.Prime ∧ ¬ 2 ∣ padicValNat r (Nat.factorial n)),
            x.factorization q) = 1 := by
        convert hq_sum using 2
        ext r; simp [Nat.dvd_iff_mod_eq_zero]
      rw [hq_sum', Nat.factorization_def _ hq_pr]
      omega
    · have hq_sum :
          (∑ x ∈ (Finset.Icc 2 n).filter (fun r => r.Prime ∧ ¬ 2 ∣ padicValNat r (Nat.factorial n)),
            x.factorization q) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        have hr_pr : r.Prime := (Finset.mem_filter.mp hr).2.1
        have hrq : r ≠ q := by
          intro h; subst h
          exact absurd (Finset.mem_filter.mp hr).2.2 (by simpa [Nat.dvd_iff_mod_eq_zero] using hq_odd)
        have hnd : ¬ q ∣ r := fun h => hrq ((Nat.prime_dvd_prime_iff_eq hq_pr hr_pr).mp h).symm
        exact Nat.factorization_eq_zero_of_not_dvd hnd
      rw [hq_sum, zero_add, Nat.factorization_def _ hq_pr]
      omega
  · have hq_sum :
        (∑ x ∈ (Finset.Icc 2 n).filter (fun r => r.Prime ∧ ¬ 2 ∣ padicValNat r (Nat.factorial n)),
          x.factorization q) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have hr_pr : r.Prime := (Finset.mem_filter.mp hr).2.1
      by_cases hq_pr : q.Prime
      · have hrq : r ≠ q := by
          intro h; subst h
          exact hq_mem (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hr).1, hr_pr⟩)
        have hnd : ¬ q ∣ r := fun h => hrq ((Nat.prime_dvd_prime_iff_eq hq_pr hr_pr).mp h).symm
        exact Nat.factorization_eq_zero_of_not_dvd hnd
      · exact (by by_contra h0; exact hq_pr (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0)))
    have hs_sum :
        (∑ x ∈ (Finset.Icc 2 n).filter Nat.Prime,
          (padicValNat x (Nat.factorial n) / 2) * x.factorization q) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have hr_pr : r.Prime := (Finset.mem_filter.mp hr).2
      by_cases hq_pr : q.Prime
      · have hrq : r ≠ q := fun h => hq_mem (h ▸ hr)
        have hnd : ¬ q ∣ r := fun h => hrq ((Nat.prime_dvd_prime_iff_eq hq_pr hr_pr).mp h).symm
        rw [Nat.factorization_eq_zero_of_not_dvd hnd, mul_zero]
      · rw [(by by_contra h0; exact hq_pr (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0)) : r.factorization q = 0), mul_zero]
    rw [hq_sum, hs_sum, zero_add, mul_zero]
    by_cases hq_pr : q.Prime
    · have hgt : n < q := by
        by_contra hle
        push_neg at hle
        exact hq_mem (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq_pr.two_le, hle⟩, hq_pr⟩)
      exact Nat.factorization_eq_zero_of_not_dvd (fun h => by
        have := hq_pr.dvd_factorial.mp h
        omega)
    · exact (by by_contra h0; exact hq_pr (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0)))

/-- **Equation (3.3) / Lemma 3.2**: For `n! = q_n * s_n^2` and `s_n = Y₁ * U_{k-1}(X₁)` with
`X₁^2 - q_n * Y₁^2 = 1`, every prime `p ∈ Podd(n) \ {3}` satisfies
`v_p(q_n * Y₁^2) = v_p(n!) - 2 * v_p(k)`. -/
theorem padicValNat_pell_absorption {n k X₁ Y₁ p : ℕ}
    (hk : 1 ≤ k) (hp : p ∈ Podd n) (hp3 : p ≠ 3)
    (hpell : (X₁ : ℤ) ^ 2 - (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 = 1)
    (hY1_pos : 0 < Y₁)
    (hs_eq : (s_n n : ℤ) = (Y₁ : ℤ) * chebyshevU_eval (q_n n : ℤ) (X₁ : ℤ) (Y₁ : ℤ) k) :
    padicValNat p (q_n n * Y₁ ^ 2) = padicValNat p (Nat.factorial n) - 2 * padicValNat p k := by
  have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2.1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hpq : p ∣ q_n n := by
    unfold q_n
    exact Finset.dvd_prod_of_mem _ hp
  have hpDY : (p : ℤ) ∣ (q_n n : ℤ) * (Y₁ : ℤ) :=
    dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hpq) _
  have hU_val : padicValInt p (chebyshevU_eval (q_n n : ℤ) (X₁ : ℤ) (Y₁ : ℤ) k) =
      padicValNat p k :=
    padicValInt_chebyshevU hk hp_prime hpell hpDY (Or.inl hp3)
  set U := (chebyshevU_eval (q_n n : ℤ) (X₁ : ℤ) (Y₁ : ℤ) k).natAbs
  have hU_nat_val : padicValNat p U = padicValNat p k := hU_val
  have hs_nat : s_n n = Y₁ * U := by
    have h1 : ((s_n n : ℕ) : ℤ).natAbs = ((Y₁ : ℤ) * chebyshevU_eval (q_n n : ℤ) (X₁ : ℤ) (Y₁ : ℤ) k).natAbs :=
      congrArg Int.natAbs hs_eq
    simpa [Int.natAbs_mul] using h1
  have hfac_eq : Nat.factorial n = (q_n n * Y₁ ^ 2) * U ^ 2 := by
    rw [factorial_eq_q_n_mul_s_n_sq n, hs_nat, mul_pow]
    ring
  have hq_ne : q_n n ≠ 0 := by
    unfold q_n
    exact Finset.prod_ne_zero_iff.mpr (fun q hq => (Finset.mem_filter.mp hq).2.1.ne_zero)
  have hqY_ne : q_n n * Y₁ ^ 2 ≠ 0 := mul_ne_zero hq_ne (pow_ne_zero 2 hY1_pos.ne')
  have hU_ne : U ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hs_nat
    have hs_ne : s_n n ≠ 0 := by
      unfold s_n
      exact Finset.prod_ne_zero_iff.mpr (fun q hq => pow_ne_zero _ (Finset.mem_filter.mp hq).2.ne_zero)
    exact hs_ne hs_nat
  have hval_add : padicValNat p (Nat.factorial n) =
      padicValNat p (q_n n * Y₁ ^ 2) + 2 * padicValNat p U := by
    rw [hfac_eq, padicValNat.mul hqY_ne (pow_ne_zero 2 hU_ne), sq U, padicValNat.mul hU_ne hU_ne]
    omega
  rw [hU_nat_val] at hval_add
  omega

end GrasGreenbergBrocard
