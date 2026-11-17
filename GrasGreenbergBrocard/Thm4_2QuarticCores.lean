import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic
import GrasGreenbergBrocard.ExternalAxiomsSec4
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.ValuationParityThm
import GrasGreenbergBrocard.ValuationParityMod
import GrasGreenbergBrocard.ChebyshevLucas
import GrasGreenbergBrocard.PellFundamental
import GrasGreenbergBrocard.Prop4_1SmoothBiquad

/-!
# Theorem 4.2: Two-Stage Euclidean Division Quartic Law and Stretched-Exponential Midpoint Core Bounds

Formalizes Section 4.2 (eqs. 4.7–4.16 and Theorem 4.2(i)–(iii)) of the manuscript:
- `A_star`, `B_star`, `Z_k2`, `A_k2`, `B_k2`, `Z_le_sqrt`, `Z_gt_sqrt`: eq. (4.7), (4.10)
- `thm_4_2_part1_quartic_law`: First-stage Euclidean division quartic law (eqs. 4.8, 4.10)
- `thm_4_2_part1_euclidean_lock`: First-stage asymptotic `4 log Z = o(n log n)` & Euclidean lock (eqs. 4.8–4.9)
- `thm_4_2_part2_dual_quartic`: Second-stage consecutive splitting & dual quartic identities (eqs. 4.11–4.12)
- `thm_4_2_part2_euclidean_locks`: Second-stage `log B_∓` asymptotics & Euclidean locks (eqs. 4.13, 4.15)
- `thm_4_2_part3_midpoint_core_bounds`: Power-band equidistribution `n^{1/2 - ε}` bounds on `δ₁, δ₂` (eqs. 4.14, 4.16)
- `thm_4_2_part3_mertens_bound`: Explicit Mertens `n^{1/4}` lower bound on `δ₁, δ₂` (Theorem 4.2(iii))
-/

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard

/-- Even-valuation odd-prime factorial integer `A_n^*` (eq. 4.7). -/
def A_star (n : ℕ) : ℕ :=
  ∏ p ∈ (Peven n).filter (3 ≤ ·), p ^ padicValNat p (Nat.factorial n)

/-- Odd-valuation odd-prime factorial integer `B_n^*` (eq. 4.7). -/
def B_star (n : ℕ) : ℕ :=
  ∏ p ∈ (Podd n).filter (3 ≤ ·), p ^ padicValNat p (Nat.factorial n)

/-- Even-valuation factor `Z` dividing `Y₁(q_n)` (eq. 4.7). -/
def Z_k2 (n Y₁ : ℕ) : ℕ :=
  ∏ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ∣ Y₁), p ^ (padicValNat p (Nat.factorial n) / 2)

/-- First-stage numerator `A_n` (eq. 4.7). -/
def A_k2 (n X₁ : ℕ) : ℕ :=
  if X₁ % 2 = 1 then A_star n else 2 ^ (padicValNat 2 (Nat.factorial n) - 2) * A_star n

/-- First-stage denominator `B_n` (eq. 4.7). -/
def B_k2 (n X₁ : ℕ) : ℕ :=
  if X₁ % 2 = 1 then 2 ^ (padicValNat 2 (Nat.factorial n) - 2) * B_star n else B_star n

/-- `(√n)`-smooth part of `Z` (eq. 4.10). -/
def Z_le_sqrt (n Y₁ : ℕ) : ℕ :=
  ∏ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ∣ Y₁ ∧ p ≤ Nat.sqrt n),
    p ^ (padicValNat p (Nat.factorial n) / 2)

/-- `(√n)`-rough part of `Z` (eq. 4.10). -/
def Z_gt_sqrt (n Y₁ : ℕ) : ℕ :=
  ∏ p ∈ (Peven n).filter (fun p => 3 ≤ p ∧ p ∣ Y₁ ∧ Nat.sqrt n < p),
    p ^ (padicValNat p (Nat.factorial n) / 2)

lemma A_star_pos (n : ℕ) : 0 < A_star n := by
  unfold A_star
  exact Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.pos _)

lemma B_star_pos (n : ℕ) : 0 < B_star n := by
  unfold B_star
  exact Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.pos _)

lemma Z_k2_pos (n Y₁ : ℕ) : 0 < Z_k2 n Y₁ := by
  unfold Z_k2
  exact Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.pos _)

lemma A_k2_pos (n X₁ : ℕ) : 0 < A_k2 n X₁ := by
  unfold A_k2
  split_ifs
  · exact A_star_pos n
  · exact mul_pos (pow_pos (by norm_num) _) (A_star_pos n)

lemma B_k2_pos (n X₁ : ℕ) : 0 < B_k2 n X₁ := by
  unfold B_k2
  split_ifs
  · exact mul_pos (pow_pos (by norm_num) _) (B_star_pos n)
  · exact B_star_pos n

lemma Z_k2_split_sqrt (n Y₁ : ℕ) : Z_k2 n Y₁ = Z_le_sqrt n Y₁ * Z_gt_sqrt n Y₁ := by
  unfold Z_k2 Z_le_sqrt Z_gt_sqrt
  have hpart : (Peven n).filter (fun p => 3 ≤ p ∧ p ∣ Y₁) =
      (Peven n).filter (fun p => 3 ≤ p ∧ p ∣ Y₁ ∧ p ≤ Nat.sqrt n) ∪
      (Peven n).filter (fun p => 3 ≤ p ∧ p ∣ Y₁ ∧ Nat.sqrt n < p) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases h4 : p ≤ Nat.sqrt n
      · left; exact ⟨h1, h2, h3, h4⟩
      · right; exact ⟨h1, h2, h3, by omega⟩
    · rintro (⟨h1, h2, h3, _⟩ | ⟨h1, h2, h3, _⟩) <;> exact ⟨h1, h2, h3⟩
  have hdisj : Disjoint
      ((Peven n).filter (fun p => 3 ≤ p ∧ p ∣ Y₁ ∧ p ≤ Nat.sqrt n))
      ((Peven n).filter (fun p => 3 ≤ p ∧ p ∣ Y₁ ∧ Nat.sqrt n < p)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2.2.2
    have h2 := (Finset.mem_filter.mp hp2).2.2.2
    omega
  rw [hpart, Finset.prod_union hdisj]

private lemma coprime_A_star_B_star (n : ℕ) : Nat.Coprime (A_star n) (B_star n) := by
  unfold A_star B_star
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  have hp_mem := Finset.mem_filter.mp hp
  have hq_mem := Finset.mem_filter.mp hq
  have hp_pr : p.Prime := (Finset.mem_filter.mp hp_mem.1).2.1
  have hq_pr : q.Prime := (Finset.mem_filter.mp hq_mem.1).2.1
  have hp_ev : 2 ∣ padicValNat p (Nat.factorial n) := (Finset.mem_filter.mp hp_mem.1).2.2
  have hq_odd : ¬ 2 ∣ padicValNat q (Nat.factorial n) := (Finset.mem_filter.mp hq_mem.1).2.2
  have hpq : p ≠ q := fun h => by subst h; exact hq_odd hp_ev
  exact ((Nat.coprime_primes hp_pr hq_pr).mpr hpq).pow _ _

private lemma A_star_mul_B_star (n : ℕ) :
    A_star n * B_star n * 2 ^ padicValNat 2 (Nat.factorial n) = Nat.factorial n := by
  have hfac_ne : Nat.factorial n ≠ 0 := Nat.factorial_ne_zero n
  have h_all : (∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p ^ padicValNat p (Nat.factorial n)) =
      Nat.factorial n := by
    apply Nat.eq_of_factorization_eq
    · exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero)
    · exact hfac_ne
    · intro q
      rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero)]
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Nat.factorization_pow, Finsupp.smul_apply,
        smul_eq_mul]
      by_cases hq : q ∈ (Finset.Icc 2 n).filter Nat.Prime
      · have hq_pr := (Finset.mem_filter.mp hq).2
        rw [Finset.sum_eq_single q]
        · rw [hq_pr.factorization_self, mul_one, Nat.factorization_def _ hq_pr]
        · intro p hp hpq
          have hp_pr := (Finset.mem_filter.mp hp).2
          rw [hp_pr.factorization, Finsupp.single_apply, if_neg hpq, mul_zero]
        · intro habs; exact absurd hq habs
      · rw [Finset.sum_eq_zero]
        · symm
          rw [Nat.factorization_eq_zero_iff]
          by_cases hq_pr : q.Prime
          · right; left; intro hdvd
            exact hq (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq_pr.two_le, hq_pr.dvd_factorial.mp hdvd⟩, hq_pr⟩)
          · left; exact hq_pr
        · intro p hp
          have hp_pr := (Finset.mem_filter.mp hp).2
          have hpq : p ≠ q := fun h => hq (h ▸ hp)
          rw [hp_pr.factorization, Finsupp.single_apply, if_neg hpq, mul_zero]
  by_cases hn2 : n < 2
  · have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl <;> simp [A_star, B_star, Peven, Podd, Nat.factorial]
  · have hsplit : (Finset.Icc 2 n).filter Nat.Prime =
        insert 2 ((Finset.Icc 3 n).filter Nat.Prime) := by
      ext p; simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hp2, hpn⟩, hp_pr⟩
        by_cases hp_eq : p = 2
        · left; exact hp_eq
        · right; exact ⟨⟨by omega, hpn⟩, hp_pr⟩
      · rintro (rfl | ⟨⟨hp3, hpn⟩, hp_pr⟩)
        · exact ⟨⟨le_rfl, by omega⟩, Nat.prime_two⟩
        · exact ⟨⟨by omega, hpn⟩, hp_pr⟩
    have h2_not : (2 : ℕ) ∉ (Finset.Icc 3 n).filter Nat.Prime := by simp
    have hsplit_oe : (Finset.Icc 3 n).filter Nat.Prime =
        (Peven n).filter (3 ≤ ·) ∪ (Podd n).filter (3 ≤ ·) := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Peven, Podd]
      constructor
      · rintro ⟨⟨hp3, hpn⟩, hp_pr⟩
        by_cases hev : 2 ∣ padicValNat p (Nat.factorial n)
        · left; exact ⟨⟨⟨by omega, hpn⟩, hp_pr, hev⟩, hp3⟩
        · right; exact ⟨⟨⟨by omega, hpn⟩, hp_pr, hev⟩, hp3⟩
      · rintro (⟨⟨⟨_, hpn⟩, hp_pr, _⟩, hp3⟩ | ⟨⟨⟨_, hpn⟩, hp_pr, _⟩, hp3⟩)
        · exact ⟨⟨hp3, hpn⟩, hp_pr⟩
        · exact ⟨⟨hp3, hpn⟩, hp_pr⟩
    have hdisj_oe : Disjoint ((Peven n).filter (3 ≤ ·)) ((Podd n).filter (3 ≤ ·)) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2.2
        (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2.2
    nth_rw 2 [← h_all]
    rw [hsplit, Finset.prod_insert h2_not, hsplit_oe, Finset.prod_union hdisj_oe]
    unfold A_star B_star
    ring

/-- **Theorem 4.2(i) (First-Stage Euclidean Division Quartic Law, eqs. 4.8–4.10)**:
In the `k = 2` regime with `n ≥ 8`, `n! + 1 = m^2`:
1. `Nat.Coprime (A_k2 n X₁) (B_k2 n X₁)`.
2. `A_k2 n X₁ = X₁ ^ 2 * (Z_k2 n Y₁) ^ 2` and `q_n n * Y₁ ^ 2 = B_k2 n X₁ * (Z_k2 n Y₁) ^ 2`.
3. `A_k2 n X₁ = B_k2 n X₁ * (Z_k2 n Y₁) ^ 4 + (Z_k2 n Y₁) ^ 2`.
4. `Z_k2 n Y₁ = Z_le_sqrt n Y₁ * Z_gt_sqrt n Y₁`.
5. If `X₁` is even, then `2 ∣ padicValNat 2 (n!)` and `q_n n % 8 = 7`. -/
theorem thm_4_2_part1_quartic_law {n m X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hm : Nat.factorial n + 1 = m ^ 2)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk2 : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2) :
    Nat.Coprime (A_k2 n X₁) (B_k2 n X₁) ∧
    A_k2 n X₁ = X₁ ^ 2 * (Z_k2 n Y₁) ^ 2 ∧
    q_n n * Y₁ ^ 2 = B_k2 n X₁ * (Z_k2 n Y₁) ^ 2 ∧
    A_k2 n X₁ = B_k2 n X₁ * (Z_k2 n Y₁) ^ 4 + (Z_k2 n Y₁) ^ 2 ∧
    Z_k2 n Y₁ = Z_le_sqrt n Y₁ * Z_gt_sqrt n Y₁ ∧
    (X₁ % 2 = 0 → 2 ∣ padicValNat 2 (Nat.factorial n) ∧ q_n n % 8 = 7) := by
  have hn6 : n ≠ 6 := by omega
  obtain ⟨_, _, _, hs_eq, _, _, hfac_eq⟩ := k_eq_2_identities (by omega) hn6 hm hfund hk2
  have hpart1 := prop_4_1_part1 hn hm hfund hk2
  have hX1_pos : 1 ≤ X₁ := hfund.1
  have hY1_pos : 0 < Y₁ := hfund.2.1
  have hq_pos : 0 < q_n n := (q_n_squarefree n).ne_zero |> Nat.pos_of_ne_zero
  have hcop_AB : Nat.Coprime (A_k2 n X₁) (B_k2 n X₁) := by
    unfold A_k2 B_k2
    have hcop_star := coprime_A_star_B_star n
    have hcop_2A : Nat.Coprime (2 ^ (padicValNat 2 (Nat.factorial n) - 2)) (A_star n) := by
      apply Nat.Coprime.pow_left
      apply Nat.Coprime.prod_right
      intro p hp
      have hp3 : 3 ≤ p := (Finset.mem_filter.mp hp).2
      have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
      exact ((Nat.coprime_primes Nat.prime_two hp_pr).mpr (by omega)).pow_right _
    have hcop_2B : Nat.Coprime (2 ^ (padicValNat 2 (Nat.factorial n) - 2)) (B_star n) := by
      apply Nat.Coprime.pow_left
      apply Nat.Coprime.prod_right
      intro p hp
      have hp3 : 3 ≤ p := (Finset.mem_filter.mp hp).2
      have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
      exact ((Nat.coprime_primes Nat.prime_two hp_pr).mpr (by omega)).pow_right _
    split_ifs
    · exact Nat.Coprime.mul_right hcop_2A.symm hcop_star
    · exact Nat.Coprime.mul_left hcop_2B hcop_star
  have hXZ_eq : A_k2 n X₁ = X₁ ^ 2 * (Z_k2 n Y₁) ^ 2 := by
    have h_lhs_ne : A_k2 n X₁ ≠ 0 := (A_k2_pos n X₁).ne'
    have h_rhs_ne : X₁ ^ 2 * (Z_k2 n Y₁) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 (by omega)) (pow_ne_zero 2 (Z_k2_pos n Y₁).ne')
    have hcop_XY : Nat.Coprime X₁ Y₁ := by
      have hpell := hfund.2.2.1
      refine Nat.coprime_of_dvd' (fun p hp hpX hpY => ?_)
      have hp1 : p ∣ X₁ ^ 2 - q_n n * Y₁ ^ 2 := Nat.dvd_sub (dvd_pow hpX (by norm_num))
        (dvd_mul_of_dvd_right (dvd_pow hpY (by norm_num)) _)
      have h1 : X₁ ^ 2 - q_n n * Y₁ ^ 2 = 1 := by omega
      rw [h1] at hp1
      exact absurd hp1 hp.not_dvd_one
    have hfac_qY : Nat.factorial n = 4 * X₁ ^ 2 * (q_n n * Y₁ ^ 2) := by
      have hdiff : (X₁ - 1) * (X₁ + 1) = q_n n * Y₁ ^ 2 := by
        zify [hX1_pos]; have : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
        linarith
      rw [hfac_eq]; calc 4 * (X₁ - 1) * X₁ ^ 2 * (X₁ + 1) = 4 * X₁ ^ 2 * ((X₁ - 1) * (X₁ + 1)) := by ring
        _ = 4 * X₁ ^ 2 * (q_n n * Y₁ ^ 2) := by rw [hdiff]
    have hv2_ge : 2 ≤ padicValNat 2 (Nat.factorial n) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
        (dvd_trans (by decide : 2 ^ 2 ∣ 24) (Nat.factorial_dvd_factorial (by omega : 4 ≤ n)))
    apply Nat.eq_of_factorization_eq h_lhs_ne h_rhs_ne
    intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      by_cases hp2 : p = 2
      · subst hp2
        have h_val_n : padicValNat 2 (Nat.factorial n) = 2 + 2 * padicValNat 2 X₁ + padicValNat 2 (q_n n * Y₁ ^ 2) := by
          rw [hfac_qY, padicValNat.mul (mul_ne_zero (by norm_num) (pow_ne_zero 2 (by omega)))
              (mul_ne_zero hq_pos.ne' (pow_ne_zero 2 hY1_pos.ne')),
            padicValNat.mul (by norm_num) (pow_ne_zero 2 (by omega)),
            show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow,
            sq, padicValNat.mul (by omega) (by omega)]
          ring
        have hZ_odd : ¬ 2 ∣ Z_k2 n Y₁ := by
          unfold Z_k2
          rw [Prime.dvd_finset_prod_iff Nat.prime_two.prime]
          rintro ⟨q, hq, hdvd⟩
          have hq3 : 3 ≤ q := (Finset.mem_filter.mp hq).2.1
          have hq_pr : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
          have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq_pr).mp (Nat.prime_two.dvd_of_dvd_pow hdvd)
          omega
        have hA_star_odd : ¬ 2 ∣ A_star n := by
          unfold A_star
          rw [Prime.dvd_finset_prod_iff Nat.prime_two.prime]
          rintro ⟨q, hq, hdvd⟩
          have hq3 : 3 ≤ q := (Finset.mem_filter.mp hq).2
          have hq_pr : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
          have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq_pr).mp (Nat.prime_two.dvd_of_dvd_pow hdvd)
          omega
        rw [Nat.factorization_mul (pow_ne_zero 2 (by omega)) (pow_ne_zero 2 (Z_k2_pos n Y₁).ne'),
            Nat.factorization_pow, Nat.factorization_pow]
        simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Nat.factorization_def (Z_k2 n Y₁) Nat.prime_two, padicValNat.eq_zero_of_not_dvd hZ_odd, mul_zero, add_zero]
        unfold A_k2
        split_ifs with hX_odd
        · have h2ndX : ¬ 2 ∣ X₁ := by omega
          rw [Nat.factorization_def (A_star n) Nat.prime_two, padicValNat.eq_zero_of_not_dvd hA_star_odd,
              Nat.factorization_def X₁ Nat.prime_two, padicValNat.eq_zero_of_not_dvd h2ndX, mul_zero]
        · have h2dX : 2 ∣ X₁ := by omega
          have h2nd_qY : ¬ 2 ∣ q_n n * Y₁ ^ 2 := by
            intro h2qY
            rcases Nat.prime_two.dvd_mul.mp h2qY with h2q | h2Y2
            · have hpell := hfund.2.2.1
              have h2d1 : 2 ∣ X₁ ^ 2 - q_n n * Y₁ ^ 2 :=
                Nat.dvd_sub (dvd_pow h2dX (by norm_num)) (dvd_mul_of_dvd_right h2q _)
              have h1 : X₁ ^ 2 - q_n n * Y₁ ^ 2 = 1 := by omega
              rw [h1] at h2d1; exact Nat.prime_two.not_dvd_one h2d1
            · exact Nat.prime_two.not_dvd_one (Nat.dvd_gcd h2dX (Nat.prime_two.dvd_of_dvd_pow h2Y2) |>.trans (by rw [hcop_XY]))
          rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (A_star_pos n).ne',
              Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
              smul_eq_mul, Nat.factorization_def (A_star n) Nat.prime_two, padicValNat.eq_zero_of_not_dvd hA_star_odd,
              Nat.prime_two.factorization_self, mul_one, add_zero,
              Nat.factorization_def X₁ Nat.prime_two, h_val_n, padicValNat.eq_zero_of_not_dvd h2nd_qY, add_zero]
          omega
      · have hp3 : 3 ≤ p := by have := hp.two_le; omega
        have hA_val : (A_k2 n X₁).factorization p = (A_star n).factorization p := by
          unfold A_k2
          split_ifs
          · rfl
          · rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (A_star_pos n).ne',
                Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
                smul_eq_mul, Nat.factorization_def _ hp, padicValNat.eq_zero_of_not_dvd (fun h => by
                  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h); omega),
                mul_zero, zero_add]
        have hA_star_val : (A_star n).factorization p =
            if p ∈ (Peven n).filter (3 ≤ ·) then padicValNat p (Nat.factorial n) else 0 := by
          unfold A_star
          rw [Nat.factorization_prod (fun q hq =>
            pow_ne_zero _ (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1.ne_zero)]
          simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Nat.factorization_pow,
            Finsupp.smul_apply, smul_eq_mul]
          split_ifs with hmem
          · rw [Finset.sum_eq_single p]
            · rw [hp.factorization_self, mul_one]
            · intro q hq hqp
              have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
              rw [hq_pr.factorization, Finsupp.single_apply, if_neg hqp, mul_zero]
            · intro habs; exact absurd hmem habs
          · rw [Finset.sum_eq_zero]
            intro q hq
            have hqp : q ≠ p := fun h => hmem (h ▸ hq)
            have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
            rw [hq_pr.factorization, Finsupp.single_apply, if_neg hqp, mul_zero]
        have hZ_val : (Z_k2 n Y₁).factorization p =
            if p ∈ (Peven n).filter (fun q => 3 ≤ q ∧ q ∣ Y₁) then padicValNat p (Nat.factorial n) / 2 else 0 := by
          unfold Z_k2
          rw [Nat.factorization_prod (fun q hq =>
            pow_ne_zero _ (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1.ne_zero)]
          simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Nat.factorization_pow,
            Finsupp.smul_apply, smul_eq_mul]
          split_ifs with hmem
          · rw [Finset.sum_eq_single p]
            · rw [hp.factorization_self, mul_one]
            · intro q hq hqp
              have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
              rw [hq_pr.factorization, Finsupp.single_apply, if_neg hqp, mul_zero]
            · intro habs; exact absurd hmem habs
          · rw [Finset.sum_eq_zero]
            intro q hq
            have hqp : q ≠ p := fun h => hmem (h ▸ hq)
            have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
            rw [hq_pr.factorization, Finsupp.single_apply, if_neg hqp, mul_zero]
        rw [hA_val, hA_star_val,
            Nat.factorization_mul (pow_ne_zero 2 (by omega)) (pow_ne_zero 2 (Z_k2_pos n Y₁).ne'),
            Nat.factorization_pow, Nat.factorization_pow]
        simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hZ_val, Nat.factorization_def X₁ hp]
        by_cases hmem : p ∈ (Peven n).filter (3 ≤ ·)
        · have hev : 2 ∣ padicValNat p (Nat.factorial n) := (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2.2
          by_cases hpY : p ∣ Y₁
          · have hp_ndX : ¬ p ∣ X₁ := fun hX => hp.not_dvd_one (Nat.dvd_gcd hX hpY |>.trans (by rw [hcop_XY]))
            have hmemZ : p ∈ (Peven n).filter (fun q => 3 ≤ q ∧ q ∣ Y₁) :=
              Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hmem).1, hp3, hpY⟩
            rw [if_pos hmem, if_pos hmemZ, padicValNat.eq_zero_of_not_dvd hp_ndX]
            omega
          · have hmemZ : ¬ p ∈ (Peven n).filter (fun q => 3 ≤ q ∧ q ∣ Y₁) := fun h =>
              hpY (Finset.mem_filter.mp h).2.2
            have hp_div_s : p ∣ s_n n := by
              have hv_ge2 : 2 ≤ padicValNat p (Nat.factorial n) := by
                have hpn : p ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).1).2
                have h1 : 1 ≤ padicValNat p (Nat.factorial n) :=
                  (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp (by
                    simpa using hp.dvd_factorial.mpr hpn)
                omega
              have hfac := factorial_eq_q_n_mul_s_n_sq n
              have hq_nd : ¬ p ^ 2 ∣ q_n n := by
                simpa [sq] using (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp
              have hp2_dvd : p ^ 2 ∣ q_n n * (s_n n) ^ 2 := by
                rw [← hfac]; exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp hv_ge2
              by_contra hnd_s
              have hcop_s : Nat.Coprime (p ^ 2) ((s_n n) ^ 2) :=
                (hp.coprime_iff_not_dvd.mpr hnd_s).pow _ _
              exact hq_nd (hcop_s.dvd_of_dvd_mul_right hp2_dvd)
            have hpX : p ∣ X₁ := by
              rw [hs_eq] at hp_div_s
              rcases hp.dvd_mul.mp hp_div_s with h2X | hY
              · rcases hp.dvd_mul.mp h2X with h2 | hX
                · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2; omega
                · exact hX
              · exact absurd hY hpY
            have hvalX := (hpart1.2.2.1 p hp hp3 hpX).2.1
            rw [if_pos hmem, if_neg hmemZ]
            omega
        · have hp_ndX : ¬ p ∣ X₁ := fun hX =>
            hmem (Finset.mem_filter.mpr ⟨(hpart1.2.2.1 p hp hp3 hX).1, hp3⟩)
          have hmemZ : ¬ p ∈ (Peven n).filter (fun q => 3 ≤ q ∧ q ∣ Y₁) := fun h =>
            hmem (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1, hp3⟩)
          rw [if_neg hmem, if_neg hmemZ, padicValNat.eq_zero_of_not_dvd hp_ndX]
    · have h0a : (A_k2 n X₁).factorization p = 0 := by
        by_contra h0
        exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
      have h0b : (X₁ ^ 2 * (Z_k2 n Y₁) ^ 2).factorization p = 0 := by
        by_contra h0
        exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
      omega
  have hBZ_eq : q_n n * Y₁ ^ 2 = B_k2 n X₁ * (Z_k2 n Y₁) ^ 2 := by
    have hprod : A_k2 n X₁ * B_k2 n X₁ = X₁ ^ 2 * (q_n n * Y₁ ^ 2) := by
      have h1 : A_k2 n X₁ * B_k2 n X₁ = A_star n * B_star n * 2 ^ (padicValNat 2 (Nat.factorial n) - 2) := by
        unfold A_k2 B_k2; split_ifs <;> ring
      have hfac_qY : Nat.factorial n = 4 * X₁ ^ 2 * (q_n n * Y₁ ^ 2) := by
        have hdiff : (X₁ - 1) * (X₁ + 1) = q_n n * Y₁ ^ 2 := by
          zify [hX1_pos]; have : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
          linarith
        rw [hfac_eq]; calc 4 * (X₁ - 1) * X₁ ^ 2 * (X₁ + 1) = 4 * X₁ ^ 2 * ((X₁ - 1) * (X₁ + 1)) := by ring
          _ = 4 * X₁ ^ 2 * (q_n n * Y₁ ^ 2) := by rw [hdiff]
      have h2_le : 2 ≤ padicValNat 2 (Nat.factorial n) := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
          (dvd_trans (by decide : 2 ^ 2 ∣ 24) (Nat.factorial_dvd_factorial (by omega : 4 ≤ n)))
      have h4_mul : 4 * (A_k2 n X₁ * B_k2 n X₁) = Nat.factorial n := by
        have hpow : 4 * 2 ^ (padicValNat 2 (Nat.factorial n) - 2) = 2 ^ padicValNat 2 (Nat.factorial n) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.add_sub_of_le h2_le]
        calc 4 * (A_k2 n X₁ * B_k2 n X₁)
            = 4 * (A_star n * B_star n * 2 ^ (padicValNat 2 (Nat.factorial n) - 2)) := by rw [h1]
          _ = A_star n * B_star n * (4 * 2 ^ (padicValNat 2 (Nat.factorial n) - 2)) := by ring
          _ = A_star n * B_star n * 2 ^ padicValNat 2 (Nat.factorial n) := by rw [hpow]
          _ = Nat.factorial n := A_star_mul_B_star n
      have h4_eq : 4 * (A_k2 n X₁ * B_k2 n X₁) = 4 * (X₁ ^ 2 * (q_n n * Y₁ ^ 2)) := by
        rw [h4_mul, hfac_qY, mul_assoc]
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4_eq
    have hmul : (X₁ ^ 2 * (Z_k2 n Y₁) ^ 2) * B_k2 n X₁ = X₁ ^ 2 * (q_n n * Y₁ ^ 2) := by
      rw [← hXZ_eq, hprod]
    have hmul' : X₁ ^ 2 * (B_k2 n X₁ * (Z_k2 n Y₁) ^ 2) = X₁ ^ 2 * (q_n n * Y₁ ^ 2) := by linarith
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos (by omega : 0 < X₁) 2) hmul').symm
  have hquartic : A_k2 n X₁ = B_k2 n X₁ * (Z_k2 n Y₁) ^ 4 + (Z_k2 n Y₁) ^ 2 := by
    have hpell := hfund.2.2.1
    calc A_k2 n X₁ = X₁ ^ 2 * (Z_k2 n Y₁) ^ 2 := hXZ_eq
      _ = (q_n n * Y₁ ^ 2 + 1) * (Z_k2 n Y₁) ^ 2 := by rw [hpell]
      _ = (B_k2 n X₁ * (Z_k2 n Y₁) ^ 2 + 1) * (Z_k2 n Y₁) ^ 2 := by rw [hBZ_eq]
      _ = B_k2 n X₁ * (Z_k2 n Y₁) ^ 4 + (Z_k2 n Y₁) ^ 2 := by ring
  have htype2 : X₁ % 2 = 0 → 2 ∣ padicValNat 2 (Nat.factorial n) ∧ q_n n % 8 = 7 := by
    intro hXev
    have h2dX : 2 ∣ X₁ := by omega
    have hfac_qY : Nat.factorial n = 4 * X₁ ^ 2 * (q_n n * Y₁ ^ 2) := by
      have hdiff : (X₁ - 1) * (X₁ + 1) = q_n n * Y₁ ^ 2 := by
        zify [hX1_pos]; have : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
        linarith
      rw [hfac_eq]; calc 4 * (X₁ - 1) * X₁ ^ 2 * (X₁ + 1) = 4 * X₁ ^ 2 * ((X₁ - 1) * (X₁ + 1)) := by ring
        _ = 4 * X₁ ^ 2 * (q_n n * Y₁ ^ 2) := by rw [hdiff]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2nd_qY : ¬ 2 ∣ q_n n * Y₁ ^ 2 := by
      intro h2qY
      have hpell := hfund.2.2.1
      have h1 : 2 ∣ X₁ ^ 2 - q_n n * Y₁ ^ 2 :=
        Nat.dvd_sub (dvd_pow h2dX (by norm_num)) h2qY
      have h2 : X₁ ^ 2 - q_n n * Y₁ ^ 2 = 1 := by omega
      rw [h2] at h1; exact Nat.prime_two.not_dvd_one h1
    have h_val_n : padicValNat 2 (Nat.factorial n) = 2 + 2 * padicValNat 2 X₁ := by
      rw [hfac_qY, padicValNat.mul (mul_ne_zero (by norm_num) (pow_ne_zero 2 (by omega)))
          (mul_ne_zero hq_pos.ne' (pow_ne_zero 2 hY1_pos.ne')),
        padicValNat.mul (by norm_num) (pow_ne_zero 2 (by omega)),
        show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow,
        sq, padicValNat.mul (by omega) (by omega), padicValNat.eq_zero_of_not_dvd h2nd_qY]
      ring
    have hv2_ge7 : 7 ≤ padicValNat 2 (Nat.factorial n) := by
      exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
        (dvd_trans (by decide : 2 ^ 7 ∣ Nat.factorial 8) (Nat.factorial_dvd_factorial hn))
    have hv2_even : 2 ∣ padicValNat 2 (Nat.factorial n) := ⟨1 + padicValNat 2 X₁, by omega⟩
    have hvX_ge3 : 3 ≤ padicValNat 2 X₁ := by omega
    have h8_dvd_X : 8 ∣ X₁ := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact (padicValNat_dvd_iff_le (by omega)).mpr hvX_ge3
    have hY_odd : Y₁ % 2 = 1 := by
      by_contra h0
      have h2Y : 2 ∣ Y₁ := by omega
      exact h2nd_qY (dvd_mul_of_dvd_right (dvd_pow h2Y (by norm_num)) _)
    have hpell := hfund.2.2.1
    have hX8 : X₁ ^ 2 % 8 = 0 := by
      obtain ⟨k, rfl⟩ := h8_dvd_X
      rw [mul_pow, show 8 ^ 2 = 8 * 8 by norm_num, mul_assoc, Nat.mul_mod_right]
    have hY8 : Y₁ ^ 2 % 8 = 1 := by
      have hY_mod : Y₁ % 8 = 1 ∨ Y₁ % 8 = 3 ∨ Y₁ % 8 = 5 ∨ Y₁ % 8 = 7 := by omega
      rw [sq, Nat.mul_mod]
      rcases hY_mod with h | h | h | h <;> rw [h]
    have hq8 : q_n n % 8 = 7 := by
      have hmod : (X₁ ^ 2) % 8 = (q_n n * Y₁ ^ 2 + 1) % 8 := congrArg (· % 8) hpell
      rw [Nat.add_mod, Nat.mul_mod, hX8, hY8] at hmod
      have : q_n n % 8 < 8 := Nat.mod_lt _ (by norm_num)
      omega
    exact ⟨hv2_even, hq8⟩
  exact ⟨hcop_AB, hXZ_eq, hBZ_eq, hquartic, Z_k2_split_sqrt n Y₁, htype2⟩

private lemma log_A_star_eq (n : ℕ) : Real.log (A_star n : ℝ) = S_even n := by
  unfold A_star S_even
  push_cast
  rw [Real.log_prod (fun p hp => pow_ne_zero _ (Nat.cast_ne_zero.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.ne_zero))]
  apply Finset.sum_congr rfl
  intro p _
  rw [Real.log_pow]

private lemma log_B_star_eq (n : ℕ) : Real.log (B_star n : ℝ) = S_odd n := by
  unfold B_star S_odd
  push_cast
  rw [Real.log_prod (fun p hp => pow_ne_zero _ (Nat.cast_ne_zero.mpr (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1.ne_zero))]
  apply Finset.sum_congr rfl
  intro p _
  rw [Real.log_pow]

private lemma Z_k2_log_upper_bound_clean (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n m X₁ Y₁ : ℕ, N₀ ≤ n →
      Nat.factorial n + 1 = m ^ 2 →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2 →
      4 * Real.log (Z_k2 n Y₁ : ℝ) ≤ ε * ((n : ℝ) * Real.log (n : ℝ)) := by
  have h_Delta_ev : ∀ᶠ n : ℕ in atTop,
      |Delta_parity n| ≤ (ε / 2) * ((n : ℝ) * Real.log (n : ℝ)) := by
    have h1 := Delta_parity_isLittleO_mul_log.bound (by positivity : (0 : ℝ) < ε / 2)
    filter_upwards [h1, eventually_ge_atTop 2] with n hn hn2
    have hn_log_nn : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
    rw [Real.norm_of_nonneg hn_log_nn] at hn
    simpa [Real.norm_eq_abs] using hn
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_all : ∀ᶠ n : ℕ in atTop,
      8 ≤ n ∧ |Delta_parity n| ≤ (ε / 2) * ((n : ℝ) * Real.log (n : ℝ)) ∧
      2 / ε ≤ Real.log (n : ℝ) :=
    (eventually_ge_atTop 8).and (h_Delta_ev.and (hlog_inf.eventually (eventually_ge_atTop (2 / ε))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h_all
  refine ⟨N₀, fun n m X₁ Y₁ hn hm hfund hk2 => ?_⟩
  obtain ⟨hn8, h_Delta_n, hlog_ge⟩ := hN₀ n hn
  have hn_err : (n : ℝ) ≤ (ε / 2) * ((n : ℝ) * Real.log (n : ℝ)) := by
    have h1 : 1 ≤ (ε / 2) * Real.log (n : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlog_ge (by positivity : 0 ≤ ε / 2)
      have heq : (ε / 2) * (2 / ε) = 1 := by field_simp [hε.ne']
      linarith
    have h2 : (n : ℝ) * 1 ≤ (n : ℝ) * ((ε / 2) * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hq1 := thm_4_2_part1_quartic_law hn8 hm hfund hk2
  have hquartic := hq1.2.2.2.1
  have hA_ge : (B_k2 n X₁ : ℝ) * (Z_k2 n Y₁ : ℝ) ^ 4 ≤ (A_k2 n X₁ : ℝ) := by
    exact_mod_cast (hquartic ▸ Nat.le_add_right (B_k2 n X₁ * Z_k2 n Y₁ ^ 4) (Z_k2 n Y₁ ^ 2))
  have hB_pos_r : (0 : ℝ) < (B_k2 n X₁ : ℝ) := by exact_mod_cast B_k2_pos n X₁
  have hZ_pos_r : (0 : ℝ) < (Z_k2 n Y₁ : ℝ) := by exact_mod_cast Z_k2_pos n Y₁
  have hlog_AB : 4 * Real.log (Z_k2 n Y₁ : ℝ) ≤ Real.log (A_k2 n X₁ : ℝ) - Real.log (B_k2 n X₁ : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hA_ge
    rw [Real.log_mul hB_pos_r.ne' (pow_ne_zero 4 hZ_pos_r.ne'), Real.log_pow] at h1
    push_cast at h1
    linarith
  have hv2_le : (padicValNat 2 (Nat.factorial n) : ℝ) ≤ (n : ℝ) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hleg : (2 - 1) * padicValNat 2 (Nat.factorial n) = n - (Nat.digits 2 n).sum :=
      sub_one_mul_padicValNat_factorial n
    exact_mod_cast (by omega : padicValNat 2 (Nat.factorial n) ≤ n)
  have h_diff_AB : Real.log (A_k2 n X₁ : ℝ) - Real.log (B_k2 n X₁ : ℝ) ≤
      |Delta_parity n| + (n : ℝ) := by
    unfold A_k2 B_k2
    have hlog2_le1 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      linarith [Real.exp_one_gt_d9]
    split_ifs
    · rw [Nat.cast_mul, Real.log_mul (by positivity) (B_star_pos n |> Nat.cast_pos.mpr |>.ne'),
          log_A_star_eq, log_B_star_eq, Nat.cast_pow, Real.log_pow]
      have h1 : S_even n - S_odd n = Delta_parity n := by unfold Delta_parity; ring
      have h2 : 0 ≤ ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) * Real.log 2 := by positivity
      norm_num at h2 ⊢
      linarith [le_abs_self (Delta_parity n)]
    · rw [Nat.cast_mul, Real.log_mul (by positivity) (A_star_pos n |> Nat.cast_pos.mpr |>.ne'),
          log_A_star_eq, log_B_star_eq, Nat.cast_pow, Real.log_pow]
      have h1 : S_even n - S_odd n = Delta_parity n := by unfold Delta_parity; ring
      have h2 : ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : padicValNat 2 (Nat.factorial n) - 2 ≤ padicValNat 2 (Nat.factorial n) := Nat.sub_le _ _
        linarith [show ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) ≤ (padicValNat 2 (Nat.factorial n) : ℝ) by exact_mod_cast this]
      have h3 : ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) * Real.log 2 ≤ (n : ℝ) * 1 :=
        mul_le_mul h2 hlog2_le1 (Real.log_nonneg (by norm_num)) (by positivity)
      norm_num at h3 ⊢
      linarith [le_abs_self (Delta_parity n)]
  linarith [abs_le.mp h_Delta_n]

/-- **Theorem 4.2(i) (Asymptotic `4 log Z = o(n log n)` and Euclidean Division Lock, eqs. 4.8–4.9)**:
For every `ε > 0`, `4 log Z ≤ ε n log n` for all sufficiently large `n`; moreover, for all
sufficiently large `n` with a `k = 2` solution, `0 < Z^2 < B_k2 n X₁`, so Euclidean division gives
`A_k2 n X₁ / B_k2 n X₁ = Z^4`, `A_k2 n X₁ % B_k2 n X₁ = Z^2`, and `(A_k2 % B_k2)^2 = A_k2 / B_k2`. -/
theorem thm_4_2_part1_euclidean_lock :
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n m X₁ Y₁ : ℕ, N₀ ≤ n →
      Nat.factorial n + 1 = m ^ 2 →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2 →
      4 * Real.log (Z_k2 n Y₁ : ℝ) ≤ ε * ((n : ℝ) * Real.log (n : ℝ))) ∧
    (∃ N₀ : ℕ, ∀ n m X₁ Y₁ : ℕ, N₀ ≤ n →
      Nat.factorial n + 1 = m ^ 2 →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2 →
      0 < (Z_k2 n Y₁) ^ 2 ∧
      (Z_k2 n Y₁) ^ 2 < B_k2 n X₁ ∧
      A_k2 n X₁ / B_k2 n X₁ = (Z_k2 n Y₁) ^ 4 ∧
      A_k2 n X₁ % B_k2 n X₁ = (Z_k2 n Y₁) ^ 2 ∧
      (A_k2 n X₁ % B_k2 n X₁) ^ 2 = A_k2 n X₁ / B_k2 n X₁) := by
  refine ⟨Z_k2_log_upper_bound_clean, ?_⟩
  obtain ⟨N₁, hN₁⟩ := Z_k2_log_upper_bound_clean (1 / 4) (by norm_num)
  have h_Sodd_ev : ∀ᶠ n : ℕ in atTop, (1 / 3 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) ≤ S_odd n := by
    have h1 := S_odd_asymptotic.bound (by norm_num : (0 : ℝ) < 1 / 6)
    filter_upwards [h1, eventually_ge_atTop 2] with n hn hn2
    have hn_log_nn : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
    rw [Real.norm_of_nonneg hn_log_nn] at hn
    have h2 := (abs_le.mp (Real.norm_eq_abs _ ▸ hn)).1
    linarith
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_all : ∀ᶠ n : ℕ in atTop,
      max N₁ 8 ≤ n ∧ (1 / 3 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) ≤ S_odd n ∧ 1 ≤ Real.log (n : ℝ) :=
    (eventually_ge_atTop (max N₁ 8)).and (h_Sodd_ev.and (hlog_inf.eventually (eventually_ge_atTop 1)))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h_all
  refine ⟨N₀, fun n m X₁ Y₁ hn hm hfund hk2 => ?_⟩
  obtain ⟨hmax, hSodd, hlog1⟩ := hN₀ n hn
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hmax
  have hn8 : 8 ≤ n := le_trans (le_max_right _ _) hmax
  have hZ_log := hN₁ n m X₁ Y₁ hn1 hm hfund hk2
  have hn_pos : (0 : ℝ) < (n : ℝ) * Real.log (n : ℝ) := by
    have : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
    nlinarith
  have hZ2_log : Real.log ((Z_k2 n Y₁ : ℝ) ^ 2) < Real.log (B_k2 n X₁ : ℝ) := by
    have hB_ge : S_odd n ≤ Real.log (B_k2 n X₁ : ℝ) := by
      unfold B_k2
      split_ifs
      · rw [Nat.cast_mul, Real.log_mul (by positivity) (B_star_pos n |> Nat.cast_pos.mpr |>.ne'), log_B_star_eq]
        have hnn : 0 ≤ Real.log ((2 ^ (padicValNat 2 (Nat.factorial n) - 2) : ℕ) : ℝ) :=
          Real.log_nonneg (by exact_mod_cast Nat.one_le_pow _ 2 (by norm_num))
        linarith
      · rw [log_B_star_eq]
    rw [Real.log_pow]
    push_cast
    linarith
  have hZ2_lt_B : (Z_k2 n Y₁) ^ 2 < B_k2 n X₁ := by
    have hZ_pos_r : (0 : ℝ) < (Z_k2 n Y₁ : ℝ) := by exact_mod_cast Z_k2_pos n Y₁
    have h1 : ((Z_k2 n Y₁ ^ 2 : ℕ) : ℝ) < (B_k2 n X₁ : ℝ) := by
      rw [Nat.cast_pow]
      exact (Real.log_lt_log_iff (pow_pos hZ_pos_r 2) (by exact_mod_cast B_k2_pos n X₁)).mp hZ2_log
    exact_mod_cast h1
  have hZ2_pos : 0 < (Z_k2 n Y₁) ^ 2 := pow_pos (Z_k2_pos n Y₁) 2
  have hquartic := (thm_4_2_part1_quartic_law hn8 hm hfund hk2).2.2.2.1
  have hdiv : A_k2 n X₁ / B_k2 n X₁ = (Z_k2 n Y₁) ^ 4 := by
    rw [hquartic, Nat.mul_add_div (B_k2_pos n X₁), Nat.div_eq_of_lt hZ2_lt_B, add_zero]
  have hmod : A_k2 n X₁ % B_k2 n X₁ = (Z_k2 n Y₁) ^ 2 := by
    rw [hquartic, Nat.mul_add_mod, Nat.mod_eq_of_lt hZ2_lt_B]
  refine ⟨hZ2_pos, hZ2_lt_B, hdiv, hmod, ?_⟩
  rw [hdiv, hmod]
  ring

/-- **Theorem 4.2(ii) (Second-Stage Consecutive Splitting and Dual Quartic Locks, eqs. 4.11–4.12)**:
Let `c₀ := Nat.gcd (X₁ - 1) (X₁ + 1) ∈ {1, 2}`. Then there exist coprime `Bm, Bp` and
coprime `Zm, Zp` such that:
- `Bm * Bp = B_k2 n X₁ / c₀ ^ 2` and `Zm * Zp = Z_k2 n Y₁`,
- `(X₁ - 1) / c₀ = Bm * Zm ^ 2`, `(X₁ + 1) / c₀ = Bp * Zp ^ 2`, `Bp * Zp ^ 2 - Bm * Zm ^ 2 = 2 / c₀`,
- `Bp * (Z_k2 n Y₁) ^ 2 = Bm * Zm ^ 4 + (2 / c₀) * Zm ^ 2`,
- `Bm * (Z_k2 n Y₁) ^ 2 = Bp * Zp ^ 4 - (2 / c₀) * Zp ^ 2`. -/
theorem thm_4_2_part2_dual_quartic {n m X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hm : Nat.factorial n + 1 = m ^ 2)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk2 : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2) :
    let c₀ := Nat.gcd (X₁ - 1) (X₁ + 1)
    (c₀ = 1 ∨ c₀ = 2) ∧
    ∃ Bm Bp Zm Zp : ℕ,
      0 < Bm ∧ 0 < Bp ∧ 0 < Zm ∧ 0 < Zp ∧
      Nat.Coprime Bm Bp ∧ Nat.Coprime Zm Zp ∧
      Bm * Bp = B_k2 n X₁ / c₀ ^ 2 ∧
      Zm * Zp = Z_k2 n Y₁ ∧
      (X₁ - 1) / c₀ = Bm * Zm ^ 2 ∧
      (X₁ + 1) / c₀ = Bp * Zp ^ 2 ∧
      Bp * Zp ^ 2 - Bm * Zm ^ 2 = 2 / c₀ ∧
      Bp * (Z_k2 n Y₁) ^ 2 = Bm * Zm ^ 4 + (2 / c₀) * Zm ^ 2 ∧
      Bm * (Z_k2 n Y₁) ^ 2 = Bp * Zp ^ 4 - (2 / c₀) * Zp ^ 2 := by
  have hn6 : n ≠ 6 := by omega
  obtain ⟨_, _, _, _, _, _, hfac_eq⟩ := k_eq_2_identities (by omega) hn6 hm hfund hk2
  obtain ⟨_, _, hBZ_eq, _, _, _⟩ := thm_4_2_part1_quartic_law hn hm hfund hk2
  have hX1_pos : 1 ≤ X₁ := hfund.1
  have hX1_gt1 : 1 < X₁ := by
    by_contra hle; have h1 : X₁ = 1 := by omega; rw [h1] at hfac_eq; simp at hfac_eq
    exact Nat.factorial_ne_zero n hfac_eq
  set c₀ := Nat.gcd (X₁ - 1) (X₁ + 1)
  have hc₀_dvd_2 : c₀ ∣ 2 := by
    have hd1 : c₀ ∣ X₁ - 1 := Nat.gcd_dvd_left _ _
    have hd2 : c₀ ∣ X₁ + 1 := Nat.gcd_dvd_right _ _
    have hd := Nat.dvd_sub hd2 hd1
    have hsub : (X₁ + 1) - (X₁ - 1) = 2 := by omega
    rwa [hsub] at hd
  have hc₀_pos : 0 < c₀ := Nat.gcd_pos_of_pos_right _ (by omega)
  have hc₀_12 : c₀ = 1 ∨ c₀ = 2 := by
    have := Nat.le_of_dvd (by norm_num) hc₀_dvd_2
    omega
  have hc₀_sq_dvd : c₀ ^ 2 ∣ B_k2 n X₁ := by
    rcases hc₀_12 with hc1 | hc2
    · rw [hc1]; simp
    · have h2d_sub : 2 ∣ X₁ - 1 := hc2 ▸ Nat.gcd_dvd_left _ _
      have hX_odd : X₁ % 2 = 1 := by omega
      have h_4_dvd_B : 4 ∣ B_k2 n X₁ := by
        unfold B_k2
        rw [if_pos hX_odd]
        have h2_ge4 : 4 ≤ padicValNat 2 (Nat.factorial n) := by
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
            (dvd_trans (by decide : 2 ^ 4 ∣ Nat.factorial 6) (Nat.factorial_dvd_factorial (by omega : 6 ≤ n)))
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : 2 ≤ padicValNat 2 (Nat.factorial n) - 2)) _
      rw [hc2]; simpa using h_4_dvd_B
  let u₁ := (X₁ - 1) / c₀
  let u₂ := (X₁ + 1) / c₀
  have hu₁_pos : 0 < u₁ := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hc₀_pos
  have hu₂_pos : 0 < u₂ := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) hc₀_pos
  have hcop_u : Nat.Coprime u₁ u₂ := Nat.coprime_div_gcd_div_gcd hc₀_pos
  have hdiff_u : u₂ - u₁ = 2 / c₀ := by
    have h1 : c₀ * u₁ = X₁ - 1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have h2 : c₀ * u₂ = X₁ + 1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    have h3 : c₀ * (u₂ - u₁) = 2 := by
      zify [hu₁_pos.le, hu₂_pos.le]
      have h1z : (c₀ : ℤ) * (u₁ : ℤ) = (X₁ : ℤ) - 1 := by exact_mod_cast h1
      have h2z : (c₀ : ℤ) * (u₂ : ℤ) = (X₁ : ℤ) + 1 := by exact_mod_cast h2
      nlinarith
    rcases hc₀_12 with hc1 | hc2 <;> omega
  have hprod_u : u₁ * u₂ = (B_k2 n X₁ / c₀ ^ 2) * (Z_k2 n Y₁) ^ 2 := by
    have h1 : c₀ * u₁ = X₁ - 1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have h2 : c₀ * u₂ = X₁ + 1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    have hdiff : (X₁ - 1) * (X₁ + 1) = q_n n * Y₁ ^ 2 := by
      zify [hX1_pos]; have : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
      linarith
    have hmul : c₀ ^ 2 * (u₁ * u₂) = c₀ ^ 2 * ((B_k2 n X₁ / c₀ ^ 2) * (Z_k2 n Y₁) ^ 2) := by
      calc c₀ ^ 2 * (u₁ * u₂) = (c₀ * u₁) * (c₀ * u₂) := by ring
        _ = (X₁ - 1) * (X₁ + 1) := by rw [h1, h2]
        _ = q_n n * Y₁ ^ 2 := hdiff
        _ = B_k2 n X₁ * (Z_k2 n Y₁) ^ 2 := hBZ_eq
        _ = (c₀ ^ 2 * (B_k2 n X₁ / c₀ ^ 2)) * (Z_k2 n Y₁) ^ 2 := by rw [Nat.mul_div_cancel' hc₀_sq_dvd]
        _ = c₀ ^ 2 * ((B_k2 n X₁ / c₀ ^ 2) * (Z_k2 n Y₁) ^ 2) := by ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hc₀_pos 2) hmul
  let B₀ := B_k2 n X₁ / c₀ ^ 2
  let Z := Z_k2 n Y₁
  let Bm := Nat.gcd u₁ B₀
  let Bp := Nat.gcd u₂ B₀
  let Zm := Nat.gcd u₁ Z
  let Zp := Nat.gcd u₂ Z
  have hB₀_pos : 0 < B₀ := Nat.div_pos (Nat.le_of_dvd (B_k2_pos n X₁) hc₀_sq_dvd) (pow_pos hc₀_pos 2)
  have hZ_pos : 0 < Z := Z_k2_pos n Y₁
  have hBm_pos : 0 < Bm := Nat.gcd_pos_of_pos_left _ hu₁_pos
  have hBp_pos : 0 < Bp := Nat.gcd_pos_of_pos_left _ hu₂_pos
  have hZm_pos : 0 < Zm := Nat.gcd_pos_of_pos_left _ hu₁_pos
  have hZp_pos : 0 < Zp := Nat.gcd_pos_of_pos_left _ hu₂_pos
  have hcop_B : Nat.Coprime Bm Bp := by
    refine Nat.coprime_of_dvd' (fun p hp h1 h2 => ?_)
    exact hp.not_dvd_one (Nat.dvd_gcd (dvd_trans h1 (Nat.gcd_dvd_left _ _))
      (dvd_trans h2 (Nat.gcd_dvd_left _ _)) |>.trans (by rw [hcop_u]))
  have hcop_Z : Nat.Coprime Zm Zp := by
    refine Nat.coprime_of_dvd' (fun p hp h1 h2 => ?_)
    exact hp.not_dvd_one (Nat.dvd_gcd (dvd_trans h1 (Nat.gcd_dvd_left _ _))
      (dvd_trans h2 (Nat.gcd_dvd_left _ _)) |>.trans (by rw [hcop_u]))
  have hB_prod : Bm * Bp = B₀ := by
    have hdvd_B : B₀ ∣ u₁ * u₂ := ⟨Z ^ 2, hprod_u.symm⟩
    exact (Nat.gcd_mul_gcd_of_coprime_of_dvd hcop_u hdvd_B).symm
  have hZ_prod : Zm * Zp = Z := by
    have hZ_dvd : Z ∣ u₁ * u₂ := by
      have : Z ^ 2 ∣ u₁ * u₂ := ⟨B₀, by rw [hprod_u]; ring⟩
      exact dvd_trans (dvd_pow_self Z (by norm_num)) this
    exact (Nat.gcd_mul_gcd_of_coprime_of_dvd hcop_u hZ_dvd).symm
  have hcop_BZ : Nat.Coprime B₀ Z := by
    refine Nat.coprime_of_dvd' (fun p hp hpB hpZ => ?_)
    have hp_pr := hp
    have hpZ_dvd : p ∣ Z := hpZ
    have hp_peven : p ∈ Peven n ∧ 3 ≤ p := by
      unfold Z Z_k2 at hpZ_dvd
      obtain ⟨q, hq, hqd⟩ := hp_pr.dvd_finset_prod_iff.mp hpZ_dvd
      have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
      have heq := (Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp (hp_pr.dvd_of_dvd_pow hqd)
      subst heq
      exact ⟨(Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2.1⟩
    have hpB_dvd : p ∣ B_k2 n X₁ := dvd_trans hpB (Nat.div_dvd_of_dvd hc₀_sq_dvd)
    unfold B_k2 at hpB_dvd
    have hp_Bstar : p ∣ B_star n := by
      split_ifs at hpB_dvd
      · rcases hp_pr.dvd_mul.mp hpB_dvd with hp2 | hpB'
        · have := (Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_two).mp (hp_pr.dvd_of_dvd_pow hp2)
          omega
        · exact hpB'
      · exact hpB_dvd
    unfold B_star at hp_Bstar
    obtain ⟨q, hq, hqd⟩ := hp_pr.dvd_finset_prod_iff.mp hp_Bstar
    have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
    have heq := (Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp (hp_pr.dvd_of_dvd_pow hqd)
    subst heq
    have h_odd := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.2
    have h_ev := (Finset.mem_filter.mp hp_peven.1).2.2
    exact h_odd h_ev
  have hu₁_eq : u₁ = Bm * Zm ^ 2 := by
    apply Nat.eq_of_factorization_eq hu₁_pos.ne' (mul_ne_zero hBm_pos.ne' (pow_ne_zero 2 hZm_pos.ne'))
    intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [Nat.factorization_mul hBm_pos.ne' (pow_ne_zero 2 hZm_pos.ne'), Nat.factorization_pow]
      simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hmin_B : (Nat.gcd u₁ B₀).factorization p = min (u₁.factorization p) (B₀.factorization p) := by
        rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp]
        exact Nat.padicValNat_gcd hu₁_pos.ne' hB₀_pos.ne'
      have hmin_Z : (Nat.gcd u₁ Z).factorization p = min (u₁.factorization p) (Z.factorization p) := by
        rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp]
        exact Nat.padicValNat_gcd hu₁_pos.ne' hZ_pos.ne'
      have heq_p : u₁.factorization p + u₂.factorization p = B₀.factorization p + 2 * Z.factorization p := by
        have h := congrArg (fun x => Nat.factorization x p) hprod_u
        rw [Nat.factorization_mul hu₁_pos.ne' hu₂_pos.ne',
            Nat.factorization_mul hB₀_pos.ne' (pow_ne_zero 2 hZ_pos.ne'),
            Nat.factorization_pow] at h
        simpa using h
      have hcop_u_p : u₁.factorization p = 0 ∨ u₂.factorization p = 0 := by
        by_contra hboth
        push Not at hboth
        have h1 : p ∣ u₁ := hp.dvd_iff_one_le_factorization hu₁_pos.ne' |>.mpr (by omega)
        have h2 : p ∣ u₂ := hp.dvd_iff_one_le_factorization hu₂_pos.ne' |>.mpr (by omega)
        exact hp.not_dvd_one (Nat.dvd_gcd h1 h2 |>.trans (by rw [hcop_u]))
      have hcop_BZ_p : B₀.factorization p = 0 ∨ Z.factorization p = 0 := by
        by_contra hboth
        push Not at hboth
        have h1 : p ∣ B₀ := hp.dvd_iff_one_le_factorization hB₀_pos.ne' |>.mpr (by omega)
        have h2 : p ∣ Z := hp.dvd_iff_one_le_factorization hZ_pos.ne' |>.mpr (by omega)
        exact hp.not_dvd_one (Nat.dvd_gcd h1 h2 |>.trans (by rw [hcop_BZ]))
      rw [hmin_B, hmin_Z]
      omega
    · have h0a : u₁.factorization p = 0 := by
        by_contra h0; exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
      have h0b : (Bm * Zm ^ 2).factorization p = 0 := by
        by_contra h0; exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
      omega
  have hu₂_eq : u₂ = Bp * Zp ^ 2 := by
    apply Nat.eq_of_factorization_eq hu₂_pos.ne' (mul_ne_zero hBp_pos.ne' (pow_ne_zero 2 hZp_pos.ne'))
    intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [Nat.factorization_mul hBp_pos.ne' (pow_ne_zero 2 hZp_pos.ne'), Nat.factorization_pow]
      simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hmin_B : (Nat.gcd u₂ B₀).factorization p = min (u₂.factorization p) (B₀.factorization p) := by
        rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp]
        exact Nat.padicValNat_gcd hu₂_pos.ne' hB₀_pos.ne'
      have hmin_Z : (Nat.gcd u₂ Z).factorization p = min (u₂.factorization p) (Z.factorization p) := by
        rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp]
        exact Nat.padicValNat_gcd hu₂_pos.ne' hZ_pos.ne'
      have heq_p : u₁.factorization p + u₂.factorization p = B₀.factorization p + 2 * Z.factorization p := by
        have h := congrArg (fun x => Nat.factorization x p) hprod_u
        rw [Nat.factorization_mul hu₁_pos.ne' hu₂_pos.ne',
            Nat.factorization_mul hB₀_pos.ne' (pow_ne_zero 2 hZ_pos.ne'),
            Nat.factorization_pow] at h
        simpa using h
      have hcop_u_p : u₁.factorization p = 0 ∨ u₂.factorization p = 0 := by
        by_contra hboth
        push Not at hboth
        have h1 : p ∣ u₁ := hp.dvd_iff_one_le_factorization hu₁_pos.ne' |>.mpr (by omega)
        have h2 : p ∣ u₂ := hp.dvd_iff_one_le_factorization hu₂_pos.ne' |>.mpr (by omega)
        exact hp.not_dvd_one (Nat.dvd_gcd h1 h2 |>.trans (by rw [hcop_u]))
      have hcop_BZ_p : B₀.factorization p = 0 ∨ Z.factorization p = 0 := by
        by_contra hboth
        push Not at hboth
        have h1 : p ∣ B₀ := hp.dvd_iff_one_le_factorization hB₀_pos.ne' |>.mpr (by omega)
        have h2 : p ∣ Z := hp.dvd_iff_one_le_factorization hZ_pos.ne' |>.mpr (by omega)
        exact hp.not_dvd_one (Nat.dvd_gcd h1 h2 |>.trans (by rw [hcop_BZ]))
      rw [hmin_B, hmin_Z]
      omega
    · have h0a : u₂.factorization p = 0 := by
        by_contra h0; exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
      have h0b : (Bp * Zp ^ 2).factorization p = 0 := by
        by_contra h0; exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
      omega
  have hdiff_BZ : Bp * Zp ^ 2 - Bm * Zm ^ 2 = 2 / c₀ := by
    rw [← hu₁_eq, ← hu₂_eq]; exact hdiff_u
  have hq_minus : Bp * Z ^ 2 = Bm * Zm ^ 4 + (2 / c₀) * Zm ^ 2 := by
    have h1 : Bp * Zp ^ 2 = Bm * Zm ^ 2 + (2 / c₀) := by omega
    calc Bp * Z ^ 2 = Bp * (Zm * Zp) ^ 2 := by rw [hZ_prod]
      _ = (Bp * Zp ^ 2) * Zm ^ 2 := by ring
      _ = (Bm * Zm ^ 2 + 2 / c₀) * Zm ^ 2 := by rw [h1]
      _ = Bm * Zm ^ 4 + (2 / c₀) * Zm ^ 2 := by ring
  have hq_plus : Bm * Z ^ 2 = Bp * Zp ^ 4 - (2 / c₀) * Zp ^ 2 := by
    have h1 : Bm * Zm ^ 2 + 2 / c₀ = Bp * Zp ^ 2 := by omega
    have hle : (2 / c₀) * Zp ^ 2 ≤ Bp * Zp ^ 4 := by
      have : 2 / c₀ ≤ Bp * Zp ^ 2 := by omega
      calc (2 / c₀) * Zp ^ 2 ≤ (Bp * Zp ^ 2) * Zp ^ 2 := Nat.mul_le_mul_right _ this
        _ = Bp * Zp ^ 4 := by ring
    zify [hle]
    have h1z : (Bm : ℤ) * (Zm : ℤ) ^ 2 + (2 / c₀ : ℕ) = (Bp : ℤ) * (Zp : ℤ) ^ 2 := by exact_mod_cast h1
    have hZz : (Z : ℤ) = (Zm : ℤ) * (Zp : ℤ) := by exact_mod_cast hZ_prod.symm
    rw [hZz]
    nlinarith
  exact ⟨hc₀_12, Bm, Bp, Zm, Zp, hBm_pos, hBp_pos, hZm_pos, hZp_pos,
    hcop_B, hcop_Z, hB_prod, hZ_prod, hu₁_eq, hu₂_eq, hdiff_BZ, hq_minus, hq_plus⟩

/-- **Theorem 4.2(ii) (Euclidean Quotient-Remainder Locks and `log B_∓` Asymptotics, eqs. 4.13, 4.15)**:
For every `ε ∈ (0, 1/6)`, for all sufficiently large `n` with a `k = 2` solution `(n, m)`, the
second-stage factors `Bm, Bp, Zm, Zp` satisfy:
1. `(1/4 - ε) n log n ≤ log B_∓ ≤ (1/4 + ε) n log n` (eq. 4.15),
2. `(2 / c₀) * Zm ^ 2 < Bm` and `(2 / c₀) * Zp ^ 2 < Bp`,
3. `(Bp * Z^2) / Bm = Zm^4` and `(Bm * Z^2 + Bp - 1) / Bp = Zp^4` (eq. 4.13). -/
theorem thm_4_2_part2_euclidean_locks (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 6) :
    ∃ N₀ : ℕ, ∀ n m X₁ Y₁ : ℕ, N₀ ≤ n →
      Nat.factorial n + 1 = m ^ 2 →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2 →
      let c₀ := Nat.gcd (X₁ - 1) (X₁ + 1)
      ∃ Bm Bp Zm Zp : ℕ,
        0 < Bm ∧ 0 < Bp ∧ 0 < Zm ∧ 0 < Zp ∧
        Nat.Coprime Bm Bp ∧ Nat.Coprime Zm Zp ∧
        Bm * Bp = B_k2 n X₁ / c₀ ^ 2 ∧
        Zm * Zp = Z_k2 n Y₁ ∧
        (X₁ - 1) / c₀ = Bm * Zm ^ 2 ∧
        (X₁ + 1) / c₀ = Bp * Zp ^ 2 ∧
        (1 / 4 - ε) * ((n : ℝ) * Real.log (n : ℝ)) ≤ Real.log (Bm : ℝ) ∧
        Real.log (Bm : ℝ) ≤ (1 / 4 + ε) * ((n : ℝ) * Real.log (n : ℝ)) ∧
        (1 / 4 - ε) * ((n : ℝ) * Real.log (n : ℝ)) ≤ Real.log (Bp : ℝ) ∧
        Real.log (Bp : ℝ) ≤ (1 / 4 + ε) * ((n : ℝ) * Real.log (n : ℝ)) ∧
        (2 / c₀) * Zm ^ 2 < Bm ∧
        (2 / c₀) * Zp ^ 2 < Bp ∧
        (Bp * (Z_k2 n Y₁) ^ 2) / Bm = Zm ^ 4 ∧
        (Bm * (Z_k2 n Y₁) ^ 2 + Bp - 1) / Bp = Zp ^ 4 := by
  obtain ⟨N₁, hN₁⟩ := Z_k2_log_upper_bound_clean (ε / 2) (by linarith)
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_all : ∀ᶠ n : ℕ in atTop,
      max N₁ 8 ≤ n ∧
      (4 / ε) * (1 + 2 * Real.log 2) ≤ Real.log (n : ℝ) ∧
      10 ≤ (1 / 4 - ε) * ((n : ℝ) * Real.log (n : ℝ)) := by
    have h1 := hlog_inf.eventually (eventually_ge_atTop ((4 / ε) * (1 + 2 * Real.log 2)))
    have h2 : ∀ᶠ n : ℕ in atTop, 10 ≤ (1 / 4 - ε) * ((n : ℝ) * Real.log (n : ℝ)) := by
      have ht : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ hlog_inf
      exact (Tendsto.const_mul_atTop (by linarith : 0 < 1 / 4 - ε) ht).eventually (eventually_ge_atTop 10)
    exact (eventually_ge_atTop (max N₁ 8)).and (h1.and h2)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h_all
  refine ⟨N₀, fun n m X₁ Y₁ hn hm hfund hk2 => ?_⟩
  obtain ⟨hmax, hlog_ge, h10⟩ := hN₀ n hn
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hmax
  have hn8 : 8 ≤ n := le_trans (le_max_right _ _) hmax
  have hZ_log := hN₁ n m X₁ Y₁ hn1 hm hfund hk2
  have hpart2 := thm_4_2_part2_dual_quartic hn8 hm hfund hk2
  obtain ⟨hc₀_12, Bm, Bp, Zm, Zp, hBm_pos, hBp_pos, hZm_pos, hZp_pos,
    hcop_B, hcop_Z, hB_prod, hZ_prod, hu₁_eq, hu₂_eq, _, hq_minus, hq_plus⟩ := hpart2
  have hn6 : n ≠ 6 := by omega
  obtain ⟨_, _, _, _, _, _, hfac_eq⟩ := k_eq_2_identities (by omega) hn6 hm hfund hk2
  have hX1_pos : 1 ≤ X₁ := hfund.1
  have hfac_lo : (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) ≤ Real.log ((Nat.factorial n : ℕ) : ℝ) :=
    (n_log_n_sub_n_le_log_factorial n (by omega)).1
  have hlog_X1_lo : (1 / 4 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) - (n : ℝ) - Real.log 2 ≤ Real.log (X₁ : ℝ) := by
    have h1 : ((Nat.factorial n : ℕ) : ℝ) ≤ 4 * (X₁ : ℝ) ^ 4 := by
      have h_nat : Nat.factorial n ≤ 4 * X₁ ^ 4 := by
        rw [hfac_eq]
        have : (X₁ - 1) * (X₁ + 1) ≤ X₁ ^ 2 := by zify [hX1_pos]; nlinarith
        nlinarith
      exact_mod_cast h_nat
    have h2 := Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) h1
    rw [Real.log_mul (by norm_num) (pow_ne_zero 4 (by positivity)), Real.log_pow,
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h2
    linarith
  have hlog_X1_hi : Real.log (X₁ : ℝ) ≤ (1 / 4 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by
    have h1 : (X₁ : ℝ) ^ 4 ≤ ((Nat.factorial n : ℕ) : ℝ) := by
      have h_nat : X₁ ^ 4 ≤ Nat.factorial n := by
        rw [hfac_eq]
        have hX2 : X₁ ^ 2 ≤ 4 * (X₁ - 1) * (X₁ + 1) := by
          zify [hX1_pos]; nlinarith
        nlinarith
      exact_mod_cast h_nat
    have h2 := Real.log_le_log (pow_pos (by positivity) 4) h1
    rw [Real.log_pow] at h2
    have hfac_hi : Real.log ((Nat.factorial n : ℕ) : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
      have hle : Nat.factorial n ≤ n ^ n := Nat.factorial_le_pow n
      have h1' := Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
        (by exact_mod_cast hle : ((Nat.factorial n : ℕ) : ℝ) ≤ ((n ^ n : ℕ) : ℝ))
      rw [Nat.cast_pow, Real.log_pow] at h1'
      exact h1'
    linarith
  have hn_err : (n : ℝ) + 2 * Real.log 2 ≤ (ε / 4) * ((n : ℝ) * Real.log (n : ℝ)) := by
    have h1 : 1 + 2 * Real.log 2 ≤ (ε / 4) * Real.log (n : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlog_ge (by positivity : 0 ≤ ε / 4)
      have heq : (ε / 4) * ((4 / ε) * (1 + 2 * Real.log 2)) = 1 + 2 * Real.log 2 := by
        field_simp [hε0.ne']
      linarith
    have h2 : (n : ℝ) * (1 + 2 * Real.log 2) ≤ (n : ℝ) * ((ε / 4) * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : (n : ℝ) + 2 * Real.log 2 ≤ (n : ℝ) * (1 + 2 * Real.log 2) := by
      have : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
      nlinarith
    linarith
  have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h_bounds : ∀ B_i Z_i u_i : ℕ, 0 < B_i → 0 < Z_i → Z_i ∣ Z_k2 n Y₁ →
      u_i = B_i * Z_i ^ 2 → (X₁ - 1) / 2 ≤ u_i → u_i ≤ X₁ + 1 →
      (1 / 4 - ε) * ((n : ℝ) * Real.log (n : ℝ)) ≤ Real.log (B_i : ℝ) ∧
      Real.log (B_i : ℝ) ≤ (1 / 4 + ε) * ((n : ℝ) * Real.log (n : ℝ)) ∧
      2 * Z_i ^ 2 < B_i := by
    intro B_i Z_i u_i hB_pos hZ_pos hZ_dvd hu_eq hu_lo hu_hi
    have hZi_le : (Z_i : ℝ) ≤ (Z_k2 n Y₁ : ℝ) := by exact_mod_cast Nat.le_of_dvd (Z_k2_pos n Y₁) hZ_dvd
    have hZ_i_log : 2 * Real.log (Z_i : ℝ) ≤ (ε / 4) * ((n : ℝ) * Real.log (n : ℝ)) := by
      have h1 := Real.log_le_log (by exact_mod_cast hZ_pos) hZi_le
      linarith
    have hu_ge : (X₁ : ℝ) / 4 ≤ (u_i : ℝ) := by
      have h1 : X₁ ≤ 4 * u_i := by omega
      have h1r : (X₁ : ℝ) ≤ 4 * (u_i : ℝ) := by exact_mod_cast h1
      linarith
    have hlog_u_lo : Real.log (X₁ : ℝ) - 2 * Real.log 2 ≤ Real.log (u_i : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hu_ge
      rw [Real.log_div (by positivity) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h1
      linarith
    have hlog_u_hi : Real.log (u_i : ℝ) ≤ Real.log (X₁ : ℝ) + Real.log 2 := by
      have h1 : (u_i : ℝ) ≤ 2 * (X₁ : ℝ) := by
        have : u_i ≤ 2 * X₁ := by omega
        exact_mod_cast this
      have h2 := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (by omega : u_i ≠ 0)) h1
      rw [Real.log_mul (by norm_num) (by positivity)] at h2
      linarith
    have hlog_u_eq : Real.log (u_i : ℝ) = Real.log (B_i : ℝ) + 2 * Real.log (Z_i : ℝ) := by
      rw [hu_eq, Nat.cast_mul, Real.log_mul (by exact_mod_cast hB_pos.ne') (pow_ne_zero 2 (by exact_mod_cast hZ_pos.ne')),
          Nat.cast_pow, Real.log_pow]
      ring
    have hZ_i_nn : 0 ≤ 2 * Real.log (Z_i : ℝ) := by
      have : (1 : ℝ) ≤ (Z_i : ℝ) := by exact_mod_cast hZ_pos
      exact mul_nonneg (by norm_num) (Real.log_nonneg this)
    have hB_lo : (1 / 4 - ε) * ((n : ℝ) * Real.log (n : ℝ)) ≤ Real.log (B_i : ℝ) := by linarith
    have hB_hi : Real.log (B_i : ℝ) ≤ (1 / 4 + ε) * ((n : ℝ) * Real.log (n : ℝ)) := by linarith
    have hlt_log : Real.log (2 * (Z_i : ℝ) ^ 2) < Real.log (B_i : ℝ) := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero 2 (by exact_mod_cast hZ_pos.ne')), Real.log_pow]
      have hlog2_lt1 : Real.log 2 < 1 := by
        rw [Real.log_lt_iff_lt_exp (by norm_num)]
        linarith [Real.exp_one_gt_d9]
      have h14 : (ε / 4 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) < (1 / 4 - ε) * ((n : ℝ) * Real.log (n : ℝ)) - 1 := by
        have hpos : 0 < (n : ℝ) * Real.log (n : ℝ) := by
          have : 0 < 1 / 4 - ε := by linarith
          nlinarith
        nlinarith
      linarith
    have hlt_r : (2 * Z_i ^ 2 : ℝ) < (B_i : ℝ) := by
      rw [← Nat.cast_pow, ← Nat.cast_ofNat (n := 2), ← Nat.cast_mul]
      exact_mod_cast (Real.log_lt_log_iff (by positivity) (by exact_mod_cast hB_pos)).mp hlt_log
    exact ⟨hB_lo, hB_hi, by exact_mod_cast hlt_r⟩
  set c₀ := Nat.gcd (X₁ - 1) (X₁ + 1)
  have hc₀_le2 : c₀ ≤ 2 := by rcases hc₀_12 with h | h <;> omega
  have hb_minus := h_bounds Bm Zm ((X₁ - 1) / c₀) hBm_pos hZm_pos ⟨Zp, hZ_prod.symm⟩ hu₁_eq.symm
    (Nat.div_le_div_left hc₀_le2 (by omega)) (Nat.div_le_self _ _ |>.trans (by omega))
  have hb_plus := h_bounds Bp Zp ((X₁ + 1) / c₀) hBp_pos hZp_pos ⟨Zm, by rw [← hZ_prod, mul_comm]⟩ hu₂_eq.symm
    (by have := Nat.div_le_div_left hc₀_le2 (by omega : 0 < c₀); have : (X₁ - 1) / 2 ≤ (X₁ + 1) / 2 := Nat.div_le_div_right (by omega); omega)
    (Nat.div_le_self _ _)
  have h2c₀_minus : (2 / c₀) * Zm ^ 2 < Bm := by
    have : 2 / c₀ ≤ 2 := Nat.div_le_self 2 c₀
    nlinarith [hb_minus.2.2]
  have h2c₀_plus : (2 / c₀) * Zp ^ 2 < Bp := by
    have : 2 / c₀ ≤ 2 := Nat.div_le_self 2 c₀
    nlinarith [hb_plus.2.2]
  have hlock_minus : (Bp * (Z_k2 n Y₁) ^ 2) / Bm = Zm ^ 4 := by
    rw [hq_minus, Nat.mul_add_div hBm_pos, Nat.div_eq_of_lt h2c₀_minus, add_zero]
  have hlock_plus : (Bm * (Z_k2 n Y₁) ^ 2 + Bp - 1) / Bp = Zp ^ 4 := by
    have h_eq : Bm * (Z_k2 n Y₁) ^ 2 + Bp - 1 = Bp * Zp ^ 4 + (Bp - (2 / c₀) * Zp ^ 2 - 1) := by
      have hle1 : (2 / c₀) * Zp ^ 2 ≤ Bp * Zp ^ 4 := by
        have : 1 ≤ Zp ^ 2 := Nat.one_le_pow 2 Zp hZp_pos
        nlinarith [h2c₀_plus]
      omega
    have h_rem_lt : Bp - (2 / c₀) * Zp ^ 2 - 1 < Bp := by omega
    rw [h_eq, Nat.mul_add_div hBp_pos, Nat.div_eq_of_lt h_rem_lt, add_zero]
  exact ⟨Bm, Bp, Zm, Zp, hBm_pos, hBp_pos, hZm_pos, hZp_pos, hcop_B, hcop_Z, hB_prod, hZ_prod,
    hu₁_eq, hu₂_eq, hb_minus.1, hb_minus.2.1, hb_plus.1, hb_plus.2.1,
    h2c₀_minus, h2c₀_plus, hlock_minus, hlock_plus⟩

private lemma log_nat_eq_sum_primeFactors {N : ℕ} (hN : 0 < N) :
    Real.log (N : ℝ) = ∑ p ∈ N.primeFactors, (padicValNat p N : ℝ) * Real.log (p : ℝ) := by
  have hprod : ∏ p ∈ N.primeFactors, p ^ N.factorization p = N := by
    apply Nat.eq_of_factorization_eq
    · exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
    · exact hN.ne'
    · intro q
      rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)]
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      by_cases hq : q ∈ N.primeFactors
      · have hq_pr := Nat.prime_of_mem_primeFactors hq
        rw [Finset.sum_eq_single q]
        · rw [hq_pr.factorization_self, mul_one]
        · intro p hp hpq
          have hp_pr := Nat.prime_of_mem_primeFactors hp
          rw [hp_pr.factorization, Finsupp.single_apply, if_neg hpq, mul_zero]
        · intro habs; exact absurd hq habs
      · rw [Finset.sum_eq_zero]
        · symm
          by_contra h0
          exact hq (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors (Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr h0),
            (Nat.prime_of_mem_primeFactors (Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr h0)).dvd_iff_one_le_factorization hN.ne' |>.mpr (Nat.pos_of_ne_zero h0), hN.ne'⟩)
        · intro p hp
          have hp_pr := Nat.prime_of_mem_primeFactors hp
          have hpq : p ≠ q := fun h => hq (h ▸ hp)
          rw [hp_pr.factorization, Finsupp.single_apply, if_neg hpq, mul_zero]
  conv_lhs => rw [← hprod]
  push_cast
  rw [Real.log_prod (fun p hp => pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero))]
  apply Finset.sum_congr rfl
  intro p hp
  have hp_pr := Nat.prime_of_mem_primeFactors hp
  rw [Real.log_pow, Nat.factorization_def _ hp_pr]

private lemma odd_prime_core_properties {n m X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hm : Nat.factorial n + 1 = m ^ 2)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk2 : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2)
    {B_i B_other Z_i u_i δ : ℕ} (hB_pos : 0 < B_i) (hBo_pos : 0 < B_other) (hZ_pos : 0 < Z_i)
    (hZ_dvd : Z_i ∣ Z_k2 n Y₁)
    (hB_mul : B_i * B_other = B_k2 n X₁ / (Nat.gcd (X₁ - 1) (X₁ + 1)) ^ 2)
    (hB_cop : Nat.Coprime B_i B_other)
    (hc₀_12 : Nat.gcd (X₁ - 1) (X₁ + 1) = 1 ∨ Nat.gcd (X₁ - 1) (X₁ + 1) = 2)
    (hu_eq : u_i = B_i * Z_i ^ 2) (hδ_eq : δ = sfCore (Nat.gcd (X₁ - 1) (X₁ + 1) * u_i)) :
    (∀ p ∈ B_i.primeFactors, p ≠ 2 →
      p ∈ Podd n ∧ padicValNat p B_i = padicValNat p (Nat.factorial n) ∧ p ∣ δ) ∧
    padicValNat 2 B_i ≤ padicValNat 2 (Nat.factorial n) := by
  have hq1 := thm_4_2_part1_quartic_law hn hm hfund hk2
  have hX1_pos : 1 ≤ X₁ := hfund.1
  set c₀ := Nat.gcd (X₁ - 1) (X₁ + 1)
  have hc₀_pos : 0 < c₀ := by rcases hc₀_12 with h | h <;> omega
  have hc₀_sq_dvd : c₀ ^ 2 ∣ B_k2 n X₁ := by
    rcases hc₀_12 with hc1 | hc2
    · rw [hc1]; simp
    · have h2d_sub : 2 ∣ X₁ - 1 := hc2 ▸ Nat.gcd_dvd_left _ _
      have hX_odd : X₁ % 2 = 1 := by omega
      unfold B_k2
      rw [hc2, if_pos hX_odd]
      have h2_ge4 : 4 ≤ padicValNat 2 (Nat.factorial n) := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
          (dvd_trans (by decide : 2 ^ 4 ∣ Nat.factorial 6) (Nat.factorial_dvd_factorial (by omega : 6 ≤ n)))
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : 2 ≤ padicValNat 2 (Nat.factorial n) - 2)) _
  have hB_mul_eq : B_i * B_other * c₀ ^ 2 = B_k2 n X₁ := by
    rw [hB_mul, mul_comm (B_k2 n X₁ / c₀ ^ 2) (c₀ ^ 2), Nat.mul_div_cancel' hc₀_sq_dvd]
  have hB_dvd : B_i ∣ B_k2 n X₁ := by
    rw [← hB_mul_eq]
    exact dvd_mul_of_dvd_left (dvd_mul_right B_i B_other) (c₀ ^ 2)
  have h_all_fac : A_k2 n X₁ * B_k2 n X₁ * 4 = Nat.factorial n := by
    have h2_le : 2 ≤ padicValNat 2 (Nat.factorial n) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
        (dvd_trans (by decide : 2 ^ 2 ∣ 24) (Nat.factorial_dvd_factorial (by omega : 4 ≤ n)))
    have h1' : A_k2 n X₁ * B_k2 n X₁ = A_star n * B_star n * 2 ^ (padicValNat 2 (Nat.factorial n) - 2) := by
      unfold A_k2 B_k2; split_ifs <;> ring
    have hpow : 2 ^ (padicValNat 2 (Nat.factorial n) - 2) * 4 = 2 ^ padicValNat 2 (Nat.factorial n) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel h2_le]
    calc A_k2 n X₁ * B_k2 n X₁ * 4
        = A_star n * B_star n * 2 ^ (padicValNat 2 (Nat.factorial n) - 2) * 4 := by rw [h1']
      _ = A_star n * B_star n * (2 ^ (padicValNat 2 (Nat.factorial n) - 2) * 4) := by ring
      _ = A_star n * B_star n * 2 ^ padicValNat 2 (Nat.factorial n) := by rw [hpow]
      _ = Nat.factorial n := A_star_mul_B_star n
  have hB_dvd_fac : B_i ∣ Nat.factorial n := by
    have h1 : B_k2 n X₁ ∣ Nat.factorial n := by
      rw [← h_all_fac]
      exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    exact dvd_trans hB_dvd h1
  have hv2_le : padicValNat 2 B_i ≤ padicValNat 2 (Nat.factorial n) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp hB_dvd_fac
  refine ⟨?_, hv2_le⟩
  intro p hp_mem hp2
  have hp_pr := Nat.prime_of_mem_primeFactors hp_mem
  haveI : Fact p.Prime := ⟨hp_pr⟩
  have hp3 : 3 ≤ p := by have := hp_pr.two_le; omega
  have hp_B : p ∣ B_i := Nat.dvd_of_mem_primeFactors hp_mem
  have hp_Bk2 : p ∣ B_k2 n X₁ := dvd_trans hp_B hB_dvd
  have hp_Bstar : p ∣ B_star n := by
    unfold B_k2 at hp_Bk2
    split_ifs at hp_Bk2
    · rcases hp_pr.dvd_mul.mp hp_Bk2 with h2 | hB'
      · have := (Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_two).mp (hp_pr.dvd_of_dvd_pow h2); omega
      · exact hB'
    · exact hp_Bk2
  have hp_Podd : p ∈ Podd n := by
    unfold B_star at hp_Bstar
    obtain ⟨q, hq, hqd⟩ := (Prime.dvd_finset_prod_iff hp_pr.prime _).mp hp_Bstar
    have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
    have heq := (Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp (hp_pr.dvd_of_dvd_pow hqd)
    subst heq
    exact (Finset.mem_filter.mp hq).1
  have hp_val_Bk2 : padicValNat p (B_k2 n X₁) = padicValNat p (Nat.factorial n) := by
    have hnd4 : ¬ p ∣ 4 := fun h => by
      have := hp_pr.dvd_of_dvd_pow (by simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using h)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have hndA : ¬ p ∣ A_k2 n X₁ := fun h =>
      hp_pr.not_dvd_one (Nat.dvd_gcd h hp_Bk2 |>.trans (by rw [hq1.1]))
    rw [← h_all_fac, padicValNat.mul (mul_ne_zero (A_k2_pos n X₁).ne' (B_k2_pos n X₁).ne') (by norm_num),
        padicValNat.mul (A_k2_pos n X₁).ne' (B_k2_pos n X₁).ne',
        padicValNat.eq_zero_of_not_dvd hndA, padicValNat.eq_zero_of_not_dvd hnd4]
    simp
  have hp_val_Bi : padicValNat p B_i = padicValNat p (Nat.factorial n) := by
    have hnd_Bo : ¬ p ∣ B_other := fun h =>
      hp_pr.not_dvd_one (Nat.dvd_gcd hp_B h |>.trans (by rw [hB_cop]))
    have hnd_c0 : ¬ p ∣ c₀ ^ 2 := by
      intro hc
      have hpc0 := hp_pr.dvd_of_dvd_pow hc
      rcases hc₀_12 with h1 | h2
      · rw [h1] at hpc0; exact hp_pr.not_dvd_one hpc0
      · rw [h2] at hpc0; have := (Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_two).mp hpc0; omega
    rw [← hp_val_Bk2, ← hB_mul_eq,
        padicValNat.mul (mul_ne_zero hB_pos.ne' hBo_pos.ne') (by rcases hc₀_12 with h | h <;> simp [c₀, h]),
        padicValNat.mul hB_pos.ne' hBo_pos.ne',
        padicValNat.eq_zero_of_not_dvd hnd_Bo, padicValNat.eq_zero_of_not_dvd hnd_c0]
    simp
  have hp_nd_Z : ¬ p ∣ Z_i := by
    intro hpZ
    have hpZ' : p ∣ Z_k2 n Y₁ := dvd_trans hpZ hZ_dvd
    unfold Z_k2 at hpZ'
    obtain ⟨q, hq, hqd⟩ := (Prime.dvd_finset_prod_iff hp_pr.prime _).mp hpZ'
    have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
    have heq := (Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp (hp_pr.dvd_of_dvd_pow hqd)
    subst heq
    exact (Finset.mem_filter.mp hp_Podd).2.2 (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.2
  have hp_nd_c0 : ¬ p ∣ c₀ := by
    rcases hc₀_12 with h1 | h2
    · rw [h1]; exact hp_pr.not_dvd_one
    · rw [h2]; intro h; have := (Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_two).mp h; omega
  have hp_dvd_δ : p ∣ δ := by
    have hu_pos : 0 < u_i := by rw [hu_eq]; exact mul_pos hB_pos (pow_pos hZ_pos 2)
    have hcu_pos : 0 < c₀ * u_i := mul_pos hc₀_pos hu_pos
    have hcore_eq := eq_sfCore_mul_sqPart_sq hcu_pos
    have hδ_ne : sfCore (c₀ * u_i) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hcore_eq; omega
    have hsq_ne : (sqPart (c₀ * u_i)) ^ 2 ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hcore_eq; omega
    have hsq_p_ne : sqPart (c₀ * u_i) ≠ 0 := by
      intro h0; apply hsq_ne; rw [h0, sq, mul_zero]
    have hval_cu : padicValNat p (c₀ * u_i) = padicValNat p (Nat.factorial n) := by
      rw [padicValNat.mul hc₀_pos.ne' hu_pos.ne', padicValNat.eq_zero_of_not_dvd hp_nd_c0, zero_add,
          hu_eq, padicValNat.mul hB_pos.ne' (pow_ne_zero 2 hZ_pos.ne'),
          sq, padicValNat.mul hZ_pos.ne' hZ_pos.ne', padicValNat.eq_zero_of_not_dvd hp_nd_Z,
          add_zero, add_zero, hp_val_Bi]
    have hval_split : padicValNat p (c₀ * u_i) = padicValNat p (sfCore (c₀ * u_i)) + 2 * padicValNat p (sqPart (c₀ * u_i)) := by
      conv_lhs => rw [hcore_eq]
      rw [padicValNat.mul hδ_ne hsq_ne, sq, padicValNat.mul hsq_p_ne hsq_p_ne]
      ring
    have hodd_val : ¬ 2 ∣ padicValNat p (Nat.factorial n) := (Finset.mem_filter.mp hp_Podd).2.2
    have hval_δ_pos : 0 < padicValNat p (sfCore (c₀ * u_i)) := by omega
    rw [hδ_eq]
    exact (padicValNat_dvd_iff_le hδ_ne).mpr (by omega)
  exact ⟨hp_Podd, hp_val_Bi, hp_dvd_δ⟩

/-- **Theorem 4.2(iii) (Power-Band Equidistribution Upgrade on Midpoint Cores, eq. 4.14)**:
For every `ε ∈ (0, 1/6)`, for all sufficiently large `n` with a `k = 2` solution `(n, m)` to
`n! + 1 = m^2`, both midpoint cores `δ₁ = sfCore (X₁ - 1)` and `δ₂ = sfCore (X₁ + 1)` satisfy:
1. `∃ p ∣ δ_i, p.Prime ∧ (n : ℝ) ^ (1/2 - ε) < p` (`P^+(δ_i) ≥ n^{1/2 - o(1)}`),
2. `(δ_i.primeFactors.card : ℝ) ≥ (ε / 5) * (n : ℝ) ^ (1/2 - ε)` (`ω(δ_i) ≥ n^{1/2 - o(1)}`),
3. `Real.log (δ_i : ℝ) ≥ (ε / 15) * (n : ℝ) ^ (1/2 - ε) * Real.log n` (`δ_i ≥ exp(n^{1/2 - o(1)})`). -/
theorem thm_4_2_part3_midpoint_core_bounds (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 6) :
    ∃ N₀ : ℕ, ∀ n m X₁ Y₁ : ℕ, N₀ ≤ n →
      Nat.factorial n + 1 = m ^ 2 →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2 →
      ∀ δ ∈ ({sfCore (X₁ - 1), sfCore (X₁ + 1)} : Finset ℕ),
        (∃ p : ℕ, p.Prime ∧ p ∣ δ ∧ (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ)) ∧
        (ε / 5) * (n : ℝ) ^ (1 / 2 - ε) ≤ (δ.primeFactors.card : ℝ) ∧
        (ε / 15) * (n : ℝ) ^ (1 / 2 - ε) * Real.log (n : ℝ) ≤ Real.log (δ : ℝ) := by
  have h_band := multi_modulus_power_band_equidistribution 2 1 (by norm_num) 0 (1 / 2 - ε)
    le_rfl (by linarith) (by linarith)
  have h_band_ev : ∀ᶠ n : ℕ in atTop,
      ∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
        p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε) ∧
        padicValNat p (Nat.factorial n) ≡ 1 [MOD 2]),
        (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
      (1 / 4 - ε / 2 + ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) := by
    have h1 := h_band.bound (by positivity : (0 : ℝ) < ε / 100)
    filter_upwards [h1, eventually_ge_atTop 2] with n hn hn2
    have hn_log_nn : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
    rw [Real.norm_of_nonneg hn_log_nn] at hn
    have h2 := (abs_le.mp (Real.norm_eq_abs _ ▸ hn)).2
    have hsub : (1 / 2 - ε - 0) / ((2 : ℕ) : ℝ) = 1 / 4 - ε / 2 := by norm_num; ring
    rw [hsub] at h2
    linarith
  have h_Delta_ev : ∀ᶠ n : ℕ in atTop,
      |Delta_parity n| ≤ (ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) := by
    have h1 := Delta_parity_isLittleO_mul_log.bound (by positivity : (0 : ℝ) < ε / 100)
    filter_upwards [h1, eventually_ge_atTop 2] with n hn hn2
    have hn_log_nn : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
    rw [Real.norm_of_nonneg hn_log_nn] at hn
    simpa [Real.norm_eq_abs] using hn
  have h_n_ev : ∀ᶠ n : ℕ in atTop,
      8 ≤ n ∧
      (n : ℝ) + 4 * Real.log 2 + 2 * Real.log 2 ≤ (ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) ∧
      (n : ℝ) ^ (1 / 2 - ε) - 1 ≥ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 - ε) ∧
      (0 : ℝ) < (n : ℝ) ^ (1 / 2 - ε) ∧
      1 < Real.log (n : ℝ) := by
    have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hrpow_inf : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 - ε)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 / 2 - ε)).comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 8,
      hlog_inf.eventually (eventually_ge_atTop ((100 / ε) * (1 + 6 * Real.log 2))),
      hlog_inf.eventually (eventually_gt_atTop 1),
      hrpow_inf.eventually (eventually_ge_atTop 2)] with n hn hn_big hlog1 hrpow2
    dsimp only at hn_big hlog1 hrpow2
    have hn_ge8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog_ge : (100 / ε) * (1 + 6 * Real.log 2) ≤ Real.log (n : ℝ) := hn_big
    have h1 : 1 + 6 * Real.log 2 ≤ (ε / 100) * Real.log (n : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlog_ge (by positivity : 0 ≤ ε / 100)
      have heq : (ε / 100) * ((100 / ε) * (1 + 6 * Real.log 2)) = 1 + 6 * Real.log 2 := by
        field_simp [hε0.ne']
      linarith
    have h2 : (n : ℝ) * (1 + 6 * Real.log 2) ≤ (ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (n : ℝ))
      linarith
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : (n : ℝ) + 4 * Real.log 2 + 2 * Real.log 2 ≤ (n : ℝ) * (1 + 6 * Real.log 2) := by
      nlinarith
    exact ⟨hn, le_trans h3 h2, by linarith, by linarith, hlog1⟩
  have h_all : ∀ᶠ n : ℕ in atTop, _ :=
    h_band_ev.and (h_Delta_ev.and h_n_ev)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h_all
  refine ⟨N₀, fun n m X₁ Y₁ hn hm hfund hk2 δ hδ_mem => ?_⟩
  obtain ⟨h_band_n, h_Delta_n, hn8, hn_err, hrpow_half, hrpow_pos, hlog1⟩ := hN₀ n hn
  have hpart2 := thm_4_2_part2_dual_quartic hn8 hm hfund hk2
  obtain ⟨hc₀_12, Bm, Bp, Zm, Zp, hBm_pos, hBp_pos, hZm_pos, hZp_pos,
    hcop_B, hcop_Z, hB_prod, hZ_prod, hu₁_eq, hu₂_eq, _, _, _⟩ := hpart2
  have hn6 : n ≠ 6 := by omega
  obtain ⟨_, _, _, _, _, _, hfac_eq⟩ := k_eq_2_identities (by omega) hn6 hm hfund hk2
  have hX1_pos : 1 ≤ X₁ := hfund.1
  have hq1 := thm_4_2_part1_quartic_law hn8 hm hfund hk2
  have hZ_log_bound : 4 * Real.log (Z_k2 n Y₁ : ℝ) ≤ (2 * ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) := by
    have hA_ge : (B_k2 n X₁ : ℝ) * (Z_k2 n Y₁ : ℝ) ^ 4 ≤ (A_k2 n X₁ : ℝ) := by
      exact_mod_cast (hq1.2.2.2.1 ▸ Nat.le_add_right (B_k2 n X₁ * Z_k2 n Y₁ ^ 4) (Z_k2 n Y₁ ^ 2))
    have hB_pos_r : (0 : ℝ) < (B_k2 n X₁ : ℝ) := by exact_mod_cast B_k2_pos n X₁
    have hZ_pos_r : (0 : ℝ) < (Z_k2 n Y₁ : ℝ) := by exact_mod_cast Z_k2_pos n Y₁
    have hlog_AB : 4 * Real.log (Z_k2 n Y₁ : ℝ) ≤ Real.log (A_k2 n X₁ : ℝ) - Real.log (B_k2 n X₁ : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hA_ge
      rw [Real.log_mul hB_pos_r.ne' (pow_ne_zero 4 hZ_pos_r.ne'), Real.log_pow] at h1
      push_cast at h1
      linarith
    have hv2_le : (padicValNat 2 (Nat.factorial n) : ℝ) ≤ (n : ℝ) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hleg : (2 - 1) * padicValNat 2 (Nat.factorial n) = n - (Nat.digits 2 n).sum :=
        sub_one_mul_padicValNat_factorial n
      exact_mod_cast (by omega : padicValNat 2 (Nat.factorial n) ≤ n)
    have h_diff_AB : Real.log (A_k2 n X₁ : ℝ) - Real.log (B_k2 n X₁ : ℝ) ≤
        |Delta_parity n| + (n : ℝ) := by
      unfold A_k2 B_k2
      have hlog2_le1 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        linarith [Real.exp_one_gt_d9]
      split_ifs
      · rw [Nat.cast_mul, Real.log_mul (by positivity) (B_star_pos n |> Nat.cast_pos.mpr |>.ne'),
            log_A_star_eq, log_B_star_eq, Nat.cast_pow, Real.log_pow]
        have h1 : S_even n - S_odd n = Delta_parity n := by unfold Delta_parity; ring
        have h2 : 0 ≤ ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) * Real.log 2 := by positivity
        norm_num at h2 ⊢
        linarith [le_abs_self (Delta_parity n)]
      · rw [Nat.cast_mul, Real.log_mul (by positivity) (A_star_pos n |> Nat.cast_pos.mpr |>.ne'),
            log_A_star_eq, log_B_star_eq, Nat.cast_pow, Real.log_pow]
        have h1 : S_even n - S_odd n = Delta_parity n := by unfold Delta_parity; ring
        have h2 : ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
          have : padicValNat 2 (Nat.factorial n) - 2 ≤ padicValNat 2 (Nat.factorial n) := Nat.sub_le _ _
          linarith [show ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) ≤ (padicValNat 2 (Nat.factorial n) : ℝ) by exact_mod_cast this]
        have h3 : ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) * Real.log 2 ≤ (n : ℝ) * 1 :=
          mul_le_mul h2 hlog2_le1 (Real.log_nonneg (by norm_num)) (by positivity)
        norm_num at h3 ⊢
        linarith [le_abs_self (Delta_parity n)]
    have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith [abs_le.mp h_Delta_n]
  have hfac_lo : (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) ≤ Real.log ((Nat.factorial n : ℕ) : ℝ) :=
    (n_log_n_sub_n_le_log_factorial n (by omega)).1
  have hlog_X1 : (1 / 4 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) - (n : ℝ) - Real.log 2 ≤ Real.log (X₁ : ℝ) := by
    have h1 : ((Nat.factorial n : ℕ) : ℝ) ≤ 4 * (X₁ : ℝ) ^ 4 := by
      have h_nat : Nat.factorial n ≤ 4 * X₁ ^ 4 := by
        rw [hfac_eq]
        have : (X₁ - 1) * (X₁ + 1) ≤ X₁ ^ 2 := by zify [hX1_pos]; nlinarith
        nlinarith
      exact_mod_cast h_nat
    have h2 := Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) h1
    rw [Real.log_mul (by norm_num) (pow_ne_zero 4 (by positivity)), Real.log_pow,
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h2
    linarith
  have hlog_B_lo : ∀ B_i Z_i u_i : ℕ, 0 < B_i → 0 < Z_i → Z_i ∣ Z_k2 n Y₁ →
      u_i = B_i * Z_i ^ 2 → (X₁ - 1) / 2 ≤ u_i →
      (1 / 4 - 4 * ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) ≤ Real.log (B_i : ℝ) := by
    intro B_i Z_i u_i hB_pos hZ_pos hZ_dvd hu_eq hX_le
    have hZi_le : (Z_i : ℝ) ≤ (Z_k2 n Y₁ : ℝ) := by exact_mod_cast Nat.le_of_dvd (Z_k2_pos n Y₁) hZ_dvd
    have hZ_log : 2 * Real.log (Z_i : ℝ) ≤ (ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) := by
      have h1 := Real.log_le_log (by exact_mod_cast hZ_pos) hZi_le
      linarith
    have hu_ge : (X₁ : ℝ) / 4 ≤ (u_i : ℝ) := by
      have h1 : X₁ ≤ 4 * u_i := by omega
      have h1r : (X₁ : ℝ) ≤ 4 * (u_i : ℝ) := by exact_mod_cast h1
      linarith
    have hlog_u : Real.log (X₁ : ℝ) - 2 * Real.log 2 ≤ Real.log (u_i : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hu_ge
      rw [Real.log_div (by positivity) (by norm_num),
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h1
      linarith
    have hlog_u_eq : Real.log (u_i : ℝ) = Real.log (B_i : ℝ) + 2 * Real.log (Z_i : ℝ) := by
      rw [hu_eq, Nat.cast_mul, Real.log_mul (by exact_mod_cast hB_pos.ne') (pow_ne_zero 2 (by exact_mod_cast hZ_pos.ne')),
          Nat.cast_pow, Real.log_pow]
      ring
    linarith
  have h_core_from_B : ∀ δ u_i B_i B_other Z_i : ℕ, 0 < B_i → 0 < B_other → 0 < Z_i →
      Z_i ∣ Z_k2 n Y₁ →
      B_i * B_other = B_k2 n X₁ / (Nat.gcd (X₁ - 1) (X₁ + 1)) ^ 2 →
      Nat.Coprime B_i B_other →
      u_i = B_i * Z_i ^ 2 → (X₁ - 1) / 2 ≤ u_i →
      δ = sfCore (Nat.gcd (X₁ - 1) (X₁ + 1) * u_i) →
      (∃ p : ℕ, p.Prime ∧ p ∣ δ ∧ (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ)) ∧
      (ε / 5) * (n : ℝ) ^ (1 / 2 - ε) ≤ (δ.primeFactors.card : ℝ) ∧
      (ε / 15) * (n : ℝ) ^ (1 / 2 - ε) * Real.log (n : ℝ) ≤ Real.log (δ : ℝ) := by
    intro δ u_i B_i B_other Z_i hB_pos hBo_pos hZ_pos hZ_dvd hB_mul hB_cop hu_eq hX_le hδ_eq
    have hB_log := hlog_B_lo B_i Z_i u_i hB_pos hZ_pos hZ_dvd hu_eq hX_le
    obtain ⟨hB_odd_primes, hv2_le_Bi⟩ :=
      odd_prime_core_properties hn8 hm hfund hk2 hB_pos hBo_pos hZ_pos hZ_dvd hB_mul hB_cop hc₀_12 hu_eq hδ_eq
    have hB_log_sum : Real.log (B_i : ℝ) =
        ∑ p ∈ B_i.primeFactors, (padicValNat p B_i : ℝ) * Real.log (p : ℝ) :=
      log_nat_eq_sum_primeFactors hB_pos
    have h_odd_sum_ge :
        (1 / 4 - 5 * ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) ≤
        ∑ p ∈ B_i.primeFactors.filter (· ≠ 2),
          (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
      have hsplit : B_i.primeFactors =
          (B_i.primeFactors.filter (· = 2)) ∪ (B_i.primeFactors.filter (· ≠ 2)) := by
        ext p; simp only [Finset.mem_union, Finset.mem_filter]; tauto
      have hdisj : Disjoint (B_i.primeFactors.filter (· = 2)) (B_i.primeFactors.filter (· ≠ 2)) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      rw [hsplit, Finset.sum_union hdisj] at hB_log_sum
      have h2_bound : ∑ p ∈ B_i.primeFactors.filter (· = 2), (padicValNat p B_i : ℝ) * Real.log (p : ℝ) ≤ (n : ℝ) := by
        have hsub : B_i.primeFactors.filter (· = 2) ⊆ {2} := by
          intro p hp; simp only [Finset.mem_singleton]; exact (Finset.mem_filter.mp hp).2
        have h1 : ∑ p ∈ B_i.primeFactors.filter (· = 2), (padicValNat p B_i : ℝ) * Real.log (p : ℝ) ≤
            (padicValNat 2 B_i : ℝ) * Real.log 2 := by
          calc ∑ p ∈ B_i.primeFactors.filter (· = 2), (padicValNat p B_i : ℝ) * Real.log (p : ℝ)
              ≤ ∑ p ∈ ({2} : Finset ℕ), (padicValNat p B_i : ℝ) * Real.log (p : ℝ) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg hsub
                intro p _ _
                exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_cast; omega))
            _ = (padicValNat 2 B_i : ℝ) * Real.log 2 := by simp
        have hv2_n : (padicValNat 2 B_i : ℝ) ≤ (n : ℝ) := by
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          have hleg : (2 - 1) * padicValNat 2 (Nat.factorial n) = n - (Nat.digits 2 n).sum :=
            sub_one_mul_padicValNat_factorial n
          exact_mod_cast le_trans hv2_le_Bi (by omega : padicValNat 2 (Nat.factorial n) ≤ n)
        have hlog2_le1 : Real.log 2 ≤ 1 := by
          rw [Real.log_le_iff_le_exp (by norm_num)]
          linarith [Real.exp_one_gt_d9]
        have h2 : (padicValNat 2 B_i : ℝ) * Real.log 2 ≤ (n : ℝ) * 1 :=
          mul_le_mul hv2_n hlog2_le1 (Real.log_nonneg (by norm_num)) (by positivity)
        linarith
      have h_eq_sum :
          ∑ p ∈ B_i.primeFactors.filter (· ≠ 2), (padicValNat p B_i : ℝ) * Real.log (p : ℝ) =
          ∑ p ∈ B_i.primeFactors.filter (· ≠ 2), (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp_mem := Finset.mem_filter.mp hp
        rw [(hB_odd_primes p hp_mem.1 hp_mem.2).2.1]
      rw [← h_eq_sum]
      linarith
    set S_oddB := B_i.primeFactors.filter (· ≠ 2)
    set L := S_oddB.filter (fun p => (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε))
    set U := S_oddB.filter (fun p => (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ))
    have hLU : S_oddB = L ∪ U := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter, L, U]
      constructor
      · intro hp
        by_cases hle : (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε)
        · left; exact ⟨hp, hle⟩
        · right; exact ⟨hp, lt_of_not_ge hle⟩
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    have hdisj_LU : Disjoint L U := by
      rw [Finset.disjoint_left]; intro p h1 h2
      have h1' := (Finset.mem_filter.mp h1).2
      have h2' := (Finset.mem_filter.mp h2).2
      linarith
    have hL_bound :
        ∑ p ∈ L, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
        (1 / 4 - ε / 2 + ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) := by
      have hsub : L ⊆ (Finset.Icc 2 n).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε) ∧
          padicValNat p (Nat.factorial n) ≡ 1 [MOD 2]) := by
        intro p hp
        have hpL := Finset.mem_filter.mp hp
        have hpS := Finset.mem_filter.mp hpL.1
        have hp_Podd := (hB_odd_primes p hpS.1 hpS.2).1
        have hp_icc := Finset.mem_filter.mp hp_Podd
        have hp_pr := hp_icc.2.1
        have hp_odd := hp_icc.2.2
        have hp_mod : padicValNat p (Nat.factorial n) ≡ 1 [MOD 2] := by
          rw [Nat.ModEq]; omega
        have hp3 : 3 ≤ p := by have := hp_pr.two_le; have := hpS.2; omega
        have hp_gt1 : (n : ℝ) ^ (0 : ℝ) < (p : ℝ) := by
          rw [Real.rpow_zero]; exact_mod_cast (by omega : 1 < p)
        exact Finset.mem_filter.mpr ⟨hp_icc.1, hp_pr, hp_gt1, hpL.2, hp_mod⟩
      calc ∑ p ∈ L, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
          ≤ ∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
              p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - ε) ∧
              padicValNat p (Nat.factorial n) ≡ 1 [MOD 2]),
              (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub
            intro p hp _
            have hp_pr := (Finset.mem_filter.mp hp).2.1
            exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le))
        _ ≤ (1 / 4 - ε / 2 + ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) := h_band_n
    have hU_sum_ge :
        (44 * ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) ≤
        ∑ p ∈ U, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
      rw [hLU, Finset.sum_union hdisj_LU] at h_odd_sum_ge
      linarith
    have hn_log_pos : 0 < (n : ℝ) * Real.log (n : ℝ) := by
      have : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
      nlinarith
    have hU_nonempty : U.Nonempty := by
      by_contra h_empty
      rw [Finset.not_nonempty_iff_eq_empty] at h_empty
      rw [h_empty, Finset.sum_empty] at hU_sum_ge
      nlinarith
    have hδ_ne : δ ≠ 0 := by
      rw [hδ_eq]
      intro h0
      have hc₀_pos : 0 < Nat.gcd (X₁ - 1) (X₁ + 1) := by rcases hc₀_12 with h | h <;> omega
      have hu_pos : 0 < u_i := by rw [hu_eq]; exact mul_pos hB_pos (pow_pos hZ_pos 2)
      have hcu_pos : 0 < Nat.gcd (X₁ - 1) (X₁ + 1) * u_i := mul_pos hc₀_pos hu_pos
      have := eq_sfCore_mul_sqPart_sq hcu_pos
      rw [h0, zero_mul] at this
      omega
    have hU_sub_δ : U ⊆ δ.primeFactors := by
      intro p hp
      have hpS := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
      have hp_pr := Nat.prime_of_mem_primeFactors hpS.1
      have hp_dvd := (hB_odd_primes p hpS.1 hpS.2).2.2
      exact Nat.mem_primeFactors.mpr ⟨hp_pr, hp_dvd, hδ_ne⟩
    have h_exists_p : ∃ p : ℕ, p.Prime ∧ p ∣ δ ∧ (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ) := by
      obtain ⟨p, hpU⟩ := hU_nonempty
      have hpδ := hU_sub_δ hpU
      exact ⟨p, Nat.prime_of_mem_primeFactors hpδ, Nat.dvd_of_mem_primeFactors hpδ,
        (Finset.mem_filter.mp hpU).2⟩
    have hU_term_le : ∀ p ∈ U,
        (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
        (2 * (n : ℝ) / (n : ℝ) ^ (1 / 2 - ε)) * Real.log (n : ℝ) := by
      intro p hpU
      have hpS := Finset.mem_filter.mp (Finset.mem_filter.mp hpU).1
      have hp_Podd := (hB_odd_primes p hpS.1 hpS.2).1
      have hp_icc := Finset.mem_filter.mp hp_Podd
      have hp_pr := hp_icc.2.1
      have hp_le_n : p ≤ n := (Finset.mem_Icc.mp hp_icc.1).2
      have hp_gt : (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ) := (Finset.mem_filter.mp hpU).2
      have hp_sub_ge : (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 - ε) ≤ (p : ℝ) - 1 := by linarith
      haveI : Fact p.Prime := ⟨hp_pr⟩
      have hleg : (p - 1) * padicValNat p (Nat.factorial n) = n - (Nat.digits p n).sum :=
        sub_one_mul_padicValNat_factorial n
      have hv_nat : (p - 1) * padicValNat p (Nat.factorial n) ≤ n := by omega
      have hv_real : ((p : ℝ) - 1) * (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) := by
        have h1 : 1 ≤ p := hp_pr.one_lt.le
        have h1' : ((p - 1 : ℕ) : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hv_nat
        rwa [Nat.cast_sub h1] at h1'
      have hv_bound : (padicValNat p (Nat.factorial n) : ℝ) ≤ 2 * (n : ℝ) / (n : ℝ) ^ (1 / 2 - ε) := by
        have hpos1 : 0 < (p : ℝ) - 1 := by linarith
        have h1 : (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) :=
          (le_div_iff₀ hpos1).mpr (by linarith)
        have h2 : (n : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) / ((1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 - ε)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hp_sub_ge
        have h3 : (n : ℝ) / ((1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 - ε)) = 2 * (n : ℝ) / (n : ℝ) ^ (1 / 2 - ε) := by
          field_simp
        linarith
      have hlog_p_le : Real.log (p : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast hp_pr.pos) (by exact_mod_cast hp_le_n)
      have hlog_p_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)
      exact mul_le_mul hv_bound hlog_p_le hlog_p_nn (by positivity)
    have hU_sum_le :
        ∑ p ∈ U, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
        (U.card : ℝ) * ((2 * (n : ℝ) / (n : ℝ) ^ (1 / 2 - ε)) * Real.log (n : ℝ)) := by
      calc ∑ p ∈ U, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
          ≤ ∑ _ ∈ U, (2 * (n : ℝ) / (n : ℝ) ^ (1 / 2 - ε)) * Real.log (n : ℝ) :=
            Finset.sum_le_sum (fun p hp => hU_term_le p hp)
        _ = (U.card : ℝ) * ((2 * (n : ℝ) / (n : ℝ) ^ (1 / 2 - ε)) * Real.log (n : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hU_card_ge : (22 * ε / 100) * (n : ℝ) ^ (1 / 2 - ε) ≤ (U.card : ℝ) := by
      have h1 : (44 * ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) ≤
          (U.card : ℝ) * ((2 * (n : ℝ) / (n : ℝ) ^ (1 / 2 - ε)) * Real.log (n : ℝ)) :=
        le_trans hU_sum_ge hU_sum_le
      have h_eq : (22 * ε / 100) * (n : ℝ) ^ (1 / 2 - ε) * ((2 * (n : ℝ) / (n : ℝ) ^ (1 / 2 - ε)) * Real.log (n : ℝ)) =
          (44 * ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) := by
        field_simp [hrpow_pos.ne']
        ring
      have h_fac_pos : 0 < (2 * (n : ℝ) / (n : ℝ) ^ (1 / 2 - ε)) * Real.log (n : ℝ) := by
        have : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
        positivity
      nlinarith
    have hδ_card_ge : (ε / 5) * (n : ℝ) ^ (1 / 2 - ε) ≤ (δ.primeFactors.card : ℝ) := by
      have hcard_le : (U.card : ℝ) ≤ (δ.primeFactors.card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hU_sub_δ)
      have h20 : (ε / 5) * (n : ℝ) ^ (1 / 2 - ε) ≤ (22 * ε / 100) * (n : ℝ) ^ (1 / 2 - ε) := by
        nlinarith
      linarith
    have hδ_log_ge : (ε / 15) * (n : ℝ) ^ (1 / 2 - ε) * Real.log (n : ℝ) ≤ Real.log (δ : ℝ) := by
      have hδ_pos : 0 < δ := Nat.pos_of_ne_zero hδ_ne
      have h_prod_dvd : ∏ p ∈ U, p ∣ δ := by
        apply Finset.prod_primes_dvd
        · intro p hp
          have hpδ := hU_sub_δ hp
          exact Nat.prime_of_mem_primeFactors hpδ
        · intro p hp
          exact Nat.dvd_of_mem_primeFactors (hU_sub_δ hp)
      have h_prod_le : (∏ p ∈ U, (p : ℝ)) ≤ (δ : ℝ) := by
        have h1 : ∏ p ∈ U, p ≤ δ := Nat.le_of_dvd hδ_pos h_prod_dvd
        exact_mod_cast h1
      have h_log_prod : ∑ p ∈ U, Real.log (p : ℝ) ≤ Real.log (δ : ℝ) := by
        have hprod_pos : 0 < ∏ p ∈ U, (p : ℝ) :=
          Finset.prod_pos (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors (hU_sub_δ hp)).pos)
        calc ∑ p ∈ U, Real.log (p : ℝ) = Real.log (∏ p ∈ U, (p : ℝ)) := by
              rw [Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors (hU_sub_δ hp)).ne_zero)]
          _ ≤ Real.log (δ : ℝ) := Real.log_le_log hprod_pos h_prod_le
      have h_each_log : ∀ p ∈ U, (1 / 3 : ℝ) * Real.log (n : ℝ) ≤ Real.log (p : ℝ) := by
        intro p hp
        have hp_gt : (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ) := (Finset.mem_filter.mp hp).2
        have h1 : (1 / 2 - ε) * Real.log (n : ℝ) ≤ Real.log (p : ℝ) := by
          rw [← Real.log_rpow (by exact_mod_cast (by omega : 0 < n))]
          exact Real.log_le_log hrpow_pos hp_gt.le
        have h2 : (1 / 3 : ℝ) * Real.log (n : ℝ) ≤ (1 / 2 - ε) * Real.log (n : ℝ) := by
          nlinarith
        linarith
      have h_sum_ge : (U.card : ℝ) * ((1 / 3 : ℝ) * Real.log (n : ℝ)) ≤ ∑ p ∈ U, Real.log (p : ℝ) := by
        calc (U.card : ℝ) * ((1 / 3 : ℝ) * Real.log (n : ℝ))
            = ∑ _ ∈ U, (1 / 3 : ℝ) * Real.log (n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ p ∈ U, Real.log (p : ℝ) := Finset.sum_le_sum h_each_log
      have h_mul_ge : (22 * ε / 100) * (n : ℝ) ^ (1 / 2 - ε) * ((1 / 3 : ℝ) * Real.log (n : ℝ)) ≤
          (U.card : ℝ) * ((1 / 3 : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hU_card_ge (by positivity)
      have h22 : (ε / 15) * (n : ℝ) ^ (1 / 2 - ε) * Real.log (n : ℝ) ≤
          (22 * ε / 100) * (n : ℝ) ^ (1 / 2 - ε) * ((1 / 3 : ℝ) * Real.log (n : ℝ)) := by
        have hpos : 0 < (n : ℝ) ^ (1 / 2 - ε) * Real.log (n : ℝ) := by positivity
        linarith
      linarith
    exact ⟨h_exists_p, hδ_card_ge, hδ_log_ge⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hδ_mem
  set c₀ := Nat.gcd (X₁ - 1) (X₁ + 1)
  have hc₀_le2 : c₀ ≤ 2 := by rcases hc₀_12 with h | h <;> omega
  rcases hδ_mem with rfl | rfl
  · exact h_core_from_B (sfCore (X₁ - 1)) ((X₁ - 1) / c₀) Bm Bp Zm hBm_pos hBp_pos hZm_pos
      ⟨Zp, hZ_prod.symm⟩ hB_prod hcop_B hu₁_eq.symm
      (Nat.div_le_div_left hc₀_le2 (by omega))
      (by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)])
  · exact h_core_from_B (sfCore (X₁ + 1)) ((X₁ + 1) / c₀) Bp Bm Zp hBp_pos hBm_pos hZp_pos
      ⟨Zm, by rw [← hZ_prod, mul_comm]⟩ (by rw [mul_comm, hB_prod]) hcop_B.symm hu₂_eq.symm
      (by have := Nat.div_le_div_left hc₀_le2 (by omega : 0 < c₀); have : (X₁ - 1) / 2 ≤ (X₁ + 1) / 2 := Nat.div_le_div_right (by omega); omega)
      (by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)])

private lemma log_div_sub_one_antitone :
    AntitoneOn (fun x : ℝ => Real.log x / (x - 1)) (Set.Ici 3) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 3)
  · apply ContinuousOn.div (Real.continuousOn_log.mono (fun x hx => ne_of_gt (by linarith [Set.mem_Ici.mp hx])))
      (continuous_id.sub continuous_const).continuousOn
    intro x hx; simp only [Pi.sub_apply, id_eq]; linarith [Set.mem_Ici.mp hx]
  · apply DifferentiableOn.div (Real.differentiableOn_log.mono (fun x hx => ne_of_gt (by linarith [Set.mem_Ici.mp (interior_subset hx)])))
      (differentiable_id.sub (differentiable_const 1)).differentiableOn
    intro x hx; simp only [Pi.sub_apply, id_eq]; linarith [Set.mem_Ici.mp (interior_subset hx)]
  · intro x hx
    have hx3 : 3 < x := by
      have := interior_Ici (a := (3 : ℝ)) ▸ hx
      exact this
    have hx0 : x ≠ 0 := by linarith
    have hx1 : x - 1 ≠ 0 := by linarith
    have hlog_gt1 : 1 < Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hderiv : deriv (fun y : ℝ => Real.log y / (y - 1)) x =
        ((1 / x) * (x - 1) - Real.log x * 1) / (x - 1) ^ 2 := by
      have h1 : HasDerivAt Real.log (1 / x) x := by simpa [one_div] using Real.hasDerivAt_log hx0
      have h2 : HasDerivAt (fun y : ℝ => y - 1) 1 x := (hasDerivAt_id x).sub_const 1
      exact (h1.div h2 hx1).deriv
    rw [hderiv]
    have hnum : (1 / x) * (x - 1) - Real.log x * 1 ≤ 0 := by
      have : (1 / x) * (x - 1) = 1 - 1 / x := by field_simp
      have : 0 < 1 / x := by positivity
      linarith
    exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg _)

private lemma nth_prime_one_eq_three : Nat.nth Nat.Prime 1 = 3 := by
  have h3_eq : Nat.nth Nat.Prime (Nat.count Nat.Prime 3) = 3 := Nat.nth_count Nat.prime_three
  have hcnt_pos : 0 < Nat.count Nat.Prime 3 := by
    by_contra h0
    have hc0 : Nat.count Nat.Prime 3 = 0 := by omega
    rw [hc0, Nat.nth_prime_zero_eq_two] at h3_eq
    omega
  have hcnt_le1 : Nat.count Nat.Prime 3 ≤ 1 := by
    by_contra hgt
    have h1 : 1 < Nat.count Nat.Prime 3 := by omega
    have hlt := Nat.nth_strictMono Nat.infinite_setOf_prime h1
    rw [h3_eq] at hlt
    have hgt2 : 2 < Nat.nth Nat.Prime 1 := by
      simpa [Nat.nth_prime_zero_eq_two] using Nat.nth_strictMono Nat.infinite_setOf_prime (by norm_num : 0 < 1)
    omega
  have hcnt1 : Nat.count Nat.Prime 3 = 1 := by omega
  rwa [hcnt1] at h3_eq

private lemma sum_log_div_sub_one_le_nth_primes (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p) :
    ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤
    ∑ p ∈ (Finset.Icc 3 (Nat.nth Nat.Prime S.card)).filter Nat.Prime,
      Real.log (p : ℝ) / ((p : ℝ) - 1) := by
  set t := S.card
  let e := S.orderEmbOfFin rfl
  have he_mem : ∀ i : Fin t, e i ∈ S := fun i => Finset.orderEmbOfFin_mem S rfl i
  have he_ge : ∀ i : Fin t, Nat.nth Nat.Prime (i.1 + 1) ≤ e i := by
    intro ⟨i, hi⟩
    induction i with
    | zero =>
      rw [zero_add, nth_prime_one_eq_three]
      exact (hS _ (he_mem _)).2
    | succ k ih =>
      have hk : k < t := by omega
      have h_ih := ih hk
      have hlt_e : e ⟨k, hk⟩ < e ⟨k + 1, hi⟩ := e.strictMono (by simp [Fin.lt_def])
      have hlt_nth : Nat.nth Nat.Prime (k + 1) < e ⟨k + 1, hi⟩ := lt_of_le_of_lt h_ih hlt_e
      have h_pr : (e ⟨k + 1, hi⟩).Prime := (hS _ (he_mem _)).1
      set m := Nat.count Nat.Prime (e ⟨k + 1, hi⟩)
      have hm_eq : Nat.nth Nat.Prime m = e ⟨k + 1, hi⟩ := Nat.nth_count h_pr
      rw [← hm_eq] at hlt_nth
      have hkm : k + 1 < m := (Nat.nth_strictMono Nat.infinite_setOf_prime).lt_iff_lt.mp hlt_nth
      have hle_nth : Nat.nth Nat.Prime (k + 2) ≤ Nat.nth Nat.Prime m :=
        (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone (by omega)
      rwa [hm_eq] at hle_nth
  have hsum_e : ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) =
      ∑ i : Fin t, Real.log ((e i : ℕ) : ℝ) / (((e i : ℕ) : ℝ) - 1) := by
    rw [← Finset.sum_coe_sort S]
    exact (Equiv.sum_comp (S.orderIsoOfFin rfl).toEquiv
      (fun x : ↥S => Real.log ((x : ℕ) : ℝ) / (((x : ℕ) : ℝ) - 1))).symm
  have hsum_le_fin :
      ∑ i : Fin t, Real.log ((e i : ℕ) : ℝ) / (((e i : ℕ) : ℝ) - 1) ≤
      ∑ i : Fin t, Real.log ((Nat.nth Nat.Prime (i.1 + 1) : ℕ) : ℝ) /
        (((Nat.nth Nat.Prime (i.1 + 1) : ℕ) : ℝ) - 1) := by
    apply Finset.sum_le_sum
    intro i _
    have h3_le : (3 : ℝ) ≤ (Nat.nth Nat.Prime (i.1 + 1) : ℝ) := by
      have h3_nat : 3 ≤ Nat.nth Nat.Prime (i.1 + 1) := by
        rw [← nth_prime_one_eq_three]
        exact (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone (by omega : 1 ≤ i.1 + 1)
      exact_mod_cast h3_nat
    have h_le : (Nat.nth Nat.Prime (i.1 + 1) : ℝ) ≤ (e i : ℝ) := by exact_mod_cast he_ge i
    exact log_div_sub_one_antitone h3_le (le_trans h3_le h_le) h_le
  have hsum_img :
      ∑ i : Fin t, Real.log ((Nat.nth Nat.Prime (i.1 + 1) : ℕ) : ℝ) /
        (((Nat.nth Nat.Prime (i.1 + 1) : ℕ) : ℝ) - 1) =
      ∑ p ∈ (Finset.univ : Finset (Fin t)).image (fun i => Nat.nth Nat.Prime (i.1 + 1)),
        Real.log (p : ℝ) / ((p : ℝ) - 1) := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    have h1 := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hab
    ext; omega
  have hsub_icc :
      (Finset.univ : Finset (Fin t)).image (fun i => Nat.nth Nat.Prime (i.1 + 1)) ⊆
      (Finset.Icc 3 (Nat.nth Nat.Prime t)).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨i, _, rfl⟩ := hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _⟩
    · rw [← nth_prime_one_eq_three]
      exact (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone (by omega)
    · exact (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone (by omega : i.1 + 1 ≤ t)
  calc ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)
      ≤ ∑ p ∈ (Finset.univ : Finset (Fin t)).image (fun i => Nat.nth Nat.Prime (i.1 + 1)),
          Real.log (p : ℝ) / ((p : ℝ) - 1) := by linarith [hsum_e, hsum_le_fin, hsum_img]
    _ ≤ ∑ p ∈ (Finset.Icc 3 (Nat.nth Nat.Prime t)).filter Nat.Prime,
          Real.log (p : ℝ) / ((p : ℝ) - 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub_icc
        intro p hp _
        have hp_pr := (Finset.mem_filter.mp hp).2
        have hpos1 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)
        have hpos2 : 0 ≤ (p : ℝ) - 1 := by
          have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_pr.one_lt.le
          linarith
        exact div_nonneg hpos1 hpos2

/-- **Theorem 4.2(iii) (Explicit Mertens `n^{1/4 - ε}` Lower Bound on Midpoint Cores)**:
Using `mertens_first_theorem_odd_primes`, there exists `γ ∈ (0.5772, 0.5773)` such that for
every `ε > 0`, for all sufficiently large `n` with a `k = 2` solution `(n, m)`, both midpoint
cores `δ ∈ {sfCore (X₁ - 1), sfCore (X₁ + 1)}` satisfy:
1. `∑ p ∈ δ.primeFactors.filter (3 ≤ ·), log p / (p - 1) ≥ (1 / 4 - ε) * log n`,
2. `log (Nat.nth Nat.Prime (δ.primeFactors.filter (3 ≤ ·)).card) ≥ (1 / 4 - ε) * log n + γ + log 2 - ε`. -/
theorem thm_4_2_part3_mertens_bound :
    ∃ γ : ℝ, 0.5772 < γ ∧ γ < 0.5773 ∧
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ n m X₁ Y₁ : ℕ, N₀ ≤ n →
      Nat.factorial n + 1 = m ^ 2 →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2 →
      ∀ δ ∈ ({sfCore (X₁ - 1), sfCore (X₁ + 1)} : Finset ℕ),
        (1 / 4 - ε) * Real.log (n : ℝ) ≤
          ∑ p ∈ δ.primeFactors.filter (3 ≤ ·), Real.log (p : ℝ) / ((p : ℝ) - 1) ∧
        (1 / 4 - ε) * Real.log (n : ℝ) + γ + Real.log 2 - ε ≤
          Real.log (Nat.nth Nat.Prime (δ.primeFactors.filter (3 ≤ ·)).card : ℝ) := by
  obtain ⟨γ, hγ1, hγ2, hmertens⟩ := mertens_first_theorem_odd_primes
  refine ⟨γ, hγ1, hγ2, fun ε hε0 => ?_⟩
  set ε₁ := min ε (1 / 12) with hε₁_def
  have hε₁_pos : 0 < ε₁ := lt_min hε0 (by norm_num)
  have hε₁_le : ε₁ ≤ ε := min_le_left _ _
  have hε₁_lt : ε₁ < 1 / 6 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨N_core, hN_core⟩ := thm_4_2_part3_midpoint_core_bounds ε₁ hε₁_pos hε₁_lt
  obtain ⟨N_locks, hN_locks⟩ := thm_4_2_part2_euclidean_locks (ε₁ / 2) (by linarith) (by linarith)
  have hmert_ev : ∀ᶠ x : ℕ in atTop,
      ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤
      Real.log (x : ℝ) - γ - Real.log 2 + ε := by
    have h1 := hmertens.bound hε0
    filter_upwards [h1] with x hx
    simp only [Real.norm_eq_abs, norm_one, mul_one] at hx
    linarith [(abs_le.mp hx).2]
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hmert_ev
  have hrpow_inf : Tendsto (fun n : ℕ => (ε₁ / 5) * (n : ℝ) ^ (1 / 2 - ε₁) - 1) atTop atTop :=
    ((Tendsto.const_mul_atTop (by positivity : 0 < ε₁ / 5)
      ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 / 2 - ε₁)).comp tendsto_natCast_atTop_atTop)).atTop_add
      tendsto_const_nhds)
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_all : ∀ᶠ n : ℕ in atTop,
      max (max N_core N_locks) 8 ≤ n ∧
      (X₀ : ℝ) ≤ (ε₁ / 5) * (n : ℝ) ^ (1 / 2 - ε₁) - 1 ∧
      2 / ε₁ ≤ Real.log (n : ℝ) :=
    (eventually_ge_atTop (max (max N_core N_locks) 8)).and
      ((hrpow_inf.eventually (eventually_ge_atTop (X₀ : ℝ))).and
        (hlog_inf.eventually (eventually_ge_atTop (2 / ε₁))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h_all
  refine ⟨N₀, fun n m X₁ Y₁ hn hm hfund hk2 δ hδ_mem => ?_⟩
  obtain ⟨hmax, hX₀_le, hlog_ge⟩ := hN₀ n hn
  have hn_core : N_core ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hmax
  have hn_locks : N_locks ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hmax
  have hn8 : 8 ≤ n := le_trans (le_max_right _ _) hmax
  have hcore := hN_core n m X₁ Y₁ hn_core hm hfund hk2 δ hδ_mem
  have hlocks := hN_locks n m X₁ Y₁ hn_locks hm hfund hk2
  obtain ⟨Bm, Bp, Zm, Zp, hBm_pos, hBp_pos, hZm_pos, hZp_pos, hcop_B, hcop_Z, hB_prod, hZ_prod,
    hu₁_eq, hu₂_eq, hBm_lo, _, hBp_lo, _, _, _, _, _⟩ := hlocks
  have hpart2 := thm_4_2_part2_dual_quartic hn8 hm hfund hk2
  have hc₀_12 := hpart2.1
  set c₀ := Nat.gcd (X₁ - 1) (X₁ + 1)
  have h_sum_for_B : ∀ B_i B_other Z_i u_i : ℕ, 0 < B_i → 0 < B_other → 0 < Z_i →
      Z_i ∣ Z_k2 n Y₁ → B_i * B_other = B_k2 n X₁ / c₀ ^ 2 → Nat.Coprime B_i B_other →
      u_i = B_i * Z_i ^ 2 → δ = sfCore (c₀ * u_i) →
      (1 / 4 - ε₁ / 2) * ((n : ℝ) * Real.log (n : ℝ)) ≤ Real.log (B_i : ℝ) →
      (1 / 4 - ε₁) * Real.log (n : ℝ) ≤
        ∑ p ∈ δ.primeFactors.filter (3 ≤ ·), Real.log (p : ℝ) / ((p : ℝ) - 1) := by
    intro B_i B_other Z_i u_i hB_pos hBo_pos hZ_pos hZ_dvd hB_mul hB_cop hu_eq hδ_eq hB_lo
    obtain ⟨hB_odd, hv2_le⟩ :=
      odd_prime_core_properties hn8 hm hfund hk2 hB_pos hBo_pos hZ_pos hZ_dvd hB_mul hB_cop hc₀_12 hu_eq hδ_eq
    have hB_log_sum : Real.log (B_i : ℝ) =
        ∑ p ∈ B_i.primeFactors, (padicValNat p B_i : ℝ) * Real.log (p : ℝ) :=
      log_nat_eq_sum_primeFactors hB_pos
    have hsplit : B_i.primeFactors =
        (B_i.primeFactors.filter (· = 2)) ∪ (B_i.primeFactors.filter (· ≠ 2)) := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    have hdisj : Disjoint (B_i.primeFactors.filter (· = 2)) (B_i.primeFactors.filter (· ≠ 2)) := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    rw [hsplit, Finset.sum_union hdisj] at hB_log_sum
    have h2_bound : ∑ p ∈ B_i.primeFactors.filter (· = 2), (padicValNat p B_i : ℝ) * Real.log (p : ℝ) ≤ (n : ℝ) := by
      have hsub : B_i.primeFactors.filter (· = 2) ⊆ {2} := by
        intro p hp; simp only [Finset.mem_singleton]; exact (Finset.mem_filter.mp hp).2
      have h1 : ∑ p ∈ B_i.primeFactors.filter (· = 2), (padicValNat p B_i : ℝ) * Real.log (p : ℝ) ≤
          (padicValNat 2 B_i : ℝ) * Real.log 2 := by
        calc ∑ p ∈ B_i.primeFactors.filter (· = 2), (padicValNat p B_i : ℝ) * Real.log (p : ℝ)
            ≤ ∑ p ∈ ({2} : Finset ℕ), (padicValNat p B_i : ℝ) * Real.log (p : ℝ) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hsub
              intro p _ _
              exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_cast; omega))
          _ = (padicValNat 2 B_i : ℝ) * Real.log 2 := by simp
      have hv2_n : (padicValNat 2 B_i : ℝ) ≤ (n : ℝ) := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hleg : (2 - 1) * padicValNat 2 (Nat.factorial n) = n - (Nat.digits 2 n).sum :=
          sub_one_mul_padicValNat_factorial n
        exact_mod_cast le_trans hv2_le (by omega : padicValNat 2 (Nat.factorial n) ≤ n)
      have hlog2_le1 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        linarith [Real.exp_one_gt_d9]
      have h2 : (padicValNat 2 B_i : ℝ) * Real.log 2 ≤ (n : ℝ) * 1 :=
        mul_le_mul hv2_n hlog2_le1 (Real.log_nonneg (by norm_num)) (by positivity)
      linarith
    have hn_err : (n : ℝ) ≤ (ε₁ / 2) * ((n : ℝ) * Real.log (n : ℝ)) := by
      have h1 : 1 ≤ (ε₁ / 2) * Real.log (n : ℝ) := by
        have := mul_le_mul_of_nonneg_left hlog_ge (by positivity : 0 ≤ ε₁ / 2)
        have heq : (ε₁ / 2) * (2 / ε₁) = 1 := by field_simp [hε₁_pos.ne']
        linarith
      have h2 : (n : ℝ) * 1 ≤ (n : ℝ) * ((ε₁ / 2) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    have h_eq_sum :
        ∑ p ∈ B_i.primeFactors.filter (· ≠ 2), (padicValNat p B_i : ℝ) * Real.log (p : ℝ) =
        ∑ p ∈ B_i.primeFactors.filter (· ≠ 2), (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp_mem := Finset.mem_filter.mp hp
      rw [(hB_odd p hp_mem.1 hp_mem.2).2.1]
    have h_odd_ge : (1 / 4 - ε₁) * ((n : ℝ) * Real.log (n : ℝ)) ≤
        ∑ p ∈ B_i.primeFactors.filter (· ≠ 2),
          (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
      linarith
    have h_term_le : ∀ p ∈ B_i.primeFactors.filter (· ≠ 2),
        (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
        (n : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) - 1)) := by
      intro p hp
      have hp_mem := Finset.mem_filter.mp hp
      have hp_pr := Nat.prime_of_mem_primeFactors hp_mem.1
      have hp3 : 3 ≤ p := by have := hp_pr.two_le; have := hp_mem.2; omega
      haveI : Fact p.Prime := ⟨hp_pr⟩
      have hleg : (p - 1) * padicValNat p (Nat.factorial n) = n - (Nat.digits p n).sum :=
        sub_one_mul_padicValNat_factorial n
      have hv_nat : (p - 1) * padicValNat p (Nat.factorial n) ≤ n := by omega
      have hv_real : ((p : ℝ) - 1) * (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) := by
        have h1 : 1 ≤ p := hp_pr.one_lt.le
        have h1' : ((p - 1 : ℕ) : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hv_nat
        rwa [Nat.cast_sub h1] at h1'
      have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
      have hv_le : (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) :=
        (le_div_iff₀ hp1_pos).mpr (by linarith)
      have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)
      calc (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
          ≤ ((n : ℝ) / ((p : ℝ) - 1)) * Real.log (p : ℝ) := mul_le_mul_of_nonneg_right hv_le hlog_nn
        _ = (n : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) - 1)) := by ring
    have h_sub_δ : B_i.primeFactors.filter (· ≠ 2) ⊆ δ.primeFactors.filter (3 ≤ ·) := by
      intro p hp
      have hp_mem := Finset.mem_filter.mp hp
      have hp_pr := Nat.prime_of_mem_primeFactors hp_mem.1
      have hp3 : 3 ≤ p := by have := hp_pr.two_le; have := hp_mem.2; omega
      have hp_dvd := (hB_odd p hp_mem.1 hp_mem.2).2.2
      have hδ_ne : δ ≠ 0 := by
        rw [hδ_eq]
        intro h0
        have hc₀_pos : 0 < c₀ := by rcases hc₀_12 with h | h <;> omega
        have hu_pos : 0 < u_i := by rw [hu_eq]; exact mul_pos hB_pos (pow_pos hZ_pos 2)
        have hcu_pos : 0 < c₀ * u_i := mul_pos hc₀_pos hu_pos
        have := eq_sfCore_mul_sqPart_sq hcu_pos
        rw [h0, zero_mul] at this
        omega
      exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp_pr, hp_dvd, hδ_ne⟩, hp3⟩
    have h_sum_le_δ :
        ∑ p ∈ B_i.primeFactors.filter (· ≠ 2),
          (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
        (n : ℝ) * ∑ p ∈ δ.primeFactors.filter (3 ≤ ·), Real.log (p : ℝ) / ((p : ℝ) - 1) := by
      calc ∑ p ∈ B_i.primeFactors.filter (· ≠ 2),
              (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
          ≤ ∑ p ∈ B_i.primeFactors.filter (· ≠ 2), (n : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) - 1)) :=
            Finset.sum_le_sum h_term_le
        _ = (n : ℝ) * ∑ p ∈ B_i.primeFactors.filter (· ≠ 2), Real.log (p : ℝ) / ((p : ℝ) - 1) := by
            rw [← Finset.mul_sum]
        _ ≤ (n : ℝ) * ∑ p ∈ δ.primeFactors.filter (3 ≤ ·), Real.log (p : ℝ) / ((p : ℝ) - 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Finset.sum_le_sum_of_subset_of_nonneg h_sub_δ
            intro p hp _
            have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
            have hpos2 : 0 ≤ (p : ℝ) - 1 := by
              have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_pr.one_lt.le
              linarith
            exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)) hpos2
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h_div := le_trans h_odd_ge h_sum_le_δ
    have h_final : (1 / 4 - ε₁) * Real.log (n : ℝ) ≤
        ∑ p ∈ δ.primeFactors.filter (3 ≤ ·), Real.log (p : ℝ) / ((p : ℝ) - 1) := by
      nlinarith
    exact h_final
  have hsum_ge_ε1 : (1 / 4 - ε₁) * Real.log (n : ℝ) ≤
      ∑ p ∈ δ.primeFactors.filter (3 ≤ ·), Real.log (p : ℝ) / ((p : ℝ) - 1) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hδ_mem
    rcases hδ_mem with rfl | rfl
    · exact h_sum_for_B Bm Bp Zm ((X₁ - 1) / c₀) hBm_pos hBp_pos hZm_pos
        ⟨Zp, hZ_prod.symm⟩ hB_prod hcop_B hu₁_eq.symm
        (by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]) hBm_lo
    · exact h_sum_for_B Bp Bm Zp ((X₁ + 1) / c₀) hBp_pos hBm_pos hZp_pos
        ⟨Zm, by rw [← hZ_prod, mul_comm]⟩ (by rw [mul_comm, hB_prod]) hcop_B.symm hu₂_eq.symm
        (by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]) hBp_lo
  have hsum_ge : (1 / 4 - ε) * Real.log (n : ℝ) ≤
      ∑ p ∈ δ.primeFactors.filter (3 ≤ ·), Real.log (p : ℝ) / ((p : ℝ) - 1) := by
    have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    nlinarith
  set S := δ.primeFactors.filter (3 ≤ ·)
  have hS_props : ∀ p ∈ S, p.Prime ∧ 3 ≤ p := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
  have hmert_upper := sum_log_div_sub_one_le_nth_primes S hS_props
  have hS_card_ge : (X₀ : ℝ) ≤ (S.card : ℝ) := by
    have hcard_all : (δ.primeFactors.card : ℝ) ≤ (S.card : ℝ) + 1 := by
      have hsplit : δ.primeFactors ⊆ insert 2 S := by
        intro p hp
        have hp_pr := Nat.prime_of_mem_primeFactors hp
        by_cases hp2 : p = 2
        · subst hp2; exact Finset.mem_insert_self 2 _
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hp, by have := hp_pr.two_le; omega⟩)
      have hle := Finset.card_le_card hsplit
      have hle2 : (insert 2 S).card ≤ S.card + 1 := Finset.card_insert_le 2 S
      exact_mod_cast le_trans hle hle2
    linarith [hcore.2.1]
  have hnth_ge_card : S.card ≤ Nat.nth Nat.Prime S.card :=
    Nat.nth_strictMono Nat.infinite_setOf_prime |>.id_le S.card
  have hX₀_le_nth : X₀ ≤ Nat.nth Nat.Prime S.card := by
    have : X₀ ≤ S.card := by exact_mod_cast hS_card_ge
    exact le_trans this hnth_ge_card
  have hmert_x := hX₀ (Nat.nth Nat.Prime S.card) hX₀_le_nth
  have hlog_nth_ge : (1 / 4 - ε) * Real.log (n : ℝ) + γ + Real.log 2 - ε ≤
      Real.log (Nat.nth Nat.Prime S.card : ℝ) := by
    linarith
  exact ⟨hsum_ge, hlog_nth_ge⟩

end GrasGreenbergBrocard
