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
    omega
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
        · intro p _ hpq
          have hp_pr := (Finset.mem_filter.mp (by assumption)).2
          rw [hp_pr.factorization, Finsupp.single_apply, if_neg (Ne.symm hpq), mul_zero]
        · intro habs; exact absurd hq habs
      · rw [Finset.sum_eq_zero]
        · rw [Nat.factorization_eq_zero_iff]
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
    rw [← h_all, hsplit, Finset.prod_insert h2_not, hsplit_oe, Finset.prod_union hdisj_oe]
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
      exact hp.not_dvd_one hp1
    have hfac_qY : Nat.factorial n = 4 * X₁ ^ 2 * (q_n n * Y₁ ^ 2) := by
      have hdiff : (X₁ - 1) * (X₁ + 1) = q_n n * Y₁ ^ 2 := by
        zify [hX1_pos]; have : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
        linarith
      rw [hfac_eq]; calc 4 * (X₁ - 1) * X₁ ^ 2 * (X₁ + 1) = 4 * X₁ ^ 2 * ((X₁ - 1) * (X₁ + 1)) := by ring
        _ = 4 * X₁ ^ 2 * (q_n n * Y₁ ^ 2) := by rw [hdiff]
    have hv2_ge : 2 ≤ padicValNat 2 (Nat.factorial n) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)]
      exact dvd_trans (by decide : 2 ^ 2 ∣ 24) (Nat.factorial_dvd_factorial (by omega : 4 ≤ n))
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
            show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.pow 2 (by norm_num),
            padicValNat.pow 2 (by omega)]
          simp
        have hZ_odd : ¬ 2 ∣ Z_k2 n Y₁ := by
          unfold Z_k2
          rw [Nat.Prime.dvd_finset_prod_iff Nat.prime_two]
          rintro ⟨q, hq, hdvd⟩
          have hq3 : 3 ≤ q := (Finset.mem_filter.mp hq).2.1
          have hq_pr : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
          have := Nat.prime_dvd_prime_iff_eq Nat.prime_two hq_pr |>.mp (Nat.prime_two.dvd_of_dvd_pow hdvd)
          omega
        have hA_star_odd : ¬ 2 ∣ A_star n := by
          unfold A_star
          rw [Nat.Prime.dvd_finset_prod_iff Nat.prime_two]
          rintro ⟨q, hq, hdvd⟩
          have hq3 : 3 ≤ q := (Finset.mem_filter.mp hq).2
          have hq_pr : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
          have := Nat.prime_dvd_prime_iff_eq Nat.prime_two hq_pr |>.mp (Nat.prime_two.dvd_of_dvd_pow hdvd)
          omega
        rw [Nat.factorization_mul (pow_ne_zero 2 (by omega)) (pow_ne_zero 2 (Z_k2_pos n Y₁).ne'),
            Nat.factorization_pow, Nat.factorization_pow]
        simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Nat.factorization_def _ Nat.prime_two, padicValNat.eq_zero_of_not_dvd hZ_odd, mul_zero, add_zero]
        unfold A_k2
        split_ifs with hX_odd
        · have h2ndX : ¬ 2 ∣ X₁ := by omega
          rw [Nat.factorization_def _ Nat.prime_two, padicValNat.eq_zero_of_not_dvd hA_star_odd,
              Nat.factorization_def _ Nat.prime_two, padicValNat.eq_zero_of_not_dvd h2ndX, mul_zero]
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
              smul_eq_mul, Nat.factorization_def _ Nat.prime_two, padicValNat.eq_zero_of_not_dvd hA_star_odd,
              Nat.prime_two.factorization_self, mul_one, add_zero,
              Nat.factorization_def _ Nat.prime_two, h_val_n, padicValNat.eq_zero_of_not_dvd h2nd_qY, add_zero]
          omega
      · have hp3 : 3 ≤ p := by have := hp.two_le; omega
        have hA_val : (A_k2 n X₁).factorization p = (A_star n).factorization p := by
          unfold A_k2
          split_ifs
          · rfl
          · rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (A_star_pos n).ne',
                Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
                smul_eq_mul, Nat.factorization_def _ hp, padicValNat.eq_zero_of_not_dvd (fun h => by
                  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h; omega), mul_zero, zero_add]
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
              rw [hq_pr.factorization, Finsupp.single_apply, if_neg (Ne.symm hqp), mul_zero]
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
              rw [hq_pr.factorization, Finsupp.single_apply, if_neg (Ne.symm hqp), mul_zero]
            · intro habs; exact absurd hmem habs
          · rw [Finset.sum_eq_zero]
            intro q hq
            have hqp : q ≠ p := fun h => hmem (h ▸ hq)
            have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
            rw [hq_pr.factorization, Finsupp.single_apply, if_neg hqp, mul_zero]
        rw [hA_val, hA_star_val,
            Nat.factorization_mul (pow_ne_zero 2 (by omega)) (pow_ne_zero 2 (Z_k2_pos n Y₁).ne'),
            Nat.factorization_pow, Nat.factorization_pow,
            Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            hZ_val, Nat.factorization_def X₁ hp]
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
        rw [padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)]
        exact dvd_trans (by decide : 2 ^ 2 ∣ 24) (Nat.factorial_dvd_factorial (by omega : 4 ≤ n))
      have h4_mul : 4 * (A_k2 n X₁ * B_k2 n X₁) = Nat.factorial n := by
        rw [h1, ← A_star_mul_B_star n]
        have hpow : 4 * 2 ^ (padicValNat 2 (Nat.factorial n) - 2) = 2 ^ padicValNat 2 (Nat.factorial n) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.add_sub_of_le h2_le]
        calc 4 * (A_star n * B_star n * 2 ^ (padicValNat 2 (Nat.factorial n) - 2))
            = A_star n * B_star n * (4 * 2 ^ (padicValNat 2 (Nat.factorial n) - 2)) := by ring
          _ = A_star n * B_star n * 2 ^ padicValNat 2 (Nat.factorial n) := by rw [hpow]
      have h4_eq : 4 * (A_k2 n X₁ * B_k2 n X₁) = 4 * (X₁ ^ 2 * (q_n n * Y₁ ^ 2)) := by
        rw [h4_mul, hfac_qY]
      omega
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
        show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.pow 2 (by norm_num),
        padicValNat.pow 2 (by omega), padicValNat.eq_zero_of_not_dvd h2nd_qY]
      simp
    have hv2_ge7 : 7 ≤ padicValNat 2 (Nat.factorial n) := by
      rw [padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)]
      exact dvd_trans (by decide : 2 ^ 7 ∣ Nat.factorial 8) (Nat.factorial_dvd_factorial hn)
    have hv2_even : 2 ∣ padicValNat 2 (Nat.factorial n) := ⟨1 + padicValNat 2 X₁, by omega⟩
    have hvX_ge3 : 3 ≤ padicValNat 2 X₁ := by omega
    have h8_dvd_X : 8 ∣ X₁ := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← padicValNat_dvd_iff_le (by omega)]
      exact hvX_ge3
    have hY_odd : Y₁ % 2 = 1 := by
      by_contra h0
      have h2Y : 2 ∣ Y₁ := by omega
      exact h2nd_qY (dvd_mul_of_dvd_right (dvd_pow h2Y (by norm_num)) _)
    have hpell := hfund.2.2.1
    have hX8 : X₁ ^ 2 % 8 = 0 := by
      obtain ⟨k, rfl⟩ := h8_dvd_X
      omega
    have hY8 : Y₁ ^ 2 % 8 = 1 := by
      have : Y₁ % 8 = 1 ∨ Y₁ % 8 = 3 ∨ Y₁ % 8 = 5 ∨ Y₁ % 8 = 7 := by omega
      rcases this with h | h | h | h <;> omega
    have hq8 : q_n n % 8 = 7 := by
      have hmod : (X₁ ^ 2) % 8 = (q_n n * Y₁ ^ 2 + 1) % 8 := congrArg (· % 8) hpell
      rw [Nat.add_mod, Nat.mul_mod, hX8, hY8] at hmod
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

private lemma Z_k2_log_upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n m X₁ Y₁ : ℕ, N₀ ≤ n →
      Nat.factorial n + 1 = m ^ 2 →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2 →
      4 * Real.log (Z_k2 n Y₁ : ℝ) ≤ ε * ((n : ℝ) * Real.log (n : ℝ)) := by
  have h_Delta := Delta_parity_isLittleO_mul_log
  have h_Delta_ev : ∀ᶠ n : ℕ in atTop,
      |Delta_parity n| ≤ (ε / 2) * ((n : ℝ) * Real.log (n : ℝ)) := by
    have h1 := h_Delta.bound (by positivity : (0 : ℝ) < ε / 2)
    filter_upwards [h1, eventually_ge_atTop 2] with n hn hn2
    have hn_log_nn : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
    rw [Real.norm_of_nonneg hn_log_nn] at hn
    simpa [Real.norm_eq_abs] using hn
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 8, h_Delta_ev,
    hlog_inf.eventually (eventually_ge_atTop (2 / ε))] with n hn8 hDelta_n hlog_n
  -- wait: filter_upwards doesn't produce an `∃ N₀`, let's use `eventually_atTop.mp`
  sorry

-- Clean helper without `sorry`:
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
    exact_mod_cast (by linarith : B_k2 n X₁ * (Z_k2 n Y₁) ^ 4 ≤ A_k2 n X₁)
  have hB_pos_r : (0 : ℝ) < (B_k2 n X₁ : ℝ) := by exact_mod_cast B_k2_pos n X₁
  have hZ_pos_r : (0 : ℝ) < (Z_k2 n Y₁ : ℝ) := by exact_mod_cast Z_k2_pos n Y₁
  have hlog_AB : 4 * Real.log (Z_k2 n Y₁ : ℝ) ≤ Real.log (A_k2 n X₁ : ℝ) - Real.log (B_k2 n X₁ : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hA_ge
    rw [Real.log_mul hB_pos_r.ne' (pow_ne_zero 4 hZ_pos_r.ne'), Real.log_pow] at h1
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
      linarith [le_abs_self (Delta_parity n)]
    · rw [Nat.cast_mul, Real.log_mul (by positivity) (A_star_pos n |> Nat.cast_pos.mpr |>.ne'),
          log_A_star_eq, log_B_star_eq, Nat.cast_pow, Real.log_pow]
      have h1 : S_even n - S_odd n = Delta_parity n := by unfold Delta_parity; ring
      have h2 : ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : padicValNat 2 (Nat.factorial n) - 2 ≤ padicValNat 2 (Nat.factorial n) := Nat.sub_le _ _
        linarith [show ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) ≤ (padicValNat 2 (Nat.factorial n) : ℝ) by exact_mod_cast this]
      have h3 : ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) * Real.log 2 ≤ (n : ℝ) * 1 :=
        mul_le_mul h2 hlog2_le1 (Real.log_nonneg (by norm_num)) (by positivity)
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
    linarith
  have hZ2_lt_B : (Z_k2 n Y₁) ^ 2 < B_k2 n X₁ := by
    have h1 : ((Z_k2 n Y₁ ^ 2 : ℕ) : ℝ) < (B_k2 n X₁ : ℝ) := by
      rw [Nat.cast_pow]
      exact (Real.log_lt_log_iff (by positivity) (by exact_mod_cast B_k2_pos n X₁)).mp hZ2_log
    exact_mod_cast h1
  have hZ2_pos : 0 < (Z_k2 n Y₁) ^ 2 := pow_pos (Z_k2_pos n Y₁) 2
  have hquartic := (thm_4_2_part1_quartic_law hn8 hm hfund hk2).2.2.2.1
  have hdiv : A_k2 n X₁ / B_k2 n X₁ = (Z_k2 n Y₁) ^ 4 := by
    rw [hquartic, mul_comm (B_k2 n X₁) ((Z_k2 n Y₁) ^ 4), Nat.mul_add_div (B_k2_pos n X₁),
        Nat.div_eq_of_lt hZ2_lt_B, add_zero]
  have hmod : A_k2 n X₁ % B_k2 n X₁ = (Z_k2 n Y₁) ^ 2 := by
    rw [hquartic, mul_comm (B_k2 n X₁) ((Z_k2 n Y₁) ^ 4), Nat.mul_add_mod,
        Nat.mod_eq_of_lt hZ2_lt_B]
  refine ⟨hZ2_pos, hZ2_lt_B, hdiv, hmod, ?_⟩
  rw [hdiv, hmod]
  ring

/-- **Theorem 4.2(ii) (Second-Stage Consecutive Splitting and Dual Quartic Locks, eqs. 4.11–4.12)**:
Let `c₀ := Nat.gcd (X₁ - 1) (X₁ + 1) ∈ {1, 2}`. Then there exist coprime `B₋, B₊` and
coprime `Z₋, Z₊` such that:
- `B₋ * B₊ = B_k2 n X₁ / c₀ ^ 2` and `Z₋ * Z₊ = Z_k2 n Y₁`,
- `(X₁ - 1) / c₀ = B₋ * Z₋ ^ 2`, `(X₁ + 1) / c₀ = B₊ * Z₊ ^ 2`, `B₊ * Z₊ ^ 2 - B₋ * Z₋ ^ 2 = 2 / c₀`,
- `B₊ * (Z_k2 n Y₁) ^ 2 = B₋ * Z₋ ^ 4 + (2 / c₀) * Z₋ ^ 2`,
- `B₋ * (Z_k2 n Y₁) ^ 2 = B₊ * Z₊ ^ 4 - (2 / c₀) * Z₊ ^ 2`. -/
theorem thm_4_2_part2_dual_quartic {n m X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hm : Nat.factorial n + 1 = m ^ 2)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk2 : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2) :
    let c₀ := Nat.gcd (X₁ - 1) (X₁ + 1)
    (c₀ = 1 ∨ c₀ = 2) ∧
    ∃ B₋ B₊ Z₋ Z₊ : ℕ,
      0 < B₋ ∧ 0 < B₊ ∧ 0 < Z₋ ∧ 0 < Z₊ ∧
      Nat.Coprime B₋ B₊ ∧ Nat.Coprime Z₋ Z₊ ∧
      B₋ * B₊ = B_k2 n X₁ / c₀ ^ 2 ∧
      Z₋ * Z₊ = Z_k2 n Y₁ ∧
      (X₁ - 1) / c₀ = B₋ * Z₋ ^ 2 ∧
      (X₁ + 1) / c₀ = B₊ * Z₊ ^ 2 ∧
      B₊ * Z₊ ^ 2 - B₋ * Z₋ ^ 2 = 2 / c₀ ∧
      B₊ * (Z_k2 n Y₁) ^ 2 = B₋ * Z₋ ^ 4 + (2 / c₀) * Z₋ ^ 2 ∧
      B₋ * (Z_k2 n Y₁) ^ 2 = B₊ * Z₊ ^ 4 - (2 / c₀) * Z₊ ^ 2 := by
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
          rw [padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)]
          exact dvd_trans (by decide : 2 ^ 4 ∣ Nat.factorial 6) (Nat.factorial_dvd_factorial (by omega : 6 ≤ n))
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
  let B₋ := Nat.gcd u₁ B₀
  let B₊ := Nat.gcd u₂ B₀
  let Z₋ := Nat.gcd u₁ Z
  let Z₊ := Nat.gcd u₂ Z
  have hB₀_pos : 0 < B₀ := Nat.div_pos (Nat.le_of_dvd (B_k2_pos n X₁) hc₀_sq_dvd) (pow_pos hc₀_pos 2)
  have hZ_pos : 0 < Z := Z_k2_pos n Y₁
  have hB₋_pos : 0 < B₋ := Nat.gcd_pos_of_pos_left _ hu₁_pos
  have hB₊_pos : 0 < B₊ := Nat.gcd_pos_of_pos_left _ hu₂_pos
  have hZ₋_pos : 0 < Z₋ := Nat.gcd_pos_of_pos_left _ hu₁_pos
  have hZ₊_pos : 0 < Z₊ := Nat.gcd_pos_of_pos_left _ hu₂_pos
  have hcop_B : Nat.Coprime B₋ B₊ := by
    refine Nat.coprime_of_dvd' (fun p hp h1 h2 => ?_)
    exact hp.not_dvd_one (Nat.dvd_gcd (dvd_trans h1 (Nat.gcd_dvd_left _ _))
      (dvd_trans h2 (Nat.gcd_dvd_left _ _)) |>.trans (by rw [hcop_u]))
  have hcop_Z : Nat.Coprime Z₋ Z₊ := by
    refine Nat.coprime_of_dvd' (fun p hp h1 h2 => ?_)
    exact hp.not_dvd_one (Nat.dvd_gcd (dvd_trans h1 (Nat.gcd_dvd_left _ _))
      (dvd_trans h2 (Nat.gcd_dvd_left _ _)) |>.trans (by rw [hcop_u]))
  have hB_prod : B₋ * B₊ = B₀ := by
    have hdvd_B : B₀ ∣ u₁ * u₂ := ⟨Z ^ 2, hprod_u.symm⟩
    exact (Nat.gcd_mul_gcd_of_coprime_of_dvd hcop_u hdvd_B).symm
  have hZ_prod : Z₋ * Z₊ = Z := by
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
  have hu₁_eq : u₁ = B₋ * Z₋ ^ 2 := by
    apply Nat.eq_of_factorization_eq hu₁_pos.ne' (mul_ne_zero hB₋_pos.ne' (pow_ne_zero 2 hZ₋_pos.ne'))
    intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [Nat.factorization_mul hB₋_pos.ne' (pow_ne_zero 2 hZ₋_pos.ne'), Nat.factorization_pow]
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
      have h0b : (B₋ * Z₋ ^ 2).factorization p = 0 := by
        by_contra h0; exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
      omega
  have hu₂_eq : u₂ = B₊ * Z₊ ^ 2 := by
    apply Nat.eq_of_factorization_eq hu₂_pos.ne' (mul_ne_zero hB₊_pos.ne' (pow_ne_zero 2 hZ₊_pos.ne'))
    intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [Nat.factorization_mul hB₊_pos.ne' (pow_ne_zero 2 hZ₊_pos.ne'), Nat.factorization_pow]
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
      have h0b : (B₊ * Z₊ ^ 2).factorization p = 0 := by
        by_contra h0; exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
      omega
  have hdiff_BZ : B₊ * Z₊ ^ 2 - B₋ * Z₋ ^ 2 = 2 / c₀ := by
    rw [← hu₁_eq, ← hu₂_eq]; exact hdiff_u
  have hq_minus : B₊ * Z ^ 2 = B₋ * Z₋ ^ 4 + (2 / c₀) * Z₋ ^ 2 := by
    have h1 : B₊ * Z₊ ^ 2 = B₋ * Z₋ ^ 2 + (2 / c₀) := by omega
    calc B₊ * Z ^ 2 = B₊ * (Z₋ * Z₊) ^ 2 := by rw [hZ_prod]
      _ = (B₊ * Z₊ ^ 2) * Z₋ ^ 2 := by ring
      _ = (B₋ * Z₋ ^ 2 + 2 / c₀) * Z₋ ^ 2 := by rw [h1]
      _ = B₋ * Z₋ ^ 4 + (2 / c₀) * Z₋ ^ 2 := by ring
  have hq_plus : B₋ * Z ^ 2 = B₊ * Z₊ ^ 4 - (2 / c₀) * Z₊ ^ 2 := by
    have h1 : B₋ * Z₋ ^ 2 + 2 / c₀ = B₊ * Z₊ ^ 2 := by omega
    have hle : (2 / c₀) * Z₊ ^ 2 ≤ B₊ * Z₊ ^ 4 := by
      have : 2 / c₀ ≤ B₊ * Z₊ ^ 2 := by omega
      calc (2 / c₀) * Z₊ ^ 2 ≤ (B₊ * Z₊ ^ 2) * Z₊ ^ 2 := Nat.mul_le_mul_right _ this
        _ = B₊ * Z₊ ^ 4 := by ring
    zify [hle]
    have h1z : (B₋ : ℤ) * (Z₋ : ℤ) ^ 2 + (2 / c₀ : ℕ) = (B₊ : ℤ) * (Z₊ : ℤ) ^ 2 := by exact_mod_cast h1
    have hZz : (Z : ℤ) = (Z₋ : ℤ) * (Z₊ : ℤ) := by exact_mod_cast hZ_prod.symm
    rw [hZz]
    nlinarith
  exact ⟨hc₀_12, B₋, B₊, Z₋, Z₊, hB₋_pos, hB₊_pos, hZ₋_pos, hZ₊_pos,
    hcop_B, hcop_Z, hB_prod, hZ_prod, hu₁_eq, hu₂_eq, hdiff_BZ, hq_minus, hq_plus⟩

/-- **Theorem 4.2(ii) (Euclidean Quotient-Remainder Locks and `log B_∓` Asymptotics, eqs. 4.13, 4.15)**:
For every `ε ∈ (0, 1/6)`, for all sufficiently large `n` with a `k = 2` solution `(n, m)`, the
second-stage factors `B₋, B₊, Z₋, Z₊` satisfy:
1. `(1/4 - ε) n log n ≤ log B_∓ ≤ (1/4 + ε) n log n` (eq. 4.15),
2. `(2 / c₀) * Z₋ ^ 2 < B₋` and `(2 / c₀) * Z₊ ^ 2 < B₊`,
3. `(B₊ * Z^2) / B₋ = Z₋^4` and `(B₋ * Z^2 + B₊ - 1) / B₊ = Z₊^4` (eq. 4.13). -/
theorem thm_4_2_part2_euclidean_locks (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 6) :
    ∃ N₀ : ℕ, ∀ n m X₁ Y₁ : ℕ, N₀ ≤ n →
      Nat.factorial n + 1 = m ^ 2 →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2 →
      let c₀ := Nat.gcd (X₁ - 1) (X₁ + 1)
      ∃ B₋ B₊ Z₋ Z₊ : ℕ,
        0 < B₋ ∧ 0 < B₊ ∧ 0 < Z₋ ∧ 0 < Z₊ ∧
        Nat.Coprime B₋ B₊ ∧ Nat.Coprime Z₋ Z₊ ∧
        B₋ * B₊ = B_k2 n X₁ / c₀ ^ 2 ∧
        Z₋ * Z₊ = Z_k2 n Y₁ ∧
        (X₁ - 1) / c₀ = B₋ * Z₋ ^ 2 ∧
        (X₁ + 1) / c₀ = B₊ * Z₊ ^ 2 ∧
        (1 / 4 - ε) * ((n : ℝ) * Real.log (n : ℝ)) ≤ Real.log (B₋ : ℝ) ∧
        Real.log (B₋ : ℝ) ≤ (1 / 4 + ε) * ((n : ℝ) * Real.log (n : ℝ)) ∧
        (1 / 4 - ε) * ((n : ℝ) * Real.log (n : ℝ)) ≤ Real.log (B₊ : ℝ) ∧
        Real.log (B₊ : ℝ) ≤ (1 / 4 + ε) * ((n : ℝ) * Real.log (n : ℝ)) ∧
        (2 / c₀) * Z₋ ^ 2 < B₋ ∧
        (2 / c₀) * Z₊ ^ 2 < B₊ ∧
        (B₊ * (Z_k2 n Y₁) ^ 2) / B₋ = Z₋ ^ 4 ∧
        (B₋ * (Z_k2 n Y₁) ^ 2 + B₊ - 1) / B₊ = Z₊ ^ 4 := by
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
  obtain ⟨hc₀_12, B₋, B₊, Z₋, Z₊, hB₋_pos, hB₊_pos, hZ₋_pos, hZ₊_pos,
    hcop_B, hcop_Z, hB_prod, hZ_prod, hu₁_eq, hu₂_eq, _, hq_minus, hq_plus⟩ := hpart2
  have hn6 : n ≠ 6 := by omega
  obtain ⟨_, _, _, _, _, _, hfac_eq⟩ := k_eq_2_identities (by omega) hn6 hm hfund hk2
  have hX1_pos : 1 ≤ X₁ := hfund.1
  have hX1_gt1 : 1 < X₁ := by
    by_contra hle; have h1 : X₁ = 1 := by omega; rw [h1] at hfac_eq; simp at hfac_eq
    exact Nat.factorial_ne_zero n hfac_eq
  have hfac_lo : (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) ≤ Real.log ((Nat.factorial n : ℕ) : ℝ) :=
    (n_log_n_sub_n_le_log_factorial n (by omega)).1
  have hfac_hi : Real.log ((Nat.factorial n : ℕ) : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    have hle : Nat.factorial n ≤ n ^ n := Nat.factorial_le_pow n
    have h1 := Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) (by exact_mod_cast hle : ((Nat.factorial n : ℕ) : ℝ) ≤ ((n ^ n : ℕ) : ℝ))
    rw [Nat.cast_pow, Real.log_pow] at h1
    exact h1
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
  have hc₀_ge1 : 1 ≤ c₀ := by rcases hc₀_12 with h | h <;> omega
  have hc₀_le2 : c₀ ≤ 2 := by rcases hc₀_12 with h | h <;> omega
  have hb_minus := h_bounds B₋ Z₋ ((X₁ - 1) / c₀) hB₋_pos hZ₋_pos ⟨Z₊, hZ_prod.symm⟩ hu₁_eq.symm
    (Nat.div_le_div_left hc₀_le2 (by omega)) (Nat.div_le_self _ _ |>.trans (by omega))
  have hb_plus := h_bounds B₊ Z₊ ((X₁ + 1) / c₀) hB₊_pos hZ₊_pos ⟨Z₋, by rw [← hZ_prod, mul_comm]⟩ hu₂_eq.symm
    (by have := Nat.div_le_div_left hc₀_le2 (by omega : 0 < c₀); have : (X₁ - 1) / 2 ≤ (X₁ + 1) / 2 := Nat.div_le_div_right (by omega); omega)
    (Nat.div_le_self _ _)
  have h2c₀_minus : (2 / c₀) * Z₋ ^ 2 < B₋ := by
    have : 2 / c₀ ≤ 2 := Nat.div_le_self 2 c₀
    nlinarith [hb_minus.2.2]
  have h2c₀_plus : (2 / c₀) * Z₊ ^ 2 < B₊ := by
    have : 2 / c₀ ≤ 2 := Nat.div_le_self 2 c₀
    nlinarith [hb_plus.2.2]
  have hlock_minus : (B₊ * (Z_k2 n Y₁) ^ 2) / B₋ = Z₋ ^ 4 := by
    rw [hq_minus, mul_comm B₋ (Z₋ ^ 4), Nat.mul_add_div hB₋_pos, Nat.div_eq_of_lt h2c₀_minus, add_zero]
  have hlock_plus : (B₋ * (Z_k2 n Y₁) ^ 2 + B₊ - 1) / B₊ = Z₊ ^ 4 := by
    have h_eq : B₋ * (Z_k2 n Y₁) ^ 2 + B₊ - 1 = B₊ * Z₊ ^ 4 + (B₊ - (2 / c₀) * Z₊ ^ 2 - 1) := by
      have hle1 : (2 / c₀) * Z₊ ^ 2 ≤ B₊ * Z₊ ^ 4 := by
        have : 1 ≤ Z₊ ^ 2 := Nat.one_le_pow 2 Z₊ hZ₊_pos
        nlinarith [h2c₀_plus]
      omega
    have h_rem_lt : B₊ - (2 / c₀) * Z₊ ^ 2 - 1 < B₊ := by omega
    rw [h_eq, mul_comm B₊ (Z₊ ^ 4), Nat.mul_add_div hB₊_pos, Nat.div_eq_of_lt h_rem_lt, add_zero]
  exact ⟨B₋, B₊, Z₋, Z₊, hB₋_pos, hB₊_pos, hZ₋_pos, hZ₊_pos, hcop_B, hcop_Z, hB_prod, hZ_prod,
    hu₁_eq, hu₂_eq, hb_minus.1, hb_minus.2.1, hb_plus.1, hb_plus.2.1,
    h2c₀_minus, h2c₀_plus, hlock_minus, hlock_plus⟩

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
    have hsub : (1 / 2 - ε - 0) / (2 : ℝ) = 1 / 4 - ε / 2 := by ring
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
    dsimp only [Function.comp_apply] at hn_big hlog1 hrpow2
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
  obtain ⟨hc₀_12, B₋, B₊, Z₋, Z₊, hB₋_pos, hB₊_pos, hZ₋_pos, hZ₊_pos,
    hcop_B, hcop_Z, hB_prod, hZ_prod, hu₁_eq, hu₂_eq, _, _, _⟩ := hpart2
  have hpart1 := prop_4_1_part1 hn8 hm hfund hk2
  have hn6 : n ≠ 6 := by omega
  obtain ⟨_, _, _, _, _, _, hfac_eq⟩ := k_eq_2_identities (by omega) hn6 hm hfund hk2
  have hX1_pos : 1 ≤ X₁ := hfund.1
  have hq1 := thm_4_2_part1_quartic_law hn8 hm hfund hk2
  have hZ_log_bound : 4 * Real.log (Z_k2 n Y₁ : ℝ) ≤ (2 * ε / 100) * ((n : ℝ) * Real.log (n : ℝ)) := by
    have hA_ge : (B_k2 n X₁ : ℝ) * (Z_k2 n Y₁ : ℝ) ^ 4 ≤ (A_k2 n X₁ : ℝ) := by
      exact_mod_cast (by linarith [hq1.2.2.2.1] : B_k2 n X₁ * (Z_k2 n Y₁) ^ 4 ≤ A_k2 n X₁)
    have hB_pos_r : (0 : ℝ) < (B_k2 n X₁ : ℝ) := by exact_mod_cast B_k2_pos n X₁
    have hZ_pos_r : (0 : ℝ) < (Z_k2 n Y₁ : ℝ) := by exact_mod_cast Z_k2_pos n Y₁
    have hlog_AB : 4 * Real.log (Z_k2 n Y₁ : ℝ) ≤ Real.log (A_k2 n X₁ : ℝ) - Real.log (B_k2 n X₁ : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hA_ge
      rw [Real.log_mul hB_pos_r.ne' (pow_ne_zero 4 hZ_pos_r.ne'), Real.log_pow] at h1
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
        linarith [le_abs_self (Delta_parity n)]
      · rw [Nat.cast_mul, Real.log_mul (by positivity) (A_star_pos n |> Nat.cast_pos.mpr |>.ne'),
            log_A_star_eq, log_B_star_eq, Nat.cast_pow, Real.log_pow]
        have h1 : S_even n - S_odd n = Delta_parity n := by unfold Delta_parity; ring
        have h2 : ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
          have : padicValNat 2 (Nat.factorial n) - 2 ≤ padicValNat 2 (Nat.factorial n) := Nat.sub_le _ _
          linarith [show ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) ≤ (padicValNat 2 (Nat.factorial n) : ℝ) by exact_mod_cast this]
        have h3 : ((padicValNat 2 (Nat.factorial n) - 2 : ℕ) : ℝ) * Real.log 2 ≤ (n : ℝ) * 1 :=
          mul_le_mul h2 hlog2_le1 (Real.log_nonneg (by norm_num)) (by positivity)
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
      Z_i ∣ Z_k2 n Y₁ → B_i * B_other ∣ B_k2 n X₁ → Nat.Coprime B_i B_other →
      u_i = B_i * Z_i ^ 2 → (X₁ - 1) / 2 ≤ u_i →
      δ = sfCore u_i →
      (∃ p : ℕ, p.Prime ∧ p ∣ δ ∧ (n : ℝ) ^ (1 / 2 - ε) < (p : ℝ)) ∧
      (ε / 5) * (n : ℝ) ^ (1 / 2 - ε) ≤ (δ.primeFactors.card : ℝ) ∧
      (ε / 15) * (n : ℝ) ^ (1 / 2 - ε) * Real.log (n : ℝ) ≤ Real.log (δ : ℝ) := by
    intro δ u_i B_i B_other Z_i hB_pos hBo_pos hZ_pos hZ_dvd hB_mul_dvd hB_cop hu_eq hX_le hδ_eq
    have hB_dvd : B_i ∣ B_k2 n X₁ := dvd_trans (dvd_mul_right B_i B_other) hB_mul_dvd
    have hB_log := hlog_B_lo B_i Z_i u_i hB_pos hZ_pos hZ_dvd hu_eq hX_le
    have hu_pos : 0 < u_i := by rw [hu_eq]; exact mul_pos hB_pos (pow_pos hZ_pos 2)
    have hδ_pos : 0 < δ := by
      rw [hδ_eq]
      exact Nat.pos_of_ne_zero (fun h0 => by
        have := eq_sfCore_mul_sqPart_sq u_i
        rw [h0, zero_mul] at this
        omega)
    have hB_odd_primes : ∀ p ∈ B_i.primeFactors, p ≠ 2 →
        p ∈ Podd n ∧ padicValNat p B_i ≤ padicValNat p (Nat.factorial n) ∧ p ∣ δ := by
      intro p hp_mem hp2
      have hp_pr := Nat.prime_of_mem_primeFactors hp_mem
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
        obtain ⟨q, hq, hqd⟩ := hp_pr.dvd_finset_prod_iff.mp hp_Bstar
        have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
        have heq := (Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp (hp_pr.dvd_of_dvd_pow hqd)
        subst heq
        exact (Finset.mem_filter.mp hq).1
      have hp_val_Bk2 : padicValNat p (B_k2 n X₁) = padicValNat p (Nat.factorial n) := by
        haveI : Fact p.Prime := ⟨hp_pr⟩
        have h1 : A_k2 n X₁ * B_k2 n X₁ * 4 = Nat.factorial n := by
          have h2_le : 2 ≤ padicValNat 2 (Nat.factorial n) := by
            rw [padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)]
            exact dvd_trans (by decide : 2 ^ 2 ∣ 24) (Nat.factorial_dvd_factorial (by omega : 4 ≤ n))
          have h1' : A_k2 n X₁ * B_k2 n X₁ = A_star n * B_star n * 2 ^ (padicValNat 2 (Nat.factorial n) - 2) := by
            unfold A_k2 B_k2; split_ifs <;> ring
          rw [h1', ← A_star_mul_B_star n]
          have hpow : 2 ^ (padicValNat 2 (Nat.factorial n) - 2) * 4 = 2 ^ padicValNat 2 (Nat.factorial n) := by
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel h2_le]
          calc A_star n * B_star n * 2 ^ (padicValNat 2 (Nat.factorial n) - 2) * 4
              = A_star n * B_star n * (2 ^ (padicValNat 2 (Nat.factorial n) - 2) * 4) := by ring
            _ = A_star n * B_star n * 2 ^ padicValNat 2 (Nat.factorial n) := by rw [hpow]
        have hnd4 : ¬ p ∣ 4 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
        have hndA : ¬ p ∣ A_k2 n X₁ := fun h =>
          hp_pr.not_dvd_one (Nat.dvd_gcd h hp_Bk2 |>.trans (by rw [hq1.1]))
        rw [← h1, padicValNat.mul (mul_ne_zero (A_k2_pos n X₁).ne' (B_k2_pos n X₁).ne') (by norm_num),
            padicValNat.mul (A_k2_pos n X₁).ne' (B_k2_pos n X₁).ne',
            padicValNat.eq_zero_of_not_dvd hndA, padicValNat.eq_zero_of_not_dvd hnd4]
        simp
      have hp_val_Bi_le : padicValNat p B_i ≤ padicValNat p (Nat.factorial n) := by
        haveI : Fact p.Prime := ⟨hp_pr⟩
        rw [← hp_val_Bk2]
        exact padicValNat.dvd_iff_le (B_k2_pos n X₁).ne' |>.mp hB_dvd |>.2
      -- Also `p ∤ Z_i` since `p ∈ Podd n` while `Z_k2` only has primes in `Peven n`
      have hp_nd_Z : ¬ p ∣ Z_i := by
        intro hpZ
        have hpZ' : p ∣ Z_k2 n Y₁ := dvd_trans hpZ hZ_dvd
        unfold Z_k2 at hpZ'
        obtain ⟨q, hq, hqd⟩ := hp_pr.dvd_finset_prod_iff.mp hpZ'
        have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
        have heq := (Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp (hp_pr.dvd_of_dvd_pow hqd)
        subst heq
        exact (Finset.mem_filter.mp hp_Podd).2.2 (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.2
      -- Moreover `padicValNat p B_i = padicValNat p (B_k2 n X₁) = padicValNat p (n!)`
      have hp_val_Bi_eq : padicValNat p B_i = padicValNat p (Nat.factorial n) := by
        haveI : Fact p.Prime := ⟨hp_pr⟩
        have hnd_Bo : ¬ p ∣ B_other := fun h =>
          hp_pr.not_dvd_one (Nat.dvd_gcd hp_B h |>.trans (by rw [hB_cop]))
        have h_c0_sq : B_k2 n X₁ = (B_k2 n X₁ / (Nat.gcd (X₁ - 1) (X₁ + 1)) ^ 2) * (Nat.gcd (X₁ - 1) (X₁ + 1)) ^ 2 := by
          -- actually `B_i * B_other ∣ B_k2`, wait: we need `B_i * B_other = B_k2 / c₀^2` and `p ∤ c₀`!
          -- Wait: `p` divides `B_i`, and `p ∤ B_other`. What if `k = B_k2 / (B_i * B_other)`?
          -- Since `B_i * B_other ∣ B_k2`, let `B_k2 = (B_i * B_other) * r`. We only need `padicValNat p B_i` is ODD!
          -- Wait: if `B_i * B_other = B_k2 / c₀^2`, then `r = c₀^2 ∈ {1, 4}`, so `p ∤ r`!
          -- What if we didn't assume `B_i * B_other = B_k2 / c₀^2`, only `B_i * B_other ∣ B_k2`?
          -- No, let's check: in `h_core_from_B`, we pass `B_k2 n X₁ = B_i * B_other * c₀ ^ 2` directly!
          sorry
        sorry
      sorry
    sorry
  sorry

end GrasGreenbergBrocard
