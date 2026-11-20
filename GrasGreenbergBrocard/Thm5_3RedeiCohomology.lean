import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic
import GrasGreenbergBrocard.ExternalAxiomsSec3
import GrasGreenbergBrocard.ExternalAxiomsSec4
import GrasGreenbergBrocard.ExternalAxiomsSec5
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.PellFundamental
import GrasGreenbergBrocard.Prop5_1MidpointBias
import GrasGreenbergBrocard.Thm5_2EffectiveCores

/-!
# Theorem 5.3: Rédei–Reichardt 4-Rank Cohomology and Reduced Dual Quartic Laws

Formalizes Section 5.2, Theorem 5.3(i)–(ii), and equations (5.8)–(5.10) of the manuscript:
- `thm_5_3_part1_cohomology_4rank`: Galois cohomology exact sequence (eq. 5.8) and
  `dim_{𝔽₂} ker_{𝔽₂}(R_n^{ram}) = 1 + rank₄ Cl^+(q_n)` (eq. 5.9)
- `PevenPlus`, `PevenMinus`: split-even and inert-even prime partitions `𝒫_even^±(n)`
- `thm_5_3_part2_inert_absorption`: deterministic `𝒫_even^-(n)`-absorption into `z₁, z₂`
- `thm_5_3_part2_dual_quartic`: reduced dual quartic equations (eq. 5.10)
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Finset BigOperators

namespace GrasGreenbergBrocard

/-! ### Theorem 5.3(i): Midpoint Norm Cocycle Proofs & Galois Cohomology 4-Rank Identity -/

private lemma q_n_pos_53 (n : ℕ) : 0 < q_n n := by
  unfold q_n
  exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.1.pos)

private lemma dvd_of_sq_dvd_sqfree_mul_sq {q m Y : ℕ} (hq : Squarefree q) (hq0 : q ≠ 0)
    (hY0 : Y ≠ 0) (hm0 : m ≠ 0) (hdvd : m ^ 2 ∣ q * Y ^ 2) : m ∣ Y := by
  rw [← Nat.factorization_le_iff_dvd hm0 hY0]
  intro p
  by_cases hp : p.Prime
  · have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hm0) (mul_ne_zero hq0 (pow_ne_zero 2 hY0))).mpr hdvd p
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.factorization_mul hq0 (pow_ne_zero 2 hY0),
      Finsupp.add_apply] at hle
    have hqp : q.factorization p ≤ 1 := by
      by_contra hgt; push_neg at hgt
      have hp2 : p ^ 2 ∣ q := by
        have := Nat.ordProj_dvd q p
        exact dvd_trans (pow_dvd_pow p (by omega : 2 ≤ q.factorization p)) this
      exact hp.ne_one (Nat.isUnit_iff.mp (hq p (by simpa [sq] using hp2)))
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private lemma prime_dvd_q_n_iff_mem_Podd {n p : ℕ} (hp : p.Prime) :
    p ∣ q_n n ↔ p ∈ Podd n := by
  constructor
  · intro hdvd
    unfold q_n at hdvd
    by_contra hnot
    have hcop : Nat.Coprime p (∏ q ∈ Podd n, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hq_pr : q.Prime := (Finset.mem_filter.mp hq).2.1
      exact (Nat.coprime_primes hp hq_pr).mpr (fun h => hnot (h ▸ hq))
    have h1 : p ∣ Nat.gcd p (∏ q ∈ Podd n, q) := Nat.dvd_gcd dvd_rfl hdvd
    rw [hcop.gcd_eq_one] at h1
    exact hp.not_dvd_one h1
  · intro hmem
    unfold q_n
    exact Finset.dvd_prod_of_mem _ hmem

private lemma prime_mem_ramPrimes_prime {n p : ℕ} (hp : p ∈ ramPrimes n) : p.Prime := by
  unfold ramPrimes at hp
  split_ifs at hp with hq
  · exact (Finset.mem_filter.mp hp).2.1
  · rcases Finset.mem_insert.mp hp with rfl | hmem
    · exact Nat.prime_two
    · exact (Finset.mem_filter.mp hmem).2.1

private lemma two_not_dvd_coreNat_two_mul_X1_add_one_of_mod4_eq1 {n X₁ Y₁ : ℕ}
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁) (hq1 : q_n n % 4 = 1) :
    ¬ 2 ∣ coreNat (2 * (X₁ + 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX1_pos : 0 < X₁ := by have := hfund.1; omega
  have hY1_pos : 0 < Y₁ := hfund.2.1
  have hpell : X₁ ^ 2 = q_n n * Y₁ ^ 2 + 1 := hfund.2.2.1
  have hX1_odd : X₁ % 2 = 1 := by
    by_contra hev
    have h0 : X₁ % 2 = 0 := by omega
    have h1 : X₁ ^ 2 % 4 = 0 := by
      obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero h0
      rw [show (2 * k) ^ 2 = 4 * k ^ 2 by ring]; omega
    have hY_mod : Y₁ ^ 2 % 4 = 0 ∨ Y₁ ^ 2 % 4 = 1 := by
      rcases Nat.even_or_odd Y₁ with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · left; rw [show (k + k) ^ 2 = 4 * k ^ 2 by ring]; omega
      · right; rw [show (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 by ring]; omega
    have hrhs : (q_n n * Y₁ ^ 2 + 1) % 4 = 1 ∨ (q_n n * Y₁ ^ 2 + 1) % 4 = 2 := by
      rcases hY_mod with hy | hy
      · left; rw [Nat.add_mod, Nat.mul_mod, hq1, hy]
      · right; rw [Nat.add_mod, Nat.mul_mod, hq1, hy]
    omega
  have hX1_gt1 : 1 < X₁ := by
    have hq_pos := q_n_pos_53 n
    nlinarith [hpell, hq_pos, hY1_pos]
  have hprod : (X₁ - 1) * (X₁ + 1) = q_n n * Y₁ ^ 2 := by
    zify [show 1 ≤ X₁ by omega] at hpell ⊢; linarith
  have hq_odd : ¬ 2 ∣ q_n n := by omega
  have hvq : padicValNat 2 (q_n n) = 0 := padicValNat.eq_zero_of_not_dvd hq_odd
  have hv_sum : padicValNat 2 (X₁ - 1) + padicValNat 2 (X₁ + 1) = 2 * padicValNat 2 Y₁ := by
    have h1 := congrArg (padicValNat 2) hprod
    rw [padicValNat.mul (by omega) (by omega),
      padicValNat.mul (q_n_pos_53 n).ne' (pow_ne_zero 2 hY1_pos.ne'),
      sq, padicValNat.mul hY1_pos.ne' hY1_pos.ne', hvq, zero_add] at h1
    omega
  have hnot_both4 : ¬ (4 ∣ X₁ - 1 ∧ 4 ∣ X₁ + 1) := by
    rintro ⟨h1, h2⟩
    have hsub : 4 ∣ (X₁ + 1) - (X₁ - 1) := Nat.dvd_sub h2 h1
    rw [show (X₁ + 1) - (X₁ - 1) = 2 by omega] at hsub
    omega
  have hv_one : padicValNat 2 (X₁ - 1) = 1 ∨ padicValNat 2 (X₁ + 1) = 1 := by
    have h2m : 2 ∣ X₁ - 1 := by omega
    have h2p : 2 ∣ X₁ + 1 := by omega
    have hvm : 1 ≤ padicValNat 2 (X₁ - 1) := one_le_padicValNat_of_dvd (by omega) h2m
    have hvp : 1 ≤ padicValNat 2 (X₁ + 1) := one_le_padicValNat_of_dvd (by omega) h2p
    by_contra hneither
    push_neg at hneither
    apply hnot_both4
    exact ⟨dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ padicValNat 2 (X₁ - 1))) pow_padicValNat_dvd,
           dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ padicValNat 2 (X₁ + 1))) pow_padicValNat_dvd⟩
  have hvp_odd : padicValNat 2 (X₁ + 1) % 2 = 1 := by omega
  have hv2p : padicValNat 2 (2 * (X₁ + 1)) % 2 = 0 := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]; omega
  intro hdvd
  have hvc : 1 ≤ padicValNat 2 (coreNat (2 * (X₁ + 1))) :=
    one_le_padicValNat_of_dvd (coreNat_pos _).ne' hdvd
  rw [padicValNat_coreNat Nat.prime_two (by omega), if_neg (by omega)] at hvc
  omega

private lemma coreNat_two_X1_add_one_prime_mem_ramPrimes {n X₁ Y₁ p : ℕ}
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hp : p.Prime) (hdvd : p ∣ coreNat (2 * (X₁ + 1))) :
    p ∈ ramPrimes n := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst hp2
    have hq_ne1 : q_n n % 4 ≠ 1 := fun h1 =>
      two_not_dvd_coreNat_two_mul_X1_add_one_of_mod4_eq1 hfund h1 hdvd
    unfold ramPrimes; rw [if_neg hq_ne1]; exact Finset.mem_insert_self 2 _
  · have hvc : padicValNat p (coreNat (2 * (X₁ + 1))) = 1 := by
      have h1 := one_le_padicValNat_of_dvd (coreNat_pos _).ne' hdvd
      have h2 := padicValNat_coreNat hp (by omega : 0 < 2 * (X₁ + 1))
      split_ifs at h2 <;> omega
    have hv_odd : padicValNat p (2 * (X₁ + 1)) % 2 = 1 := by
      have h2 := padicValNat_coreNat hp (by omega : 0 < 2 * (X₁ + 1))
      rw [hvc] at h2
      by_contra hne
      rw [if_neg hne] at h2
      omega
    have hv2 : padicValNat p 2 = 0 := padicValNat.eq_zero_of_not_dvd (fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
    rw [padicValNat.mul (by norm_num) (by omega), hv2, zero_add] at hv_odd
    have hp_dvd_p1 : p ∣ X₁ + 1 := by
      simpa using dvd_trans (pow_dvd_pow p (by omega : 1 ≤ padicValNat p (X₁ + 1))) pow_padicValNat_dvd
    have hp_not_m1 : ¬ p ∣ X₁ - 1 := by
      intro hm1
      have hX1_gt1 : 1 < X₁ := by
        have := hfund.2.2.1; have := hfund.2.1; have := q_n_pos_53 n; nlinarith
      have hsub : p ∣ (X₁ + 1) - (X₁ - 1) := Nat.dvd_sub hp_dvd_p1 hm1
      rw [show (X₁ + 1) - (X₁ - 1) = 2 by omega] at hsub
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hsub)
    have hX1_gt1 : 1 < X₁ := by
      have := hfund.2.2.1; have := hfund.2.1; have := q_n_pos_53 n; nlinarith
    have hprod : (X₁ - 1) * (X₁ + 1) = q_n n * Y₁ ^ 2 := by
      have := hfund.2.2.1; zify [show 1 ≤ X₁ by omega] at this ⊢; linarith
    have hvm1 : padicValNat p (X₁ - 1) = 0 := padicValNat.eq_zero_of_not_dvd hp_not_m1
    have hv_eq := congrArg (padicValNat p) hprod
    rw [padicValNat.mul (by omega) (by omega), hvm1, zero_add,
      padicValNat.mul (q_n_pos_53 n).ne' (pow_ne_zero 2 hfund.2.1.ne'),
      sq, padicValNat.mul hfund.2.1.ne' hfund.2.1.ne'] at hv_eq
    have hvq_odd : padicValNat p (q_n n) % 2 = 1 := by omega
    have hp_q : p ∣ q_n n := by
      simpa using dvd_trans (pow_dvd_pow p (by omega : 1 ≤ padicValNat p (q_n n))) pow_padicValNat_dvd
    have hp_podd : p ∈ Podd n := (prime_dvd_q_n_iff_mem_Podd hp).mp hp_q
    unfold ramPrimes
    split_ifs
    · exact hp_podd
    · exact Finset.mem_insert_of_mem hp_podd

/-- **Non-vanishing of the Midpoint Vector** (pure kernel proof, zero external axioms):
For every `n ≥ 8` and fundamental Pell solution `(X₁, Y₁)` of `q_n`, `yMidVec n X₁ ≠ 0`. -/
theorem yMidVec_ne_zero {n X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁) :
    yMidVec n X₁ ≠ 0 := by
  have hq_pos := q_n_pos_53 n
  have hq2 : 2 ≤ q_n n := by
    have h1 := oddPartNat_q_n_gt_one hn
    have h2 := oddPartNat_le (m := q_n n)
    omega
  have hX1_gt1 : 1 < X₁ := by nlinarith [hfund.2.2.1, hq2, hfund.2.1]
  have hc_ne1 : coreNat (2 * (X₁ + 1)) ≠ 1 := by
    intro hc1
    have hmul := coreNat_mul_sqPartNat_sq (m := 2 * (X₁ + 1)) (by omega)
    rw [hc1, one_mul] at hmul
    set v := sqPartNat (2 * (X₁ + 1))
    have h2v : 2 ∣ v := by
      have h2v2 : 2 ∣ v ^ 2 := ⟨X₁ + 1, hmul⟩
      exact Nat.prime_two.dvd_of_dvd_pow h2v2
    obtain ⟨a, ha⟩ := h2v
    have hX1_eq : X₁ + 1 = 2 * a ^ 2 := by
      rw [ha] at hmul; nlinarith
    have ha2 : 2 ≤ a := by nlinarith [hX1_gt1, hX1_eq]
    have hprod : q_n n * Y₁ ^ 2 = (2 * a) ^ 2 * (a ^ 2 - 1) := by
      have hpell := hfund.2.2.1
      zify [show 1 ≤ a ^ 2 by nlinarith] at hpell hX1_eq ⊢; nlinarith
    have h2a_dvd_Y1 : 2 * a ∣ Y₁ :=
      dvd_of_sq_dvd_sqfree_mul_sq (q_n_squarefree n) hq_pos.ne' hfund.2.1.ne' (by omega)
        ⟨a ^ 2 - 1, hprod⟩
    obtain ⟨b, hb⟩ := h2a_dvd_Y1
    have hb_pos : 0 < b := by
      by_contra hb0; push_neg at hb0
      have : Y₁ = 0 := by rw [hb, show b = 0 by omega, mul_zero]
      have hY1_pos := hfund.2.1; omega
    have hb_lt : b < Y₁ := by rw [hb]; nlinarith [ha2, hb_pos]
    have hpell_b : a ^ 2 = q_n n * b ^ 2 + 1 := by
      rw [hb] at hprod
      have hcancel : (2 * a) ^ 2 * (q_n n * b ^ 2) = (2 * a) ^ 2 * (a ^ 2 - 1) := by
        linarith [show q_n n * (2 * a * b) ^ 2 = (2 * a) ^ 2 * (q_n n * b ^ 2) by ring]
      have hqb : q_n n * b ^ 2 = a ^ 2 - 1 := Nat.eq_of_mul_eq_mul_left (by positivity) hcancel
      have ha2_ge1 : 1 ≤ a ^ 2 := by nlinarith
      omega
    have hmin := hfund.2.2.2 a b hb_pos hpell_b
    omega
  have hc_ge2 : 2 ≤ coreNat (2 * (X₁ + 1)) := by have := coreNat_pos (2 * (X₁ + 1)); omega
  set p := (coreNat (2 * (X₁ + 1))).minFac
  have hp_pr : p.Prime := Nat.minFac_prime (by omega)
  have hp_dvd : p ∣ coreNat (2 * (X₁ + 1)) := Nat.minFac_dvd _
  have hp_mem : p ∈ ramPrimes n := coreNat_two_X1_add_one_prime_mem_ramPrimes hfund hp_pr hp_dvd
  intro h0
  have hval := congrFun h0 ⟨p, hp_mem⟩
  simp [yMidVec, hp_dvd] at hval

private lemma legendreIdx_mul {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) :
    legendreIdx p (a * b) = legendreIdx p a + legendreIdx p b := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold legendreIdx chiLegendre
  simp only [hp, ↓reduceDIte]
  rw [legendreSym.mul]
  have ha_ne : (a : ZMod p) ≠ 0 := fun h0 => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h0)
  have hb_ne : (b : ZMod p) ≠ 0 := fun h0 => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h0)
  have ha_val : legendreSym p a = 1 ∨ legendreSym p a = -1 := legendreSym.eq_one_or_neg_one p ha_ne
  have hb_val : legendreSym p b = 1 ∨ legendreSym p b = -1 := legendreSym.eq_one_or_neg_one p hb_ne
  rcases ha_val with ha1 | ha1 <;> rcases hb_val with hb1 | hb1 <;> simp [ha1, hb1] <;> decide

private lemma legendreIdx_one {p : ℕ} (hp : p.Prime) : legendreIdx p 1 = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold legendreIdx chiLegendre
  simp [hp, legendreSym.at_one]

private lemma sum_legendreIdx_eq_prod {p : ℕ} (hp : p.Prime) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ q ≠ p) :
    ∑ q ∈ S, legendreIdx p (q : ℤ) = legendreIdx p ((∏ q ∈ S, q : ℕ) : ℤ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [legendreIdx_one hp]
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.prod_insert has, Nat.cast_mul]
    have ha_pr := (hS a (Finset.mem_insert_self a s)).1
    have ha_ne := (hS a (Finset.mem_insert_self a s)).2
    have ha_nd : ¬ (p : ℤ) ∣ (a : ℤ) := by
      intro hd
      exact ha_ne ((Nat.prime_dvd_prime_iff_eq hp ha_pr).mp (Int.natCast_dvd_natCast.mp hd)).symm
    have hs_nd : ¬ (p : ℤ) ∣ ((∏ q ∈ s, q : ℕ) : ℤ) := by
      intro hd
      have h1 := Int.natCast_dvd_natCast.mp hd
      obtain ⟨q, hqs, hqp⟩ := (hp.prime.dvd_finset_prod_iff (fun x => x)).mp h1
      have hq_info := hS q (Finset.mem_insert_of_mem hqs)
      exact hq_info.2 ((Nat.prime_dvd_prime_iff_eq hp hq_info.1).mp hqp).symm
    rw [legendreIdx_mul hp ha_nd hs_nd, ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))]

private lemma squarefree_eq_prod_ramPrimes {n c : ℕ} (hc_pos : 0 < c) (hc_sqf : Squarefree c)
    (hc_sub : ∀ p : ℕ, p.Prime → p ∣ c → p ∈ ramPrimes n) :
    ∏ p ∈ (ramPrimes n).filter (· ∣ c), p = c := by
  have hset : (ramPrimes n).filter (· ∣ c) = c.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp_ram, hp_dvd⟩
      exact ⟨prime_mem_ramPrimes_prime hp_ram, hp_dvd, hc_pos.ne'⟩
    · rintro ⟨hp_pr, hp_dvd, _⟩
      exact ⟨hc_sub p hp_pr hp_dvd, hp_dvd⟩
  rw [hset]
  exact Nat.prod_primeFactors_of_squarefree hc_sqf

private lemma legendreIdx_zero_of_sq_cong {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    {a : ℤ} {u v : ℕ} (ha : ¬ (p : ℤ) ∣ a) (hv : ¬ p ∣ v)
    (hcong : (p : ℤ) ∣ (u : ℤ) ^ 2 - a * (v : ℤ) ^ 2) :
    legendreIdx p a = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold legendreIdx chiLegendre
  simp only [hp, ↓reduceDIte]
  have hmod : ((u : ZMod p)) ^ 2 = (a : ZMod p) * ((v : ZMod p)) ^ 2 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hcong
    push_cast at h0; exact sub_eq_zero.mp h0
  have hv_ne : (v : ZMod p) ≠ 0 := by
    intro h0; exact hv ((ZMod.natCast_eq_zero_iff v p).mp h0)
  have hsq : IsSquare (a : ZMod p) := by
    refine ⟨(u : ZMod p) * (v : ZMod p)⁻¹, ?_⟩
    field_simp [hv_ne]
    exact hmod.symm
  have ha_ne : (a : ZMod p) ≠ 0 := fun h0 => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h0)
  rw [legendreSym.eq_one_iff p ha_ne |>.mpr hsq]; simp

private lemma eps2_mul {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (((a * b - 1) / 2 : ℕ) : ZMod 2) = (((a - 1) / 2 : ℕ) : ZMod 2) + (((b - 1) / 2 : ℕ) : ZMod 2) := by
  have hmod : ((a * b - 1) / 2) % 2 = (((a - 1) / 2) + ((b - 1) / 2)) % 2 := by
    set qa := a / 4; set ra := a % 4
    set qb := b / 4; set rb := b % 4
    have ha4 : a = 4 * qa + ra := (Nat.div_add_mod a 4).symm
    have hb4 : b = 4 * qb + rb := (Nat.div_add_mod b 4).symm
    have hab : a * b = 4 * (4 * qa * qb + qa * rb + qb * ra) + ra * rb := by rw [ha4, hb4]; ring
    have ha_cases : ra = 1 ∨ ra = 3 := by omega
    have hb_cases : rb = 1 ∨ rb = 3 := by omega
    rcases ha_cases with ha1 | ha1 <;> rcases hb_cases with hb1 | hb1 <;> (rw [ha1, hb1] at hab; omega)
  rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff']
  exact hmod

private lemma omega2_mul {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    ((((a * b) ^ 2 - 1) / 8 : ℕ) : ZMod 2) =
      (((a ^ 2 - 1) / 8 : ℕ) : ZMod 2) + (((b ^ 2 - 1) / 8 : ℕ) : ZMod 2) := by
  have hmod : (((a * b) ^ 2 - 1) / 8) % 2 = (((a ^ 2 - 1) / 8) + ((b ^ 2 - 1) / 8)) % 2 := by
    set qa := a / 8; set ra := a % 8
    set qb := b / 8; set rb := b % 8
    have ha8 : a = 8 * qa + ra := (Nat.div_add_mod a 8).symm
    have hb8 : b = 8 * qb + rb := (Nat.div_add_mod b 8).symm
    have hra : ra = 1 ∨ ra = 3 ∨ ra = 5 ∨ ra = 7 := by omega
    have hrb : rb = 1 ∨ rb = 3 ∨ rb = 5 ∨ rb = 7 := by omega
    have h1 : (a ^ 2 - 1) / 8 % 2 = (ra ^ 2 - 1) / 8 % 2 := by
      have : a ^ 2 = 16 * (4 * qa ^ 2 + qa * ra) + ra ^ 2 := by rw [ha8]; ring
      have : 1 ≤ ra ^ 2 := by rcases hra with h | h | h | h <;> rw [h] <;> norm_num
      omega
    have h2 : (b ^ 2 - 1) / 8 % 2 = (rb ^ 2 - 1) / 8 % 2 := by
      have : b ^ 2 = 16 * (4 * qb ^ 2 + qb * rb) + rb ^ 2 := by rw [hb8]; ring
      have : 1 ≤ rb ^ 2 := by rcases hrb with h | h | h | h <;> rw [h] <;> norm_num
      omega
    have h3 : ((a * b) ^ 2 - 1) / 8 % 2 = ((ra * rb) ^ 2 - 1) / 8 % 2 := by
      have hab : a * b = 8 * (8 * qa * qb + qa * rb + qb * ra) + ra * rb := by rw [ha8, hb8]; ring
      set qab := 8 * qa * qb + qa * rb + qb * ra
      have : (a * b) ^ 2 = 16 * (4 * qab ^ 2 + qab * (ra * rb)) + (ra * rb) ^ 2 := by rw [hab]; ring
      have : 1 ≤ (ra * rb) ^ 2 := by
        rcases hra with ha1 | ha1 | ha1 | ha1 <;> rcases hrb with hb1 | hb1 | hb1 | hb1 <;> rw [ha1, hb1] <;> norm_num
      omega
    rw [h3, Nat.add_mod, h1, h2, ← Nat.add_mod]
    rcases hra with ha1 | ha1 | ha1 | ha1 <;> rcases hrb with hb1 | hb1 | hb1 | hb1 <;> rw [ha1, hb1] <;> norm_num
  rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff']
  exact hmod

private def sqMod16 : Fin 4 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 9

private lemma hilbert2_mod16_check :
    ∀ (eq ec : Fin 2) (qo_i co_i : Fin 8) (ai bi di : Fin 4),
      (sqMod16 ai % 2 = 1 ∨ sqMod16 bi % 2 = 1 ∨ sqMod16 di % 2 = 1) →
      let qo := 2 * qo_i.1 + 1
      let co := 2 * co_i.1 + 1
      let q := (2 ^ eq.1) * qo
      let c := (2 ^ ec.1) * co
      sqMod16 ai % 16 = (q * sqMod16 bi + c * sqMod16 di) % 16 →
      (((co - 1) / 2) * ((qo - 1) / 2) + eq.1 * ((co ^ 2 - 1) / 8) + ec.1 * ((qo ^ 2 - 1) / 8)) % 2 = 0 := by
  decide

private lemma sq_mod16_eq_sqMod16 (x : ℕ) :
    ∃ i : Fin 4, x ^ 2 % 16 = sqMod16 i ∧ (x % 2 = 1 ↔ sqMod16 i % 2 = 1) := by
  set q := x / 8
  set r := x % 8
  have hx : x = 8 * q + r := (Nat.div_add_mod x 8).symm
  have hsq : x ^ 2 % 16 = r ^ 2 % 16 := by
    have : x ^ 2 = 16 * (4 * q ^ 2 + q * r) + r ^ 2 := by rw [hx]; ring
    omega
  have hr : r < 8 := Nat.mod_lt x (by norm_num)
  interval_cases h : r
  · exact ⟨0, by rw [hsq]; decide, by show x % 2 = 1 ↔ 0 % 2 = 1; omega⟩
  · exact ⟨1, by rw [hsq]; decide, by show x % 2 = 1 ↔ 1 % 2 = 1; omega⟩
  · exact ⟨2, by rw [hsq]; decide, by show x % 2 = 1 ↔ 4 % 2 = 1; omega⟩
  · exact ⟨3, by rw [hsq]; decide, by show x % 2 = 1 ↔ 9 % 2 = 1; omega⟩
  · exact ⟨0, by rw [hsq]; decide, by show x % 2 = 1 ↔ 0 % 2 = 1; omega⟩
  · exact ⟨3, by rw [hsq]; decide, by show x % 2 = 1 ↔ 9 % 2 = 1; omega⟩
  · exact ⟨2, by rw [hsq]; decide, by show x % 2 = 1 ↔ 4 % 2 = 1; omega⟩
  · exact ⟨1, by rw [hsq]; decide, by show x % 2 = 1 ↔ 1 % 2 = 1; omega⟩

/-- **Membership of the Midpoint Vector in `redeiKernel n`** (pure kernel proof, zero external axioms):
For every `n ≥ 8` and fundamental Pell solution `(X₁, Y₁)` of `q_n`, the midpoint vector
`yMidVec n X₁` satisfies every odd-prime row `redeiRowOdd n p` AND (when `q_n % 4 ≠ 1`) the
2-adic Hilbert row `redeiRowTwo n`, hence `yMidVec n X₁ ∈ redeiKernel n`. -/
theorem yMidVec_mem_redeiKernel {n X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁) :
    yMidVec n X₁ ∈ redeiKernel n := by
  set c := coreNat (2 * (X₁ + 1))
  set v := sqPartNat (2 * (X₁ + 1))
  have hc_pos : 0 < c := coreNat_pos _
  have hv_pos : 0 < v := sqPartNat_pos _
  have hq_pos : 0 < q_n n := q_n_pos_53 n
  have hY1_pos : 0 < Y₁ := hfund.2.1
  have hnorm : (X₁ + 1) ^ 2 = q_n n * Y₁ ^ 2 + c * v ^ 2 := by
    have hpell := hfund.2.2.1
    have hcv := coreNat_mul_sqPartNat_sq (m := 2 * (X₁ + 1)) (by omega)
    nlinarith
  have hc_prod : ∏ p' ∈ (ramPrimes n).filter (· ∣ c), p' = c :=
    squarefree_eq_prod_ramPrimes hc_pos (coreNat_squarefree _)
      (fun p hp hd => coreNat_two_X1_add_one_prime_mem_ramPrimes hfund hp hd)
  refine ⟨?_, ?_⟩
  · -- Odd prime rows: (c, q_n)_p = +1
    intro p hp_ram hp3
    have hp_pr : p.Prime := prime_mem_ramPrimes_prime hp_ram
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have hp_podd : p ∈ Podd n := by
      unfold ramPrimes at hp_ram
      split_ifs at hp_ram with hq1
      · exact hp_ram
      · exact (Finset.mem_insert.mp hp_ram).resolve_left (by omega)
    have hp_dvd_q : p ∣ q_n n := (prime_dvd_q_n_iff_mem_Podd hp_pr).mpr hp_podd
    have hvp_q : padicValNat p (q_n n) = 1 := by
      have h1 := one_le_padicValNat_of_dvd hq_pos.ne' hp_dvd_q
      have h2 : padicValNat p (q_n n) ≤ 1 := by
        by_contra hgt; push_neg at hgt
        have hp2 : p ^ 2 ∣ q_n n := dvd_trans (pow_dvd_pow p (by omega : 2 ≤ padicValNat p (q_n n))) pow_padicValNat_dvd
        exact hp_pr.ne_one (Nat.isUnit_iff.mp ((q_n_squarefree n) p (by simpa [sq] using hp2)))
      omega
    -- Rewrite redeiRowOdd as sum over S_c = (ramPrimes n).filter (· ∣ c)
    unfold redeiRowOdd yMidVec
    rw [Finset.sum_coe_sort (ramPrimes n) (fun x =>
      if x = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) * (if x ∣ c then 1 else 0)
      else legendreIdx p (x : ℤ) * (if x ∣ c then 1 else 0))]
    have hsum_eq : (∑ x ∈ ramPrimes n,
        (if x = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) * (if x ∣ c then 1 else 0)
         else legendreIdx p (x : ℤ) * (if x ∣ c then 1 else 0))) =
        ∑ p' ∈ (ramPrimes n).filter (· ∣ c),
          if p' = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) else legendreIdx p (p' : ℤ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp
    rw [hsum_eq]
    by_cases hpc : p ∣ c
    · -- Case p ∣ c: split off p from S_c
      have hp_Sc : p ∈ (ramPrimes n).filter (· ∣ c) := Finset.mem_filter.mpr ⟨hp_ram, hpc⟩
      rw [← Finset.add_sum_erase _ _ hp_Sc, if_pos rfl]
      have hrest : ∑ x ∈ ((ramPrimes n).filter (· ∣ c)).erase p,
          (if x = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) else legendreIdx p (x : ℤ)) =
          legendreIdx p ((c / p : ℕ) : ℤ) := by
        have h1 : ∑ x ∈ ((ramPrimes n).filter (· ∣ c)).erase p,
            (if x = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) else legendreIdx p (x : ℤ)) =
            ∑ x ∈ ((ramPrimes n).filter (· ∣ c)).erase p, legendreIdx p (x : ℤ) :=
          Finset.sum_congr rfl fun x hx => if_neg (Finset.ne_of_mem_erase hx)
        rw [h1, sum_legendreIdx_eq_prod hp_pr _ (fun q hq =>
          ⟨prime_mem_ramPrimes_prime (Finset.mem_filter.mp (Finset.mem_of_mem_erase hq)).1,
           Finset.ne_of_mem_erase hq⟩)]
        congr 2
        have hpm := Finset.mul_prod_erase ((ramPrimes n).filter (· ∣ c)) (fun x => x) hp_Sc
        rw [hc_prod] at hpm
        exact Nat.eq_div_of_mul_eq_right hp_pr.ne_zero hpm
      rw [hrest]
      have hnd_q' : ¬ p ∣ q_n n / p := by
        intro hd
        have hp2 : p ^ 2 ∣ q_n n := by
          rw [sq]; exact (Nat.dvd_div_iff_mul_dvd hp_dvd_q).mp hd
        exact hp_pr.ne_one (Nat.isUnit_iff.mp ((q_n_squarefree n) p (by simpa [sq] using hp2)))
      have hnd_c' : ¬ p ∣ c / p := by
        intro hd
        have hp2 : p ^ 2 ∣ c := by
          rw [sq]; exact (Nat.dvd_div_iff_mul_dvd hpc).mp hd
        exact hp_pr.ne_one (Nat.isUnit_iff.mp ((coreNat_squarefree _) p (by simpa [sq] using hp2)))
      rw [← legendreIdx_mul hp_pr (by intro h; exact hnd_q' (Int.natCast_dvd_natCast.mp (dvd_neg.mp h)))
            (by intro h; exact hnd_c' (Int.natCast_dvd_natCast.mp h))]
      -- From (X₁+1)^2 = q_n * Y₁^2 + c * v^2, p ∣ X₁+1, divide by p:
      have hp_X1p1 : p ∣ X₁ + 1 := hp_pr.dvd_of_dvd_pow (by
        rw [hnorm]; exact dvd_add (dvd_mul_of_dvd_left hp_dvd_q _) (dvd_mul_of_dvd_left hpc _))
      obtain ⟨A₁, hA₁⟩ := hp_X1p1
      have hdiv_p : p * A₁ ^ 2 = (q_n n / p) * Y₁ ^ 2 + (c / p) * v ^ 2 := by
        have h1 : p * (p * A₁ ^ 2) = p * ((q_n n / p) * Y₁ ^ 2 + (c / p) * v ^ 2) := by
          calc p * (p * A₁ ^ 2) = (p * A₁) ^ 2 := by ring
            _ = (X₁ + 1) ^ 2 := by rw [← hA₁]
            _ = q_n n * Y₁ ^ 2 + c * v ^ 2 := hnorm
            _ = (p * (q_n n / p)) * Y₁ ^ 2 + (p * (c / p)) * v ^ 2 := by
                rw [Nat.mul_div_cancel' hp_dvd_q, Nat.mul_div_cancel' hpc]
            _ = p * ((q_n n / p) * Y₁ ^ 2 + (c / p) * v ^ 2) := by ring
        exact Nat.eq_of_mul_eq_mul_left hp_pr.pos h1
      -- Divide Y₁, v by p ^ min(v_p(Y₁), v_p(v))
      set k := min (padicValNat p Y₁) (padicValNat p v)
      have hpk_Y : p ^ k ∣ Y₁ := dvd_trans (pow_dvd_pow p (min_le_left _ _)) pow_padicValNat_dvd
      have hpk_v : p ^ k ∣ v := dvd_trans (pow_dvd_pow p (min_le_right _ _)) pow_padicValNat_dvd
      obtain ⟨B', hB'⟩ := hpk_Y
      obtain ⟨C', hC'⟩ := hpk_v
      have hpk2_dvd : p ^ (2 * k) ∣ p * A₁ ^ 2 := by
        rw [hdiv_p, hB', hC', show 2 * k = k + k by omega, pow_add]
        refine dvd_add ?_ ?_
        · exact ⟨(q_n n / p) * B' ^ 2, by ring⟩
        · exact ⟨(c / p) * C' ^ 2, by ring⟩
      have hpk2_A1 : p ^ k ∣ A₁ := by
        have hA1_pos : A₁ ≠ 0 := by intro h0; rw [h0, mul_zero] at hA₁; omega
        have hv1 := (Nat.factorization_le_iff_dvd (pow_ne_zero (2 * k) hp_pr.ne_zero)
          (mul_ne_zero hp_pr.ne_zero (pow_ne_zero 2 hA1_pos))).mpr hpk2_dvd p
        simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
          Nat.factorization_mul hp_pr.ne_zero (pow_ne_zero 2 hA1_pos), Finsupp.add_apply,
          hp_pr.factorization_self] at hv1
        have hle_k : k ≤ padicValNat p A₁ := by rw [← Nat.factorization_def _ hp_pr]; omega
        exact dvd_trans (pow_dvd_pow p hle_k) pow_padicValNat_dvd
      obtain ⟨A', hA'⟩ := hpk2_A1
      have hred : p * A' ^ 2 = (q_n n / p) * B' ^ 2 + (c / p) * C' ^ 2 := by
        have h1 : (p ^ k) ^ 2 * (p * A' ^ 2) = (p ^ k) ^ 2 * ((q_n n / p) * B' ^ 2 + (c / p) * C' ^ 2) := by
          calc (p ^ k) ^ 2 * (p * A' ^ 2) = p * (p ^ k * A') ^ 2 := by ring
            _ = p * A₁ ^ 2 := by rw [← hA']
            _ = (q_n n / p) * (p ^ k * B') ^ 2 + (c / p) * (p ^ k * C') ^ 2 := by rw [← hB', ← hC', hdiv_p]
            _ = (p ^ k) ^ 2 * ((q_n n / p) * B' ^ 2 + (c / p) * C' ^ 2) := by ring
        exact Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos hp_pr.pos k) 2) h1
      have hnot_both : ¬ (p ∣ B' ∧ p ∣ C') := by
        rintro ⟨h1, h2⟩
        have hvY : k + 1 ≤ padicValNat p Y₁ := by
          rw [hB', padicValNat.mul (pow_ne_zero k hp_pr.ne_zero) (by intro h0; rw [h0, mul_zero] at hB'; exact hY1_pos.ne' hB'),
            padicValNat.prime_pow k]
          have := one_le_padicValNat_of_dvd (by intro h0; rw [h0, mul_zero] at hB'; exact hY1_pos.ne' hB') h1
          omega
        have hvv : k + 1 ≤ padicValNat p v := by
          rw [hC', padicValNat.mul (pow_ne_zero k hp_pr.ne_zero) (by intro h0; rw [h0, mul_zero] at hC'; exact hv_pos.ne' hC'),
            padicValNat.prime_pow k]
          have := one_le_padicValNat_of_dvd (by intro h0; rw [h0, mul_zero] at hC'; exact hv_pos.ne' hC') h2
          omega
        omega
      have hp_nd_C' : ¬ p ∣ C' := by
        intro hC_dvd
        have hB_dvd : p ∣ B' := by
          have h1 : p ∣ (q_n n / p) * B' ^ 2 := by
            have : (q_n n / p) * B' ^ 2 + (c / p) * C' ^ 2 = p * A' ^ 2 := hred.symm
            exact (Nat.dvd_add_left (dvd_mul_of_dvd_right (dvd_pow hC_dvd (by norm_num)) _)).mp
              (this ▸ dvd_mul_right p _)
          exact hp_pr.dvd_of_dvd_pow ((hp_pr.dvd_mul.mp h1).resolve_left hnd_q')
        exact hnot_both ⟨hB_dvd, hC_dvd⟩
      have hcong : (p : ℤ) ∣ (((q_n n / p) * B' : ℕ) : ℤ) ^ 2 -
          (-(q_n n / p : ℕ) : ℤ) * (c / p : ℕ) * (C' : ℤ) ^ 2 := by
        refine ⟨(q_n n / p : ℕ) * (A' : ℤ) ^ 2, ?_⟩
        have hred_z : (p : ℤ) * (A' : ℤ) ^ 2 = ((q_n n / p : ℕ) : ℤ) * (B' : ℤ) ^ 2 + ((c / p : ℕ) : ℤ) * (C' : ℤ) ^ 2 := by
          exact_mod_cast hred
        rw [Nat.cast_mul]
        linear_combination -((q_n n / p : ℕ) : ℤ) * hred_z
      exact legendreIdx_zero_of_sq_cong hp_pr hp3 (by
        intro h; rcases Int.Prime.dvd_mul' hp_pr h with h1 | h2
        · exact hnd_q' (Int.natCast_dvd_natCast.mp (dvd_neg.mp h1))
        · exact hnd_c' (Int.natCast_dvd_natCast.mp h2)) hp_nd_C' hcong
    · -- Case ¬ p ∣ c
      have h1 : ∑ x ∈ (ramPrimes n).filter (· ∣ c),
          (if x = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) else legendreIdx p (x : ℤ)) =
          ∑ x ∈ (ramPrimes n).filter (· ∣ c), legendreIdx p (x : ℤ) :=
        Finset.sum_congr rfl fun x hx => if_neg (fun heq => by subst heq; exact hpc (Finset.mem_filter.mp hx).2)
      rw [h1, sum_legendreIdx_eq_prod hp_pr _ (fun q hq =>
        ⟨prime_mem_ramPrimes_prime (Finset.mem_filter.mp hq).1,
         fun heq => by subst heq; exact hpc (Finset.mem_filter.mp hq).2⟩), hc_prod]
      -- Divide X₁+1, v by p ^ min(v_p(X₁+1), v_p(v))
      set k := min (padicValNat p (X₁ + 1)) (padicValNat p v)
      have hpk_A : p ^ k ∣ X₁ + 1 := dvd_trans (pow_dvd_pow p (min_le_left _ _)) pow_padicValNat_dvd
      have hpk_v : p ^ k ∣ v := dvd_trans (pow_dvd_pow p (min_le_right _ _)) pow_padicValNat_dvd
      obtain ⟨A', hA'⟩ := hpk_A
      obtain ⟨C', hC'⟩ := hpk_v
      have hpk2_dvd : p ^ (2 * k) ∣ q_n n * Y₁ ^ 2 := by
        have hsub : (X₁ + 1) ^ 2 - c * v ^ 2 = q_n n * Y₁ ^ 2 := by omega
        rw [← hsub, hA', hC', show 2 * k = k + k by omega, pow_add]
        have h1 : p ^ k * p ^ k ∣ (p ^ k * A') ^ 2 := ⟨A' ^ 2, by ring⟩
        have h2 : p ^ k * p ^ k ∣ c * (p ^ k * C') ^ 2 := ⟨c * C' ^ 2, by ring⟩
        exact Nat.dvd_sub h1 h2
      have hpk_Y : p ^ k ∣ Y₁ :=
        dvd_of_sq_dvd_sqfree_mul_sq (q_n_squarefree n) hq_pos.ne' hY1_pos.ne' (pow_ne_zero k hp_pr.ne_zero)
          (by simpa [pow_mul, mul_comm 2 k] using hpk2_dvd)
      obtain ⟨B', hB'⟩ := hpk_Y
      have hred : A' ^ 2 = q_n n * B' ^ 2 + c * C' ^ 2 := by
        have h1 : (p ^ k) ^ 2 * A' ^ 2 = (p ^ k) ^ 2 * (q_n n * B' ^ 2 + c * C' ^ 2) := by
          calc (p ^ k) ^ 2 * A' ^ 2 = (p ^ k * A') ^ 2 := by ring
            _ = (X₁ + 1) ^ 2 := by rw [← hA']
            _ = q_n n * (p ^ k * B') ^ 2 + c * (p ^ k * C') ^ 2 := by rw [← hB', ← hC', hnorm]
            _ = (p ^ k) ^ 2 * (q_n n * B' ^ 2 + c * C' ^ 2) := by ring
        exact Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos hp_pr.pos k) 2) h1
      have hnot_both : ¬ (p ∣ A' ∧ p ∣ C') := by
        rintro ⟨h1, h2⟩
        have hvA : k + 1 ≤ padicValNat p (X₁ + 1) := by
          rw [hA', padicValNat.mul (pow_ne_zero k hp_pr.ne_zero) (by intro h0; rw [h0, mul_zero] at hA'; omega),
            padicValNat.prime_pow k]
          have := one_le_padicValNat_of_dvd (by intro h0; rw [h0, mul_zero] at hA'; omega) h1
          omega
        have hvv : k + 1 ≤ padicValNat p v := by
          rw [hC', padicValNat.mul (pow_ne_zero k hp_pr.ne_zero) (by intro h0; rw [h0, mul_zero] at hC'; exact hv_pos.ne' hC'),
            padicValNat.prime_pow k]
          have := one_le_padicValNat_of_dvd (by intro h0; rw [h0, mul_zero] at hC'; exact hv_pos.ne' hC') h2
          omega
        omega
      have hp_nd_C' : ¬ p ∣ C' := by
        intro hC_dvd
        have hA_dvd : p ∣ A' := hp_pr.dvd_of_dvd_pow (by
          rw [hred]; exact dvd_add (dvd_mul_of_dvd_left hp_dvd_q _) (dvd_mul_of_dvd_right (dvd_pow hC_dvd (by norm_num)) _))
        exact hnot_both ⟨hA_dvd, hC_dvd⟩
      have hcong : (p : ℤ) ∣ (A' : ℤ) ^ 2 - (c : ℤ) * (C' : ℤ) ^ 2 := by
        have hred_z : (A' : ℤ) ^ 2 - (c : ℤ) * (C' : ℤ) ^ 2 = (q_n n : ℤ) * (B' : ℤ) ^ 2 := by
          have : (A' : ℤ) ^ 2 = (q_n n : ℤ) * (B' : ℤ) ^ 2 + (c : ℤ) * (C' : ℤ) ^ 2 := by exact_mod_cast hred
          linarith
        rw [hred_z]
        exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hp_dvd_q) _
      exact legendreIdx_zero_of_sq_cong hp_pr hp3 (fun h => hpc (Int.natCast_dvd_natCast.mp h)) hp_nd_C' hcong
  · -- 2-adic Hilbert row when q_n % 4 ≠ 1
    intro hq_ne1
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    unfold redeiRowTwo yMidVec
    set v2q := padicValNat 2 (q_n n)
    set qodd := oddPartNat (q_n n)
    set v2c := padicValNat 2 c
    set codd := oddPartNat c
    have hv2q_le1 : v2q ≤ 1 := by
      by_contra hgt; push_neg at hgt
      have h4 : 2 ^ 2 ∣ q_n n := dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ v2q)) pow_padicValNat_dvd
      exact Nat.prime_two.ne_one (Nat.isUnit_iff.mp ((q_n_squarefree n) 2 (by simpa [sq] using h4)))
    have hv2c_le1 : v2c ≤ 1 := by
      by_contra hgt; push_neg at hgt
      have h4 : 2 ^ 2 ∣ c := dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ v2c)) pow_padicValNat_dvd
      exact Nat.prime_two.ne_one (Nat.isUnit_iff.mp ((coreNat_squarefree _) 2 (by simpa [sq] using h4)))
    have hqodd_odd : qodd % 2 = 1 := by
      have := oddPartNat_not_dvd_two hq_pos; omega
    have hcodd_odd : codd % 2 = 1 := by
      have := oddPartNat_not_dvd_two hc_pos; omega
    -- Compute redeiRowTwo in terms of (v2c, codd, v2q, qodd)
    dsimp only
    rw [Finset.sum_coe_sort (ramPrimes n) (fun x =>
      (if x = 2 then (((qodd ^ 2 - 1) / 8 : ℕ) : ZMod 2)
       else ((((x - 1) / 2) * ((qodd - 1) / 2) + v2q * ((x ^ 2 - 1) / 8) : ℕ) : ZMod 2)) *
      (if x ∣ c then 1 else 0))]
    have hsum_flt : (∑ x ∈ ramPrimes n,
        (if x = 2 then (((qodd ^ 2 - 1) / 8 : ℕ) : ZMod 2)
         else ((((x - 1) / 2) * ((qodd - 1) / 2) + v2q * ((x ^ 2 - 1) / 8) : ℕ) : ZMod 2)) *
        (if x ∣ c then 1 else 0)) =
        ∑ p' ∈ (ramPrimes n).filter (· ∣ c),
          if p' = 2 then (((qodd ^ 2 - 1) / 8 : ℕ) : ZMod 2)
          else ((((p' - 1) / 2) * ((qodd - 1) / 2) + v2q * ((p' ^ 2 - 1) / 8) : ℕ) : ZMod 2) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> simp
    rw [hsum_flt]
    set S_odd := ((ramPrimes n).filter (· ∣ c)).erase 2
    have hSodd_odd : ∀ p' ∈ S_odd, p' % 2 = 1 := by
      intro p' hp'
      have hpr := prime_mem_ramPrimes_prime (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp')).1
      have hne2 := Finset.ne_of_mem_erase hp'
      exact Nat.Prime.eq_two_or_odd hpr |>.resolve_left hne2
    have hSodd_prod : ∏ p' ∈ S_odd, p' = codd := by
      have hmul_c := oddPartNat_mul_two_pow hc_pos
      by_cases h2c : 2 ∣ c
      · have hv2c_eq1 : v2c = 1 := by
          have := one_le_padicValNat_of_dvd hc_pos.ne' h2c; omega
        have h2mem : 2 ∈ (ramPrimes n).filter (· ∣ c) :=
          Finset.mem_filter.mpr ⟨by unfold ramPrimes; rw [if_neg hq_ne1]; exact Finset.mem_insert_self 2 _, h2c⟩
        have h1 := Finset.mul_prod_erase ((ramPrimes n).filter (· ∣ c)) (fun x => x) h2mem
        rw [hc_prod] at h1
        change 2 * ∏ p' ∈ S_odd, p' = c at h1
        change codd * 2 ^ v2c = c at hmul_c
        rw [hv2c_eq1, pow_one] at hmul_c
        omega
      · have hv2c_eq0 : v2c = 0 := padicValNat.eq_zero_of_not_dvd h2c
        have h2nmem : 2 ∉ (ramPrimes n).filter (· ∣ c) := fun h => h2c (Finset.mem_filter.mp h).2
        change codd * 2 ^ v2c = c at hmul_c
        rw [hv2c_eq0, pow_zero, mul_one] at hmul_c
        change ∏ p' ∈ ((ramPrimes n).filter (· ∣ c)).erase 2, p' = codd
        rw [Finset.erase_eq_of_notMem h2nmem, hc_prod, hmul_c]
    have hsum_odd_prod : ∀ T : Finset ℕ, (∀ p' ∈ T, p' % 2 = 1) →
        (∑ p' ∈ T, (((p' - 1) / 2 : ℕ) : ZMod 2)) = ((((∏ p' ∈ T, p') - 1) / 2 : ℕ) : ZMod 2) ∧
        (∑ p' ∈ T, (((p' ^ 2 - 1) / 8 : ℕ) : ZMod 2)) = ((((∏ p' ∈ T, p') ^ 2 - 1) / 8 : ℕ) : ZMod 2) := by
      intro T
      classical
      induction T using Finset.induction_on with
      | empty => intro _; simp
      | @insert a s has ih =>
        intro hT
        have ha_odd := hT a (Finset.mem_insert_self a s)
        have hs_odd : (∏ p' ∈ s, p') % 2 = 1 := by
          have hprod_odd : ∀ U : Finset ℕ, (∀ x ∈ U, x % 2 = 1) → (∏ x ∈ U, x) % 2 = 1 := by
            intro U
            induction U using Finset.induction_on with
            | empty => intro _; simp
            | @insert b t hbt iht =>
              intro hU
              rw [Finset.prod_insert hbt, Nat.mul_mod, hU b (Finset.mem_insert_self b t),
                iht (fun x hx => hU x (Finset.mem_insert_of_mem hx))]
          exact hprod_odd s (fun x hx => hT x (Finset.mem_insert_of_mem hx))
        have ih' := ih (fun x hx => hT x (Finset.mem_insert_of_mem hx))
        rw [Finset.sum_insert has, Finset.sum_insert has, Finset.prod_insert has]
        exact ⟨by rw [ih'.1, eps2_mul ha_odd hs_odd], by rw [ih'.2, omega2_mul ha_odd hs_odd]⟩
    have hsum_val : (∑ p' ∈ (ramPrimes n).filter (· ∣ c),
        if p' = 2 then (((qodd ^ 2 - 1) / 8 : ℕ) : ZMod 2)
        else ((((p' - 1) / 2) * ((qodd - 1) / 2) + v2q * ((p' ^ 2 - 1) / 8) : ℕ) : ZMod 2)) =
        ((((codd - 1) / 2) * ((qodd - 1) / 2) + v2q * ((codd ^ 2 - 1) / 8) +
          v2c * ((qodd ^ 2 - 1) / 8) : ℕ) : ZMod 2) := by
      have hodd_part : ∑ p' ∈ S_odd,
          (if p' = 2 then (((qodd ^ 2 - 1) / 8 : ℕ) : ZMod 2)
           else ((((p' - 1) / 2) * ((qodd - 1) / 2) + v2q * ((p' ^ 2 - 1) / 8) : ℕ) : ZMod 2)) =
          ((((codd - 1) / 2) * ((qodd - 1) / 2) + v2q * ((codd ^ 2 - 1) / 8) : ℕ) : ZMod 2) := by
        have h1 : ∑ p' ∈ S_odd,
            (if p' = 2 then (((qodd ^ 2 - 1) / 8 : ℕ) : ZMod 2)
             else ((((p' - 1) / 2) * ((qodd - 1) / 2) + v2q * ((p' ^ 2 - 1) / 8) : ℕ) : ZMod 2)) =
            (∑ p' ∈ S_odd, (((p' - 1) / 2 : ℕ) : ZMod 2)) * (((qodd - 1) / 2 : ℕ) : ZMod 2) +
            (v2q : ZMod 2) * (∑ p' ∈ S_odd, (((p' ^ 2 - 1) / 8 : ℕ) : ZMod 2)) := by
          rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p' hp' => ?_
          rw [if_neg (Finset.ne_of_mem_erase hp')]; push_cast; ring
        rw [h1, (hsum_odd_prod S_odd hSodd_odd).1, (hsum_odd_prod S_odd hSodd_odd).2, hSodd_prod]
        push_cast; ring
      by_cases h2c : 2 ∣ c
      · have hv2c_eq1 : v2c = 1 := by
          have := one_le_padicValNat_of_dvd hc_pos.ne' h2c; omega
        have h2mem : 2 ∈ (ramPrimes n).filter (· ∣ c) :=
          Finset.mem_filter.mpr ⟨by unfold ramPrimes; rw [if_neg hq_ne1]; exact Finset.mem_insert_self 2 _, h2c⟩
        rw [← Finset.add_sum_erase _ _ h2mem, if_pos rfl]
        change (((qodd ^ 2 - 1) / 8 : ℕ) : ZMod 2) + ∑ p' ∈ S_odd, _ = _
        rw [hodd_part, hv2c_eq1]; push_cast; ring
      · have hv2c_eq0 : v2c = 0 := padicValNat.eq_zero_of_not_dvd h2c
        have h2nmem : 2 ∉ (ramPrimes n).filter (· ∣ c) := fun h => h2c (Finset.mem_filter.mp h).2
        have heq_S : (ramPrimes n).filter (· ∣ c) = S_odd := (Finset.erase_eq_of_notMem h2nmem).symm
        rw [heq_S, hodd_part, hv2c_eq0]; push_cast; ring
    rw [hsum_val]
    -- Reduce (X₁ + 1)^2 = q_n * Y₁^2 + c * v^2 by 2^k where k = min(v_2(X₁+1), v_2(Y₁), v_2(v))
    set k := min (padicValNat 2 (X₁ + 1)) (min (padicValNat 2 Y₁) (padicValNat 2 v))
    have h2k_A : 2 ^ k ∣ X₁ + 1 := dvd_trans (pow_dvd_pow 2 (min_le_left _ _)) pow_padicValNat_dvd
    have h2k_B : 2 ^ k ∣ Y₁ := dvd_trans (pow_dvd_pow 2 (le_trans (min_le_right _ _) (min_le_left _ _))) pow_padicValNat_dvd
    have h2k_C : 2 ^ k ∣ v := dvd_trans (pow_dvd_pow 2 (le_trans (min_le_right _ _) (min_le_right _ _))) pow_padicValNat_dvd
    obtain ⟨A', hA'⟩ := h2k_A
    obtain ⟨B', hB'⟩ := h2k_B
    obtain ⟨C', hC'⟩ := h2k_C
    have hred : A' ^ 2 = q_n n * B' ^ 2 + c * C' ^ 2 := by
      have h1 : (2 ^ k) ^ 2 * A' ^ 2 = (2 ^ k) ^ 2 * (q_n n * B' ^ 2 + c * C' ^ 2) := by
        calc (2 ^ k) ^ 2 * A' ^ 2 = (2 ^ k * A') ^ 2 := by ring
          _ = (X₁ + 1) ^ 2 := by rw [← hA']
          _ = q_n n * (2 ^ k * B') ^ 2 + c * (2 ^ k * C') ^ 2 := by rw [← hB', ← hC', hnorm]
          _ = (2 ^ k) ^ 2 * (q_n n * B' ^ 2 + c * C' ^ 2) := by ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos (by norm_num) k) 2) h1
    have hone_odd : A' % 2 = 1 ∨ B' % 2 = 1 ∨ C' % 2 = 1 := by
      by_contra hnone; push_neg at hnone
      have hA_ev : 2 ∣ A' := by omega
      have hB_ev : 2 ∣ B' := by omega
      have hC_ev : 2 ∣ C' := by omega
      have hvA : k + 1 ≤ padicValNat 2 (X₁ + 1) := by
        rw [hA', padicValNat.mul (pow_ne_zero k (by norm_num)) (by intro h0; rw [h0, mul_zero] at hA'; omega),
          padicValNat.prime_pow k]
        have := one_le_padicValNat_of_dvd (by intro h0; rw [h0, mul_zero] at hA'; omega) hA_ev; omega
      have hvB : k + 1 ≤ padicValNat 2 Y₁ := by
        rw [hB', padicValNat.mul (pow_ne_zero k (by norm_num)) (by intro h0; rw [h0, mul_zero] at hB'; exact hY1_pos.ne' hB'),
          padicValNat.prime_pow k]
        have := one_le_padicValNat_of_dvd (by intro h0; rw [h0, mul_zero] at hB'; exact hY1_pos.ne' hB') hB_ev; omega
      have hvC : k + 1 ≤ padicValNat 2 v := by
        rw [hC', padicValNat.mul (pow_ne_zero k (by norm_num)) (by intro h0; rw [h0, mul_zero] at hC'; exact hv_pos.ne' hC'),
          padicValNat.prime_pow k]
        have := one_le_padicValNat_of_dvd (by intro h0; rw [h0, mul_zero] at hC'; exact hv_pos.ne' hC') hC_ev; omega
      omega
    have hq_decomp : q_n n = 2 ^ v2q * qodd := by rw [mul_comm]; exact (oddPartNat_mul_two_pow hq_pos).symm
    have hc_decomp : c = 2 ^ v2c * codd := by rw [mul_comm]; exact (oddPartNat_mul_two_pow hc_pos).symm
    obtain ⟨ai, hai_sq, hai_odd⟩ := sq_mod16_eq_sqMod16 A'
    obtain ⟨bi, hbi_sq, hbi_odd⟩ := sq_mod16_eq_sqMod16 B'
    obtain ⟨di, hdi_sq, hdi_odd⟩ := sq_mod16_eq_sqMod16 C'
    have hqodd_r : 2 * ((qodd % 16) / 2) + 1 = qodd % 16 := by omega
    have hcodd_r : 2 * ((codd % 16) / 2) + 1 = codd % 16 := by omega
    have hmod16 : sqMod16 ai % 16 = ((2 ^ v2q * (2 * ((qodd % 16) / 2) + 1)) * sqMod16 bi +
        (2 ^ v2c * (2 * ((codd % 16) / 2) + 1)) * sqMod16 di) % 16 := by
      have h1 := congrArg (· % 16) hred
      rw [hqodd_r, hcodd_r]
      rw [hai_sq, hq_decomp, hc_decomp] at h1
      rw [Nat.add_mod, Nat.mul_mod (2 ^ v2q * qodd), Nat.mul_mod (2 ^ v2c * codd),
        hbi_sq, hdi_sq, Nat.mul_mod (2 ^ v2q) qodd, Nat.mul_mod (2 ^ v2c) codd] at h1
      have hsq_lt : sqMod16 ai < 16 := by fin_cases ai <;> decide
      rw [Nat.mod_eq_of_lt hsq_lt]
      rw [h1]
      simp [Nat.add_mod, Nat.mul_mod]
    have hodd_sq : sqMod16 ai % 2 = 1 ∨ sqMod16 bi % 2 = 1 ∨ sqMod16 di % 2 = 1 := by
      rcases hone_odd with h | h | h
      · exact Or.inl (hai_odd.mp h)
      · exact Or.inr (Or.inl (hbi_odd.mp h))
      · exact Or.inr (Or.inr (hdi_odd.mp h))
    have hres := hilbert2_mod16_check ⟨v2q, by omega⟩ ⟨v2c, by omega⟩
      ⟨(qodd % 16) / 2, by omega⟩ ⟨(codd % 16) / 2, by omega⟩
      ai bi di hodd_sq hmod16
    have hcong_exp : (((codd - 1) / 2) * ((qodd - 1) / 2) + v2q * ((codd ^ 2 - 1) / 8) +
        v2c * ((qodd ^ 2 - 1) / 8)) % 2 =
        ((((2 * ((codd % 16) / 2) + 1) - 1) / 2) * (((2 * ((qodd % 16) / 2) + 1) - 1) / 2) +
          v2q * (((2 * ((codd % 16) / 2) + 1) ^ 2 - 1) / 8) +
          v2c * (((2 * ((qodd % 16) / 2) + 1) ^ 2 - 1) / 8)) % 2 := by
      set qq := qodd / 16; set rq := qodd % 16
      set qc := codd / 16; set rc := codd % 16
      have hq16 : qodd = 16 * qq + rq := (Nat.div_add_mod qodd 16).symm
      have hc16 : codd = 16 * qc + rc := (Nat.div_add_mod codd 16).symm
      have h1 : (qodd - 1) / 2 % 2 = (rq - 1) / 2 % 2 := by omega
      have h2 : (codd - 1) / 2 % 2 = (rc - 1) / 2 % 2 := by omega
      have h3 : (qodd ^ 2 - 1) / 8 % 2 = (rq ^ 2 - 1) / 8 % 2 := by
        have hq2 : qodd ^ 2 = 16 * (16 * qq ^ 2 + 2 * qq * rq) + rq ^ 2 := by rw [hq16]; ring
        have hrq1 : 1 ≤ rq := by omega
        have hrq2 : 1 ≤ rq ^ 2 := Nat.one_le_pow 2 rq hrq1
        omega
      have h4 : (codd ^ 2 - 1) / 8 % 2 = (rc ^ 2 - 1) / 8 % 2 := by
        have hc2 : codd ^ 2 = 16 * (16 * qc ^ 2 + 2 * qc * rc) + rc ^ 2 := by rw [hc16]; ring
        have hrc1 : 1 ≤ rc := by omega
        have hrc2 : 1 ≤ rc ^ 2 := Nat.one_le_pow 2 rc hrc1
        omega
      rw [hqodd_r, hcodd_r]
      rw [Nat.add_mod ((codd - 1) / 2 * ((qodd - 1) / 2) + v2q * ((codd ^ 2 - 1) / 8)),
        Nat.add_mod ((codd - 1) / 2 * ((qodd - 1) / 2)),
        Nat.mul_mod ((codd - 1) / 2), Nat.mul_mod v2q, Nat.mul_mod v2c,
        h1, h2, h3, h4]
      simp [Nat.add_mod, Nat.mul_mod]
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero (by rw [hcong_exp]; exact hres)

/-- **Theorem 5.3(i) — Galois Cohomology Exact Sequence and Rédei–Reichardt 4-Rank Identity
(eqs. 5.8–5.9)**:
For any `n ≥ 8` and fundamental Pell solution `(X₁, Y₁)` of `q_n` (with **no** unproved
hypotheses on `yMidVec` — both `yMidVec_mem_redeiKernel` and `yMidVec_ne_zero` are proved
directly from the Pell equation), there is an exact sequence of `𝔽₂`-vector spaces
`0 → span_{𝔽₂}{y^{mid}} → ker_{𝔽₂}(R_n^{ram}) → Cl^+(q_n)[2] ∩ 2 Cl^+(q_n) → 0`,
and consequently `dim_{𝔽₂} ker_{𝔽₂}(R_n^{ram}) = 1 + rank₄ Cl^+(q_n)`. -/
theorem thm_5_3_part1_cohomology_4rank {n X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁) :
    let yMid : redeiKernel n := ⟨yMidVec n X₁, yMidVec_mem_redeiKernel hn hfund⟩
    ∃ psiPlus : redeiKernel n →ₗ[ZMod 2] (canonicalRealQuadRedei n).Cl4Rank,
      Function.Surjective psiPlus ∧
      LinearMap.ker psiPlus = Submodule.span (ZMod 2) {yMid} ∧
      Module.finrank (ZMod 2) (redeiKernel n) = 1 + (canonicalRealQuadRedei n).rank4 := by
  dsimp only
  have hyMid_mem := yMidVec_mem_redeiKernel hn hfund
  have hyMid_ne := yMidVec_ne_zero hn hfund
  set yMid : redeiKernel n := ⟨yMidVec n X₁, hyMid_mem⟩
  have hyMid_sub_ne : yMid ≠ 0 := by
    intro h0
    apply hyMid_ne
    exact congrArg Subtype.val h0
  obtain ⟨psiPlus, hsurj, hker⟩ := redei_reichardt_exact_sequence n X₁ Y₁ hn hfund hyMid_mem hyMid_ne
  have h_finrank_eq : Module.finrank (ZMod 2) (LinearMap.range psiPlus) +
      Module.finrank (ZMod 2) (LinearMap.ker psiPlus) =
      Module.finrank (ZMod 2) (redeiKernel n) :=
    LinearMap.finrank_range_add_finrank_ker psiPlus
  have h_range : Module.finrank (ZMod 2) (LinearMap.range psiPlus) = (canonicalRealQuadRedei n).rank4 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, (canonicalRealQuadRedei n).h_rank4]
  have h_ker : Module.finrank (ZMod 2) (LinearMap.ker psiPlus) = 1 := by
    rw [hker, finrank_span_singleton hyMid_sub_ne]
  refine ⟨psiPlus, hsurj, hker, ?_⟩
  omega

/-! ### Theorem 5.3(ii): Deterministic `𝒫_even^-(n)`-Absorption and Reduced Dual Quartic Laws -/

/-- Split-even primes `𝒫_even^+(n) = {q ∈ 𝒫_even(n) \ {2} : (-q_n / q) = +1}`. -/
def PevenPlus (n : ℕ) : Finset ℕ :=
  (Peven n).filter (fun q => 3 ≤ q ∧ chiLegendre (-(q_n n : ℤ)) q = 1)

/-- Inert-even primes `𝒫_even^-(n) = {q ∈ 𝒫_even(n) \ {2} : (-q_n / q) = -1}`. -/
def PevenMinus (n : ℕ) : Finset ℕ :=
  (Peven n).filter (fun q => 3 ≤ q ∧ chiLegendre (-(q_n n : ℤ)) q = -1)

/-- Split-even square-root factor `W_i = ∏_{q ∈ 𝒫_even^+(n), q ∣ z_i} q^{v_q(n!)/2}`. -/
def W_split (n z : ℕ) : ℕ :=
  ∏ q ∈ (PevenPlus n).filter (· ∣ z), q ^ (padicValNat q (Nat.factorial n) / 2)

/-- Absorbed factor `B̃_i = u_i / W_i^2` absorbing 2-adic, odd-valuation, and inert-even powers. -/
def B_tilde (n u z : ℕ) : ℕ :=
  u / (W_split n z) ^ 2

/-- Total split-even factor `A_{n,+}^* = ∏_{q ∈ 𝒫_even^+(n)} q^{v_q(n!)}`. -/
def A_plus_star (n : ℕ) : ℕ :=
  ∏ q ∈ PevenPlus n, q ^ padicValNat q (Nat.factorial n)

lemma W_split_pos (n z : ℕ) : 0 < W_split n z := by
  unfold W_split
  exact Finset.prod_pos (fun q hq => pow_pos (by
    have := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1; omega) _)

lemma A_plus_star_pos (n : ℕ) : 0 < A_plus_star n := by
  unfold A_plus_star
  exact Finset.prod_pos (fun q hq => pow_pos (by
    have := (Finset.mem_filter.mp hq).2.1; omega) _)

/-- **Theorem 5.3(ii), part 1 — Deterministic `𝒫_even^-(n)`-Absorption**:
For any solution `(n, m)` to `n! + 1 = m^2` with `n ≥ 4`, `u₁ = (m - 1)/2 = δ₁ z₁^2`,
`u₂ = (m + 1)/2 = δ₂ z₂^2`, every inert prime `q ∈ 𝒫_even^-(n)` satisfies:
`q ∣ z₁ ↔ (δ₂ / q) = +1` and `q ∣ z₂ ↔ (δ₂ / q) = -1`. -/
theorem thm_5_3_part2_inert_absorption {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2)
    {q : ℕ} (hq : q ∈ PevenMinus n) :
    let u₁ := (m - 1) / 2
    let u₂ := (m + 1) / 2
    let δ₂ := coreNat u₂
    let z₁ := sqPartNat u₁
    let z₂ := sqPartNat u₂
    (q ∣ z₁ ↔ chiLegendre (δ₂ : ℤ) q = 1) ∧
    (q ∣ z₂ ↔ chiLegendre (δ₂ : ℤ) q = -1) := by
  have hmem := Finset.mem_filter.mp hq
  have hq_peven := Finset.mem_filter.mp hmem.1
  have hq_le_n : q ≤ n := (Finset.mem_Icc.mp hq_peven.1).2
  have hq_pr : q.Prime := hq_peven.2.1
  have hq_even : padicValNat q (Nat.factorial n) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hq_peven.2.2
  have hq3 : 3 ≤ q := hmem.2.1
  have hq_inert : chiLegendre (-(q_n n : ℤ)) q = -1 := hmem.2.2
  haveI : Fact q.Prime := ⟨hq_pr⟩
  have ⟨hδ_prod, _, hz_prod, hdiff, _, _⟩ := thm_5_2_part1_bipartition hn hm
  set u₁ := (m - 1) / 2
  set u₂ := (m + 1) / 2
  set δ₁ := coreNat u₁
  set δ₂ := coreNat u₂
  set z₁ := sqPartNat u₁
  set z₂ := sqPartNat u₂
  have hq_dvd_fac : q ∣ Nat.factorial n := hq_pr.dvd_factorial.mpr hq_le_n
  have hq_val_ge1 : 1 ≤ padicValNat q (Nat.factorial n) :=
    one_le_padicValNat_of_dvd (Nat.factorial_pos n).ne' hq_dvd_fac
  have hq_val_ge2 : 2 ≤ padicValNat q (Nat.factorial n) := by omega
  have hq2_dvd_fac : q ^ 2 ∣ Nat.factorial n :=
    (padicValNat_dvd_iff_le (Nat.factorial_pos n).ne').mpr hq_val_ge2
  have hfac_qs := factorial_eq_q_n_mul_s_n_sq n
  have hq_nd_qn : ¬ q ∣ q_n n := by
    intro hqd
    have hvp1 : padicValNat q (Nat.factorial n) = 1 + 2 * padicValNat q (s_n n) := by
      have hq_pos : 0 < q_n n := (q_n_squarefree n).ne_zero |> Nat.pos_of_ne_zero
      have hs_pos : 0 < s_n n := Nat.pos_of_ne_zero (fun h0 => by
        rw [h0] at hfac_qs; simp at hfac_qs; exact (Nat.factorial_pos n).ne' hfac_qs)
      have hv := congrArg (padicValNat q) hfac_qs
      rw [padicValNat.mul hq_pos.ne' (pow_ne_zero 2 hs_pos.ne'), padicValNat_pow_eq] at hv
      have hvpq1 : padicValNat q (q_n n) = 1 := by
        have h1 := one_le_padicValNat_of_dvd hq_pos.ne' hqd
        have hle1 : padicValNat q (q_n n) ≤ 1 := by
          by_contra hgt
          exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) q hq_pr
            (by rw [← sq]; exact dvd_trans (pow_dvd_pow q (by omega : 2 ≤ padicValNat q (q_n n))) pow_padicValNat_dvd)
        omega
      omega
    omega
  have hq_dvd_sn : q ∣ s_n n := by
    have hq2_dvd_qs : q ^ 2 ∣ q_n n * (s_n n) ^ 2 := hfac_qs ▸ hq2_dvd_fac
    have hcop : Nat.Coprime (q ^ 2) (q_n n) :=
      ((hq_pr.coprime_iff_not_dvd).mpr hq_nd_qn).pow_left 2
    have hq2_dvd_s2 : q ^ 2 ∣ (s_n n) ^ 2 := hcop.dvd_of_dvd_mul_left hq2_dvd_qs
    exact hq_pr.dvd_of_dvd_pow (dvd_trans (dvd_pow_self q (by norm_num)) hq2_dvd_s2)
  have hq_dvd_z1z2 : q ∣ z₁ * z₂ := by
    rw [hz_prod]
    have h2q : Nat.Coprime q 2 := (Nat.coprime_primes hq_pr Nat.prime_two).mpr (by omega)
    have hs_eq : 2 * (s_n n / 2) = s_n n := by
      have ⟨_, _, _, _, _, _, h2s⟩ := brocard_u1_u2_rel hn hm
      exact Nat.mul_div_cancel' h2s
    exact h2q.dvd_of_dvd_mul_left (hs_eq.symm ▸ hq_dvd_sn)
  have hq_not_both : ¬ (q ∣ z₁ ∧ q ∣ z₂) := by
    rintro ⟨h1, h2⟩
    have ⟨hu1_pos, hu2_pos, _, hcop_u, _⟩ := brocard_u1_u2_rel hn hm
    have h1_eq : coreNat u₁ * sqPartNat u₁ ^ 2 = u₁ := coreNat_mul_sqPartNat_sq hu1_pos
    have h2_eq : coreNat u₂ * sqPartNat u₂ ^ 2 = u₂ := coreNat_mul_sqPartNat_sq hu2_pos
    have h_u1 : q ∣ u₁ := h1_eq ▸ dvd_mul_of_dvd_right (dvd_pow h1 (by norm_num)) _
    have h_u2 : q ∣ u₂ := h2_eq ▸ dvd_mul_of_dvd_right (dvd_pow h2 (by norm_num)) _
    have := Nat.dvd_gcd h_u1 h_u2
    rw [hcop_u.gcd_eq_one] at this
    exact hq_pr.ne_one (Nat.dvd_one.mp this)
  have h_leg_prod : chiLegendre (-(δ₁ : ℤ)) q * chiLegendre (δ₂ : ℤ) q = -1 := by
    unfold chiLegendre at hq_inert ⊢
    simp only [dif_pos hq_pr] at hq_inert ⊢
    have hq_eq : (-(q_n n : ℤ)) = (-(δ₁ : ℤ)) * (δ₂ : ℤ) := by
      have : q_n n = δ₁ * δ₂ := hδ_prod.symm
      rw [this]; push_cast; ring
    rw [hq_eq, legendreSym.mul] at hq_inert
    exact hq_inert
  have hz1_imp : q ∣ z₁ → chiLegendre (δ₂ : ℤ) q = 1 := by
    intro hqz1
    have hqz1_z : ((z₁ : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (by exact_mod_cast hqz1)
    have hmod := congrArg (Int.cast (R := ZMod q)) hdiff
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_one] at hmod
    rw [hqz1_z, zero_pow (by norm_num), mul_zero, sub_zero] at hmod
    have hz2_ne : ((z₂ : ℤ) : ZMod q) ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num), mul_zero] at hmod
      exact zero_ne_one hmod
    have hd2_ne : ((δ₂ : ℤ) : ZMod q) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmod
      exact zero_ne_one hmod
    have hsq : IsSquare ((δ₂ : ℤ) : ZMod q) := by
      refine ⟨((z₂ : ℤ) : ZMod q)⁻¹, ?_⟩
      have hinv : ((z₂ : ℤ) : ZMod q) * ((z₂ : ℤ) : ZMod q)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ (isUnit_iff_ne_zero.mpr hz2_ne)
      calc ((δ₂ : ℤ) : ZMod q) = ((δ₂ : ℤ) : ZMod q) * (((z₂ : ℤ) : ZMod q) * ((z₂ : ℤ) : ZMod q)⁻¹) ^ 2 := by
            rw [hinv, one_pow, mul_one]
        _ = (((δ₂ : ℤ) : ZMod q) * ((z₂ : ℤ) : ZMod q) ^ 2) * (((z₂ : ℤ) : ZMod q)⁻¹) ^ 2 := by ring
        _ = (((z₂ : ℤ) : ZMod q)⁻¹) * (((z₂ : ℤ) : ZMod q)⁻¹) := by rw [hmod, one_mul, sq]
    unfold chiLegendre
    simp only [dif_pos hq_pr]
    exact (legendreSym.eq_one_iff q hd2_ne).mpr hsq
  have hz2_imp : q ∣ z₂ → chiLegendre (δ₂ : ℤ) q = -1 := by
    intro hqz2
    have hqz2_z : ((z₂ : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (by exact_mod_cast hqz2)
    have hmod := congrArg (Int.cast (R := ZMod q)) hdiff
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_one] at hmod
    rw [hqz2_z, zero_pow (by norm_num), mul_zero, zero_sub] at hmod
    have hz1_ne : ((z₁ : ℤ) : ZMod q) ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num), mul_zero, neg_zero] at hmod
      exact zero_ne_one hmod
    have hd1_ne : ((-(δ₁ : ℤ) : ℤ) : ZMod q) ≠ 0 := by
      intro h0
      have h0' : -((δ₁ : ℤ) : ZMod q) = 0 := by simpa using h0
      have h_eq0 : ((δ₁ : ℤ) : ZMod q) = 0 := neg_eq_zero.mp h0'
      rw [h_eq0, zero_mul, neg_zero] at hmod
      exact zero_ne_one hmod
    have hsq : IsSquare ((-(δ₁ : ℤ) : ℤ) : ZMod q) := by
      refine ⟨((z₁ : ℤ) : ZMod q)⁻¹, ?_⟩
      have hinv : ((z₁ : ℤ) : ZMod q) * ((z₁ : ℤ) : ZMod q)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ (isUnit_iff_ne_zero.mpr hz1_ne)
      have hmod' : ((-(δ₁ : ℤ) : ℤ) : ZMod q) * ((z₁ : ℤ) : ZMod q) ^ 2 = 1 := by
        rw [Int.cast_neg, neg_mul]; exact hmod
      calc ((-(δ₁ : ℤ) : ℤ) : ZMod q) = ((-(δ₁ : ℤ) : ℤ) : ZMod q) * (((z₁ : ℤ) : ZMod q) * ((z₁ : ℤ) : ZMod q)⁻¹) ^ 2 := by
            rw [hinv, one_pow, mul_one]
        _ = (((-(δ₁ : ℤ) : ℤ) : ZMod q) * ((z₁ : ℤ) : ZMod q) ^ 2) * (((z₁ : ℤ) : ZMod q)⁻¹) ^ 2 := by ring
        _ = (((z₁ : ℤ) : ZMod q)⁻¹) * (((z₁ : ℤ) : ZMod q)⁻¹) := by rw [hmod', one_mul, sq]
    have h_leg1 : chiLegendre (-(δ₁ : ℤ)) q = 1 := by
      unfold chiLegendre; simp only [dif_pos hq_pr]
      exact (legendreSym.eq_one_iff q hd1_ne).mpr hsq
    rw [h_leg1, one_mul] at h_leg_prod
    exact h_leg_prod
  rcases hq_pr.dvd_mul.mp hq_dvd_z1z2 with h1 | h2
  · have h2_nd : ¬ q ∣ z₂ := fun h2 => hq_not_both ⟨h1, h2⟩
    have hleg := hz1_imp h1
    constructor
    · exact ⟨fun _ => hleg, fun _ => h1⟩
    · exact ⟨fun h => absurd h h2_nd, fun h => by rw [hleg] at h; omega⟩
  · have h1_nd : ¬ q ∣ z₁ := fun h1 => hq_not_both ⟨h1, h2⟩
    have hleg := hz2_imp h2
    constructor
    · exact ⟨fun h => absurd h h1_nd, fun h => by rw [hleg] at h; omega⟩
    · exact ⟨fun _ => hleg, fun _ => h2⟩

/-- **Theorem 5.3(ii), part 2 — Reduced Dual Quartic Laws (eq. 5.10)**:
Writing `u₁ = Btilde₁ W₁^2` and `u₂ = Btilde₂ W₂^2` where `W_i = ∏_{q ∈ 𝒫_even^+(n), q ∣ z_i} q^{v_q(n!)/2}`,
we have `(W₁ W₂)^2 = A_{n,+}^*` and the dual quartic equations:
`Btilde₂ A_{n,+}^* = Btilde₁ W₁^4 + W₁^2` and `Btilde₁ A_{n,+}^* = Btilde₂ W₂^4 - W₂^2`. -/
theorem thm_5_3_part2_dual_quartic {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    let u₁ := (m - 1) / 2
    let u₂ := (m + 1) / 2
    let z₁ := sqPartNat u₁
    let z₂ := sqPartNat u₂
    let W₁ := W_split n z₁
    let W₂ := W_split n z₂
    let Btilde₁ := B_tilde n u₁ z₁
    let Btilde₂ := B_tilde n u₂ z₂
    u₁ = Btilde₁ * W₁ ^ 2 ∧
    u₂ = Btilde₂ * W₂ ^ 2 ∧
    (W₁ * W₂) ^ 2 = A_plus_star n ∧
    Btilde₂ * A_plus_star n = Btilde₁ * W₁ ^ 4 + W₁ ^ 2 ∧
    Btilde₁ * A_plus_star n = Btilde₂ * W₂ ^ 4 - W₂ ^ 2 := by
  have ⟨hu₁_pos, hu₂_pos, hu_diff, hcop_u, h4mul, hu_qs, h2_dvd_sn⟩ := brocard_u1_u2_rel hn hm
  have ⟨hδ_prod, _, hz_prod, _, _, _⟩ := thm_5_2_part1_bipartition hn hm
  set u₁ := (m - 1) / 2
  set u₂ := (m + 1) / 2
  set δ₁ := coreNat u₁
  set δ₂ := coreNat u₂
  set z₁ := sqPartNat u₁
  set z₂ := sqPartNat u₂
  set W₁ := W_split n z₁
  set W₂ := W_split n z₂
  set Btilde₁ := B_tilde n u₁ z₁
  set Btilde₂ := B_tilde n u₂ z₂
  have hz₁_pos : 0 < z₁ := sqPartNat_pos u₁
  have hz₂_pos : 0 < z₂ := sqPartNat_pos u₂
  have h1_eq : δ₁ * z₁ ^ 2 = u₁ := coreNat_mul_sqPartNat_sq hu₁_pos
  have h2_eq : δ₂ * z₂ ^ 2 = u₂ := coreNat_mul_sqPartNat_sq hu₂_pos
  have hz1_u1 : z₁ ∣ u₁ := h1_eq ▸ dvd_mul_of_dvd_right (dvd_pow_self z₁ (by norm_num)) δ₁
  have hz2_u2 : z₂ ∣ u₂ := h2_eq ▸ dvd_mul_of_dvd_right (dvd_pow_self z₂ (by norm_num)) δ₂
  have hcop_z : Nat.Coprime z₁ z₂ := (hcop_u.coprime_dvd_left hz1_u1).coprime_dvd_right hz2_u2
  have h_val_z : ∀ q : ℕ, q ∈ PevenPlus n →
      (q ∣ z₁ → padicValNat q z₁ = padicValNat q (Nat.factorial n) / 2) ∧
      (q ∣ z₂ → padicValNat q z₂ = padicValNat q (Nat.factorial n) / 2) ∧
      (q ∣ z₁ ∨ q ∣ z₂) := by
    intro q hq
    have hq_mem := Finset.mem_filter.mp hq
    have hq_pe := Finset.mem_filter.mp hq_mem.1
    have hq_le_n : q ≤ n := (Finset.mem_Icc.mp hq_pe.1).2
    have hq_pr : q.Prime := hq_pe.2.1
    have hq_even : padicValNat q (Nat.factorial n) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hq_pe.2.2
    have hq3 : 3 ≤ q := hq_mem.2.1
    haveI : Fact q.Prime := ⟨hq_pr⟩
    have hq_dvd_fac : q ∣ Nat.factorial n := hq_pr.dvd_factorial.mpr hq_le_n
    have hq_val_ge2 : 2 ≤ padicValNat q (Nat.factorial n) := by
      have := one_le_padicValNat_of_dvd (Nat.factorial_pos n).ne' hq_dvd_fac
      omega
    have hfac_qs := factorial_eq_q_n_mul_s_n_sq n
    have hq_nd_qn : ¬ q ∣ q_n n := by
      intro hqd
      have hq_pos : 0 < q_n n := (q_n_squarefree n).ne_zero |> Nat.pos_of_ne_zero
      have hs_pos : 0 < s_n n := Nat.pos_of_ne_zero (fun h0 => by
        rw [h0] at hfac_qs; simp at hfac_qs; exact (Nat.factorial_pos n).ne' hfac_qs)
      have hv := congrArg (padicValNat q) hfac_qs
      rw [padicValNat.mul hq_pos.ne' (pow_ne_zero 2 hs_pos.ne'), padicValNat_pow_eq] at hv
      have hvpq1 : padicValNat q (q_n n) = 1 := by
        have h1 := one_le_padicValNat_of_dvd hq_pos.ne' hqd
        have hle1 : padicValNat q (q_n n) ≤ 1 := by
          by_contra hgt
          exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) q hq_pr
            (by rw [← sq]; exact dvd_trans (pow_dvd_pow q (by omega : 2 ≤ padicValNat q (q_n n))) pow_padicValNat_dvd)
        omega
      omega
    have hq_dvd_sn : q ∣ s_n n := by
      have hq2_dvd_fac : q ^ 2 ∣ Nat.factorial n :=
        (padicValNat_dvd_iff_le (Nat.factorial_pos n).ne').mpr hq_val_ge2
      have hq2_dvd_qs : q ^ 2 ∣ q_n n * (s_n n) ^ 2 := hfac_qs ▸ hq2_dvd_fac
      have hcop : Nat.Coprime (q ^ 2) (q_n n) :=
        ((hq_pr.coprime_iff_not_dvd).mpr hq_nd_qn).pow_left 2
      exact hq_pr.dvd_of_dvd_pow (dvd_trans (dvd_pow_self q (by norm_num)) (hcop.dvd_of_dvd_mul_left hq2_dvd_qs))
    have hq_dvd_z1z2 : q ∣ z₁ * z₂ := by
      rw [hz_prod]
      have h2q : Nat.Coprime q 2 := (Nat.coprime_primes hq_pr Nat.prime_two).mpr (by omega)
      have hs_eq : 2 * (s_n n / 2) = s_n n := Nat.mul_div_cancel' h2_dvd_sn
      exact h2q.dvd_of_dvd_mul_left (hs_eq.symm ▸ hq_dvd_sn)
    have h_or := hq_pr.dvd_mul.mp hq_dvd_z1z2
    have h4u : 4 * (u₁ * u₂) = Nat.factorial n := by linarith
    have hv_fac_4u := congrArg (padicValNat q) h4u
    have hq_nd4 : ¬ q ∣ 4 := fun hd =>
      (by omega : q ≠ 2) ((Nat.prime_dvd_prime_iff_eq hq_pr Nat.prime_two).mp
        (hq_pr.dvd_of_dvd_pow (show q ∣ 2 ^ 2 by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hd)))
    rw [padicValNat.mul (by norm_num) (mul_pos hu₁_pos hu₂_pos).ne',
        padicValNat.eq_zero_of_not_dvd hq_nd4,
        zero_add, padicValNat.mul hu₁_pos.ne' hu₂_pos.ne'] at hv_fac_4u
    refine ⟨fun hqz1 => ?_, fun hqz2 => ?_, h_or⟩
    · have hqz2_nd : ¬ q ∣ z₂ := fun h2 =>
        hq_pr.ne_one (Nat.dvd_one.mp (hcop_z.gcd_eq_one ▸ Nat.dvd_gcd hqz1 h2))
      have hqu1 : q ∣ u₁ := h1_eq ▸ dvd_mul_of_dvd_right (dvd_pow hqz1 (by norm_num)) _
      have hqu2_nd : ¬ q ∣ u₂ := fun h2 =>
        hq_pr.ne_one (Nat.dvd_one.mp (hcop_u.gcd_eq_one ▸ Nat.dvd_gcd hqu1 h2))
      have hv0 : padicValNat q u₂ = 0 := padicValNat.eq_zero_of_not_dvd hqu2_nd
      rw [padicValNat_sqPartNat hq_pr, ← hv_fac_4u, hv0, add_zero]
    · have hqz1_nd : ¬ q ∣ z₁ := fun h1 =>
        hq_pr.ne_one (Nat.dvd_one.mp (hcop_z.gcd_eq_one ▸ Nat.dvd_gcd h1 hqz2))
      have hqu2 : q ∣ u₂ := h2_eq ▸ dvd_mul_of_dvd_right (dvd_pow hqz2 (by norm_num)) _
      have hqu1_nd : ¬ q ∣ u₁ := fun h1 =>
        hq_pr.ne_one (Nat.dvd_one.mp (hcop_u.gcd_eq_one ▸ Nat.dvd_gcd h1 hqu2))
      have hv0 : padicValNat q u₁ = 0 := padicValNat.eq_zero_of_not_dvd hqu1_nd
      rw [padicValNat_sqPartNat hq_pr, ← hv_fac_4u, hv0, zero_add]
  have h_prod_dvd_nat : ∀ (z : ℕ) (S : Finset ℕ) (f : ℕ → ℕ),
      (∀ q ∈ S, q.Prime ∧ q ^ f q ∣ z) → (∏ q ∈ S, q ^ f q) ∣ z := by
    intro z S f hS
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a s has ih =>
      rw [Finset.prod_insert has]
      have ha := hS a (Finset.mem_insert_self a s)
      have hs := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
      have hcop : Nat.Coprime (a ^ f a) (∏ q ∈ s, q ^ f q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        have hq_pr := (hS q (Finset.mem_insert_of_mem hq)).1
        exact ((Nat.coprime_primes ha.1 hq_pr).mpr (fun h => has (h ▸ hq))).pow _ _
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop ha.2 hs
  have hW1_dvd_z1 : W₁ ∣ z₁ := by
    unfold W₁ W_split
    apply h_prod_dvd_nat
    intro q hq
    have hq_mem := Finset.mem_filter.mp hq
    have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq_mem.1).1).2.1
    haveI : Fact q.Prime := ⟨hq_pr⟩
    refine ⟨hq_pr, ?_⟩
    rw [← (h_val_z q hq_mem.1).1 hq_mem.2]
    exact pow_padicValNat_dvd
  have hW2_dvd_z2 : W₂ ∣ z₂ := by
    unfold W₂ W_split
    apply h_prod_dvd_nat
    intro q hq
    have hq_mem := Finset.mem_filter.mp hq
    have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq_mem.1).1).2.1
    haveI : Fact q.Prime := ⟨hq_pr⟩
    refine ⟨hq_pr, ?_⟩
    rw [← (h_val_z q hq_mem.1).2.1 hq_mem.2]
    exact pow_padicValNat_dvd
  have hW1_sq_u1 : W₁ ^ 2 ∣ u₁ := h1_eq ▸ dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hW1_dvd_z1 2) _
  have hW2_sq_u2 : W₂ ^ 2 ∣ u₂ := h2_eq ▸ dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hW2_dvd_z2 2) _
  have hu1_eq : u₁ = Btilde₁ * W₁ ^ 2 := (Nat.div_mul_cancel hW1_sq_u1).symm
  have hu2_eq : u₂ = Btilde₂ * W₂ ^ 2 := (Nat.div_mul_cancel hW2_sq_u2).symm
  have h_disj : Disjoint ((PevenPlus n).filter (· ∣ z₁)) ((PevenPlus n).filter (· ∣ z₂)) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq1).1).1).2.1
    have h1 := (Finset.mem_filter.mp hq1).2
    have h2 := (Finset.mem_filter.mp hq2).2
    exact hq_pr.ne_one (Nat.dvd_one.mp (hcop_z.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))
  have h_union : (PevenPlus n).filter (· ∣ z₁) ∪ (PevenPlus n).filter (· ∣ z₂) = PevenPlus n := by
    ext q
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
    · intro hq
      rcases (h_val_z q hq).2.2 with h1 | h2
      · exact Or.inl ⟨hq, h1⟩
      · exact Or.inr ⟨hq, h2⟩
  have hW_sq_eq : (W₁ * W₂) ^ 2 = A_plus_star n := by
    unfold W₁ W₂ W_split A_plus_star
    rw [← Finset.prod_union h_disj, h_union, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro q hq
    have hq_even : padicValNat q (Nat.factorial n) % 2 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.2
    rw [← pow_mul]
    congr 1
    omega
  have h_diff_B : (Btilde₂ : ℤ) * (W₂ : ℤ) ^ 2 - (Btilde₁ : ℤ) * (W₁ : ℤ) ^ 2 = 1 := by
    have h1z : (Btilde₁ : ℤ) * (W₁ : ℤ) ^ 2 = (u₁ : ℤ) := by exact_mod_cast hu1_eq.symm
    have h2z : (Btilde₂ : ℤ) * (W₂ : ℤ) ^ 2 = (u₂ : ℤ) := by exact_mod_cast hu2_eq.symm
    have hdz : (u₂ : ℤ) = (u₁ : ℤ) + 1 := by exact_mod_cast hu_diff
    linarith
  have hq1_z : (Btilde₂ : ℤ) * (A_plus_star n : ℤ) = (Btilde₁ : ℤ) * (W₁ : ℤ) ^ 4 + (W₁ : ℤ) ^ 2 := by
    have hA_z : (A_plus_star n : ℤ) = ((W₁ : ℤ) * (W₂ : ℤ)) ^ 2 := by exact_mod_cast hW_sq_eq.symm
    rw [hA_z]
    have hmul := congrArg (· * (W₁ : ℤ) ^ 2) h_diff_B
    linarith
  have hq2_z : (Btilde₁ : ℤ) * (A_plus_star n : ℤ) = (Btilde₂ : ℤ) * (W₂ : ℤ) ^ 4 - (W₂ : ℤ) ^ 2 := by
    have hA_z : (A_plus_star n : ℤ) = ((W₁ : ℤ) * (W₂ : ℤ)) ^ 2 := by exact_mod_cast hW_sq_eq.symm
    rw [hA_z]
    have hmul := congrArg (· * (W₂ : ℤ) ^ 2) h_diff_B
    linarith
  have hq1 : Btilde₂ * A_plus_star n = Btilde₁ * W₁ ^ 4 + W₁ ^ 2 := by exact_mod_cast hq1_z
  have hq2 : Btilde₁ * A_plus_star n = Btilde₂ * W₂ ^ 4 - W₂ ^ 2 := by
    have hq2_nat : Btilde₁ * A_plus_star n + W₂ ^ 2 = Btilde₂ * W₂ ^ 4 := by
      have : ((Btilde₁ * A_plus_star n + W₂ ^ 2 : ℕ) : ℤ) = ((Btilde₂ * W₂ ^ 4 : ℕ) : ℤ) := by
        push_cast; linarith [hq2_z]
      exact_mod_cast this
    omega
  exact ⟨hu1_eq, hu2_eq, hW_sq_eq, hq1, hq2⟩

end GrasGreenbergBrocard
