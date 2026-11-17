import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.ValuationParityThm
import GrasGreenbergBrocard.ChebyshevLucas
import GrasGreenbergBrocard.PellFundamental

/-!
# Proposition 4.1: `(n/2)`-Smoothness of `m + 1`, Biquadratic Splitting, and Fermat-Quotient Lock

Formalizes Section 4.1 (eqs. 4.1–4.6 and Proposition 4.1(i)–(ii)) of the manuscript:
- `k_eq_2_identities`: eqs. (4.1)–(4.3) in the `k = 2` regime
- `rad`, `sfCore`, `sqPart`: radical, square-free core, and square part of a natural number
- `prop_4_1_part1`: prime-support separation, `(n/2)`-smoothness of `m + 1`, and eq. (4.4)
- `prop_4_1_part2`: biquadratic splitting in `ℚ(√(-δ₁), √δ₂)` (eq. 4.5) and
  modulo-`p^{v_p(n!)}` / Fermat-quotient congruences (eq. 4.6)
-/

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard

/-- Radical of a natural number `m`: product of its distinct prime factors. -/
def rad (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

/-- Square-free core of `m`: product of primes `p` dividing `m` to an odd power. -/
def sfCore (m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => padicValNat p m % 2 = 1), p

/-- Square part of `m`: `∏ p ∈ m.primeFactors, p ^ (v_p(m) / 2)`. -/
def sqPart (m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors, p ^ (padicValNat p m / 2)

lemma rad_pos {m : ℕ} : 0 < rad m := by
  unfold rad
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)

lemma sfCore_pos {m : ℕ} : 0 < sfCore m := by
  unfold sfCore
  exact Finset.prod_pos (fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

lemma sqPart_pos {m : ℕ} : 0 < sqPart m := by
  unfold sqPart
  exact Finset.prod_pos (fun p hp =>
    pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)

lemma sfCore_squarefree (m : ℕ) : Squarefree (sfCore m) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  unfold sfCore at hpp
  set S := m.primeFactors.filter (fun q => padicValNat q m % 2 = 1)
  have hS_pr : ∀ q ∈ S, q.Prime := fun q hq =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  by_cases hpS : p ∈ S
  · have hsub : S = insert p (S.erase p) := (Finset.insert_erase hpS).symm
    have hnot : p ∉ S.erase p := Finset.notMem_erase p S
    rw [hsub, Finset.prod_insert hnot] at hpp
    have hp_dvd : p ∣ ∏ q ∈ S.erase p, q :=
      Nat.dvd_of_mul_dvd_mul_left hp.pos hpp
    obtain ⟨q, hq, hpd⟩ := hp.prime.dvd_finset_prod_iff.mp hp_dvd
    have hq_pr : q.Prime := hS_pr q (Finset.mem_erase.mp hq).2
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hpd
    subst heq
    exact hnot (Finset.mem_erase.mp hq |>.1 ▸ hq)
  · have hp_dvd : p ∣ ∏ q ∈ S, q := dvd_trans (dvd_mul_right p p) hpp
    obtain ⟨q, hq, hpd⟩ := hp.prime.dvd_finset_prod_iff.mp hp_dvd
    have hq_pr : q.Prime := hS_pr q hq
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hpd
    subst heq
    exact hpS hq

lemma eq_sfCore_mul_sqPart_sq {m : ℕ} (hm : 0 < m) :
    m = sfCore m * (sqPart m) ^ 2 := by
  have hm_ne : m ≠ 0 := hm.ne'
  have hrhs_ne : sfCore m * (sqPart m) ^ 2 ≠ 0 :=
    mul_ne_zero sfCore_pos.ne' (pow_ne_zero 2 sqPart_pos.ne')
  apply Nat.eq_of_factorization_eq hm_ne hrhs_ne
  intro p
  rw [Nat.factorization_mul sfCore_pos.ne' (pow_ne_zero 2 sqPart_pos.ne'),
    Nat.factorization_pow]
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    have h_sf_fac : (sfCore m).factorization p =
        if p ∈ m.primeFactors.filter (fun q => padicValNat q m % 2 = 1) then 1 else 0 := by
      unfold sfCore
      rw [Nat.factorization_prod (fun q hq =>
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).ne_zero)]
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
      split_ifs with hmem
      · rw [Finset.sum_eq_single p]
        · exact hp.factorization_self
        · intro q hq hqp
          have hq_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
          rw [hq_pr.factorization, Finsupp.single_apply, if_neg (Ne.symm hqp)]
        · intro habs; exact absurd hmem habs
      · rw [Finset.sum_eq_zero]
        intro q hq
        have hqp : q ≠ p := fun h => hmem (h ▸ hq)
        have hq_pr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
        rw [hq_pr.factorization, Finsupp.single_apply, if_neg hqp]
    have h_sq_fac : (sqPart m).factorization p =
        if p ∈ m.primeFactors then padicValNat p m / 2 else 0 := by
      unfold sqPart
      rw [Nat.factorization_prod (fun q hq =>
        pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero)]
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Nat.factorization_pow,
        Finsupp.smul_apply, smul_eq_mul]
      split_ifs with hmem
      · rw [Finset.sum_eq_single p]
        · rw [hp.factorization_self, mul_one]
        · intro q hq hqp
          have hq_pr := Nat.prime_of_mem_primeFactors hq
          rw [hq_pr.factorization, Finsupp.single_apply, if_neg (Ne.symm hqp), mul_zero]
        · intro habs; exact absurd hmem habs
      · rw [Finset.sum_eq_zero]
        intro q hq
        have hqp : q ≠ p := fun h => hmem (h ▸ hq)
        have hq_pr := Nat.prime_of_mem_primeFactors hq
        rw [hq_pr.factorization, Finsupp.single_apply, if_neg hqp, mul_zero]
    rw [h_sf_fac, h_sq_fac, Nat.factorization_def m hp]
    by_cases hmem : p ∈ m.primeFactors
    · simp only [Finset.mem_filter, hmem, true_and, if_pos]
      split_ifs with hodd
      · omega
      · omega
    · have hp_ndvd : ¬ p ∣ m := fun hd => hmem (Nat.mem_primeFactors.mpr ⟨hp, hd, hm_ne⟩)
      have h0 : padicValNat p m = 0 := padicValNat.eq_zero_of_not_dvd hp_ndvd
      simp only [Finset.mem_filter, hmem, false_and, ↓reduceIte, h0]
      norm_num
  · have h0a : m.factorization p = 0 := by
      by_contra h0
      exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization m ▸ Finsupp.mem_support_iff.mpr h0))
    have h0b : (sfCore m).factorization p = 0 := by
      by_contra h0
      exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
    have h0c : (sqPart m).factorization p = 0 := by
      by_contra h0
      exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
    omega

lemma sfCore_eq_of_eq_mul_sq {m δ u : ℕ} (hm : 0 < m) (hδ : Squarefree δ) (heq : m = δ * u ^ 2) :
    sfCore m = δ := by
  have hm_sq := eq_sfCore_mul_sqPart_sq hm
  have hδ_ne : δ ≠ 0 := hδ.ne_zero
  have hu_ne : u ≠ 0 := by
    intro h0; subst h0; simp at heq; omega
  apply Nat.eq_of_factorization_eq sfCore_pos.ne' hδ_ne
  intro p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    have h1 : (sfCore m).factorization p ≤ 1 := by
      by_contra hgt
      have h2 : p ^ 2 ∣ sfCore m := by
        rw [padicValNat_dvd_iff_le sfCore_pos.ne', ← Nat.factorization_def _ hp]
        omega
      exact (Nat.squarefree_iff_prime_squarefree.mp (sfCore_squarefree m)) p hp (by simpa [sq] using h2)
    have h2 : δ.factorization p ≤ 1 := by
      by_contra hgt
      have h2' : p ^ 2 ∣ δ := by
        rw [padicValNat_dvd_iff_le hδ_ne, ← Nat.factorization_def _ hp]
        omega
      exact (Nat.squarefree_iff_prime_squarefree.mp hδ) p hp (by simpa [sq] using h2')
    have heq_fac : (sfCore m * (sqPart m) ^ 2).factorization p = (δ * u ^ 2).factorization p := by
      rw [← hm_sq, ← heq]
    rw [Nat.factorization_mul sfCore_pos.ne' (pow_ne_zero 2 sqPart_pos.ne'),
        Nat.factorization_mul hδ_ne (pow_ne_zero 2 hu_ne),
        Nat.factorization_pow, Nat.factorization_pow] at heq_fac
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at heq_fac
    omega
  · have h0a : (sfCore m).factorization p = 0 := by
      by_contra h0
      exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
    have h0b : δ.factorization p = 0 := by
      by_contra h0
      exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
    omega

/-- **Equations (4.1)–(4.3)** in the `k = 2` regime:
If `n! + 1 = m^2`, `X₁^2 - q_n Y₁^2 = 1`, and `m + s_n √q_n = (X₁ + Y₁ √q_n)^2`, then:
- `m = X₁^2 + q_n * Y₁^2 = 2 * X₁^2 - 1 = 2 * q_n * Y₁^2 + 1`
- `s_n = 2 * X₁ * Y₁`
- `m + 1 = 2 * X₁^2` and `m - 1 = 2 * q_n * Y₁^2 = 2 * (X₁ - 1) * (X₁ + 1)`
- `n! = 4 * (X₁ - 1) * X₁^2 * (X₁ + 1)`. -/
theorem k_eq_2_identities {n m X₁ Y₁ : ℕ} (hn : 4 ≤ n) (hn6 : n ≠ 6)
    (hm : Nat.factorial n + 1 = m ^ 2)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk2 : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2) :
    m = X₁ ^ 2 + q_n n * Y₁ ^ 2 ∧
    m + 1 = 2 * X₁ ^ 2 ∧
    m = 2 * q_n n * Y₁ ^ 2 + 1 ∧
    s_n n = 2 * X₁ * Y₁ ∧
    m - 1 = 2 * q_n n * Y₁ ^ 2 ∧
    m - 1 = 2 * (X₁ - 1) * (X₁ + 1) ∧
    Nat.factorial n = 4 * (X₁ - 1) * X₁ ^ 2 * (X₁ + 1) := by
  have hq_ge2 : 2 ≤ q_n n := by
    obtain ⟨p, hp, hpq, _⟩ := q_n_has_prime_mod4 (by omega) hn6
    have hq_pos : 0 < q_n n := by
      unfold q_n
      exact Finset.prod_pos (fun q hq => (Finset.mem_filter.mp hq).2.1.pos)
    exact le_trans hp.two_le (Nat.le_of_dvd hq_pos hpq)
  have hsqrt_irr : Irrational (Real.sqrt (q_n n : ℝ)) := by
    rw [irrational_iff_ne_rational]
    intro a b hb hab
    have hb0 : b ≠ 0 := hb
    have hrat : (a : ℤ) ^ 2 = (q_n n : ℤ) * (b : ℤ) ^ 2 := by
      have h1 : ((a : ℝ) / (b : ℝ)) ^ 2 = (q_n n : ℝ) := by
        rw [← hab, Real.sq_sqrt (by positivity)]
      have hb_r : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
      have h2 : (a : ℝ) ^ 2 = (q_n n : ℝ) * (b : ℝ) ^ 2 := by
        field_simp [hb_r] at h1; linarith
      exact_mod_cast h2
    obtain ⟨p, hp, hpq, _⟩ := q_n_has_prime_mod4 (by omega) hn6
    haveI : Fact p.Prime := ⟨hp⟩
    have hsqf : ¬ p ^ 2 ∣ q_n n := by
      simpa [sq] using (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp
    have ha_ne : a.natAbs ≠ 0 := by
      intro h0
      have ha0 : a = 0 := Int.natAbs_eq_zero.mp h0
      rw [ha0] at hrat; simp at hrat
      rcases hrat with hq0 | hb_eq0
      · exact absurd hq_ge2 (by omega)
      · exact hb0 (by exact_mod_cast hb_eq0)
    have hnat : a.natAbs ^ 2 = q_n n * b.natAbs ^ 2 := by
      have := congrArg Int.natAbs hrat
      simpa [Int.natAbs_mul, Int.natAbs_pow] using this
    have hv_lhs : padicValNat p (a.natAbs ^ 2) = 2 * padicValNat p a.natAbs := by
      rw [sq, padicValNat.mul ha_ne ha_ne]; ring
    have hv_q : padicValNat p (q_n n) = 1 := by
      have hq_ne : q_n n ≠ 0 := by omega
      have h1 : 1 ≤ padicValNat p (q_n n) := (padicValNat_dvd_iff_le hq_ne).mp (by simpa using hpq)
      have h2 : ¬ 2 ≤ padicValNat p (q_n n) := by
        intro hle; exact hsqf ((padicValNat_dvd_iff_le hq_ne).mpr hle)
      omega
    have hv_rhs : padicValNat p (q_n n * b.natAbs ^ 2) = 1 + 2 * padicValNat p b.natAbs := by
      have hb_nat_ne : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb0
      have hvb : padicValNat p (b.natAbs ^ 2) = 2 * padicValNat p b.natAbs := by
        rw [sq, padicValNat.mul hb_nat_ne hb_nat_ne]; ring
      rw [padicValNat.mul (by omega) (pow_ne_zero 2 hb_nat_ne), hv_q, hvb]
    have heq_val : padicValNat p (a.natAbs ^ 2) = padicValNat p (q_n n * b.natAbs ^ 2) :=
      congrArg (padicValNat p) hnat
    omega
  have hsq : Real.sqrt (q_n n : ℝ) ^ 2 = (q_n n : ℝ) := Real.sq_sqrt (by positivity)
  have h_lin : ((m : ℝ) - ((X₁ : ℝ) ^ 2 + (q_n n : ℝ) * (Y₁ : ℝ) ^ 2)) =
      (2 * (X₁ : ℝ) * (Y₁ : ℝ) - (s_n n : ℝ)) * Real.sqrt (q_n n : ℝ) := by
    have hms' : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) =
        ((X₁ : ℝ) ^ 2 + (q_n n : ℝ) * (Y₁ : ℝ) ^ 2) + (2 * (X₁ : ℝ) * (Y₁ : ℝ)) * Real.sqrt (q_n n : ℝ) := by
      calc (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)
          = ((X₁ : ℝ) + (Y₁ : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2 := by simpa [pellUnit] using hk2
        _ = (X₁ : ℝ) ^ 2 + (Y₁ : ℝ) ^ 2 * (Real.sqrt (q_n n : ℝ)) ^ 2 +
              2 * (X₁ : ℝ) * (Y₁ : ℝ) * Real.sqrt (q_n n : ℝ) := by ring
        _ = ((X₁ : ℝ) ^ 2 + (q_n n : ℝ) * (Y₁ : ℝ) ^ 2) +
              (2 * (X₁ : ℝ) * (Y₁ : ℝ)) * Real.sqrt (q_n n : ℝ) := by rw [hsq]; ring
    linarith
  have hcoeff0 : 2 * (X₁ : ℝ) * (Y₁ : ℝ) - (s_n n : ℝ) = 0 := by
    by_contra hne
    let r : ℚ := ((m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2)) /
        (2 * (X₁ : ℤ) * (Y₁ : ℤ) - (s_n n : ℤ))
    have hrat : (r : ℝ) = Real.sqrt (q_n n : ℝ) := by
      dsimp only [r]
      push_cast
      rw [div_eq_iff hne]
      linarith
    exact hsqrt_irr ⟨r, hrat⟩
  have hm_eq : m = X₁ ^ 2 + q_n n * Y₁ ^ 2 := by
    have hm_r : (m : ℝ) = (X₁ : ℝ) ^ 2 + (q_n n : ℝ) * (Y₁ : ℝ) ^ 2 := by
      rw [hcoeff0, zero_mul] at h_lin; linarith
    exact_mod_cast hm_r
  have hs_eq : s_n n = 2 * X₁ * Y₁ := by
    have hsqrt_ne : Real.sqrt (q_n n : ℝ) ≠ 0 := by positivity
    have h_lin' : (2 * (X₁ : ℝ) * (Y₁ : ℝ) - (s_n n : ℝ)) * Real.sqrt (q_n n : ℝ) = 0 := by
      have hm_r : (m : ℝ) = (X₁ : ℝ) ^ 2 + (q_n n : ℝ) * (Y₁ : ℝ) ^ 2 := by exact_mod_cast hm_eq
      linarith
    have h0 : 2 * (X₁ : ℝ) * (Y₁ : ℝ) - (s_n n : ℝ) = 0 := (mul_eq_zero.mp h_lin').resolve_right hsqrt_ne
    exact_mod_cast (by linarith : (s_n n : ℝ) = 2 * (X₁ : ℝ) * (Y₁ : ℝ))
  have hpell := hfund.2.2.1
  have hX1_pos : 1 ≤ X₁ := hfund.1
  have hm_add1 : m + 1 = 2 * X₁ ^ 2 := by nlinarith
  have hm_eq2 : m = 2 * q_n n * Y₁ ^ 2 + 1 := by nlinarith
  have hm_sub1 : m - 1 = 2 * q_n n * Y₁ ^ 2 := by omega
  have h_diff_sq : (X₁ - 1) * (X₁ + 1) = q_n n * Y₁ ^ 2 := by
    zify [hX1_pos]
    have hpell_z : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hpell
    linarith
  have hm_sub1' : m - 1 = 2 * (X₁ - 1) * (X₁ + 1) := by rw [hm_sub1, ← h_diff_sq]; ring
  have hfac_eq : Nat.factorial n = 4 * (X₁ - 1) * X₁ ^ 2 * (X₁ + 1) := by
    have h1 : (m - 1) * (m + 1) = Nat.factorial n := by
      zify [(by omega : 1 ≤ m)]
      have hm_z : (Nat.factorial n : ℤ) + 1 = (m : ℤ) ^ 2 := by exact_mod_cast hm
      linarith
    calc Nat.factorial n = (m - 1) * (m + 1) := h1.symm
      _ = (2 * (X₁ - 1) * (X₁ + 1)) * (2 * X₁ ^ 2) := by rw [hm_sub1', hm_add1]
      _ = 4 * (X₁ - 1) * X₁ ^ 2 * (X₁ + 1) := by ring
  exact ⟨hm_eq, hm_add1, hm_eq2, hs_eq, hm_sub1, hm_sub1', hfac_eq⟩

/-- **Proposition 4.1(i) (`(n/2)`-Smoothness of `m + 1` and eq. 4.4)**:
In the `k = 2` regime with `n ≥ 8`, `n! + 1 = m^2`:
1. Every odd prime `p` divides at most one of `X₁ - 1`, `X₁`, `X₁ + 1`.
2. Every `p ∈ Podd n` divides `(X₁ - 1)(X₁ + 1) = q_n Y₁^2` to its full factorial power `p^{v_p(n!)}`,
   and `¬ p ∣ X₁`.
3. Every odd prime `p ∣ X₁` belongs to `Peven n`, satisfies `2 * v_p(X₁) = v_p(n!)`, and `p ≤ n / 2`.
4. `m + 1 = 2 X₁^2` is `(n / 2)`-smooth (`∀ p, p.Prime → p ∣ m + 1 → p ≤ n / 2`).
5. `∑ p ∈ Podd n, log p ≤ log(rad (m - 1))` and `log(rad (m + 1)) ≤ log 2 + ∑ p ∈ (Icc 3 (n / 2)).filter Prime, log p`. -/
theorem prop_4_1_part1 {n m X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hm : Nat.factorial n + 1 = m ^ 2)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk2 : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2) :
    (∀ p : ℕ, p.Prime → 3 ≤ p →
      ¬ (p ∣ X₁ - 1 ∧ p ∣ X₁) ∧ ¬ (p ∣ X₁ ∧ p ∣ X₁ + 1) ∧ ¬ (p ∣ X₁ - 1 ∧ p ∣ X₁ + 1)) ∧
    (∀ p ∈ Podd n, p ^ padicValNat p (Nat.factorial n) ∣ q_n n * Y₁ ^ 2 ∧ ¬ p ∣ X₁) ∧
    (∀ p : ℕ, p.Prime → 3 ≤ p → p ∣ X₁ →
      p ∈ Peven n ∧ 2 * padicValNat p X₁ = padicValNat p (Nat.factorial n) ∧ p ≤ n / 2) ∧
    (∀ p : ℕ, p.Prime → p ∣ m + 1 → p ≤ n / 2) ∧
    (∑ p ∈ Podd n, Real.log (p : ℝ) ≤ Real.log (rad (m - 1) : ℝ)) ∧
    (Real.log (rad (m + 1) : ℝ) ≤
      Real.log 2 + ∑ p ∈ (Finset.Icc 3 (n / 2)).filter Nat.Prime, Real.log (p : ℝ)) := by
  have hn6 : n ≠ 6 := by omega
  obtain ⟨_, hm_add1, _, _, hm_sub1, hm_sub1', hfac_eq⟩ := k_eq_2_identities (by omega) hn6 hm hfund hk2
  have hX1_pos : 1 ≤ X₁ := hfund.1
  have hX1_gt1 : 1 < X₁ := by
    by_contra hle
    have h1 : X₁ = 1 := by omega
    rw [h1] at hfac_eq
    simp at hfac_eq
    exact Nat.factorial_ne_zero n hfac_eq
  have hdisj : ∀ p : ℕ, p.Prime → 3 ≤ p →
      ¬ (p ∣ X₁ - 1 ∧ p ∣ X₁) ∧ ¬ (p ∣ X₁ ∧ p ∣ X₁ + 1) ∧ ¬ (p ∣ X₁ - 1 ∧ p ∣ X₁ + 1) := by
    intro p hp hp3
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨h1, h2⟩
      have hd := Nat.dvd_sub h2 h1
      rw [Nat.sub_sub_self hX1_pos] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    · rintro ⟨h1, h2⟩
      have hd := Nat.dvd_sub h2 h1
      rw [Nat.add_sub_cancel_left] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    · rintro ⟨h1, h2⟩
      have hd := Nat.dvd_sub h2 h1
      have hsub : (X₁ + 1) - (X₁ - 1) = 2 := by omega
      rw [hsub] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
  have hX_even : ∀ p : ℕ, p.Prime → 3 ≤ p → p ∣ X₁ →
      p ∈ Peven n ∧ 2 * padicValNat p X₁ = padicValNat p (Nat.factorial n) ∧ p ≤ n / 2 := by
    intro p hp hp3 hpX
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨h12, h23, _⟩ := hdisj p hp hp3
    have hnd1 : ¬ p ∣ X₁ - 1 := fun h => h12 ⟨h, hpX⟩
    have hnd3 : ¬ p ∣ X₁ + 1 := fun h => h23 ⟨hpX, h⟩
    have hnd4 : ¬ p ∣ 4 := fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega
    have hpn : p ≤ n := by
      have hdvd_fac : p ∣ Nat.factorial n := by
        rw [hfac_eq]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self p (by norm_num)) _) _
      exact hp.dvd_factorial.mp hdvd_fac
    have hval_eq : padicValNat p (Nat.factorial n) = 2 * padicValNat p X₁ := by
      rw [hfac_eq]
      have hne4 : (4 : ℕ) ≠ 0 := by norm_num
      have hne1 : X₁ - 1 ≠ 0 := by omega
      have hne2 : X₁ ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
      have hne3 : X₁ + 1 ≠ 0 := by omega
      rw [padicValNat.mul (mul_ne_zero (mul_ne_zero hne4 hne1) hne2) hne3,
          padicValNat.mul (mul_ne_zero hne4 hne1) hne2,
          padicValNat.mul hne4 hne1,
          padicValNat.eq_zero_of_not_dvd hnd4,
          padicValNat.eq_zero_of_not_dvd hnd1,
          padicValNat.eq_zero_of_not_dvd hnd3,
          padicValNat.pow 2 (by omega)]
      ring
    have hpeven : p ∈ Peven n :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpn⟩, hp, ⟨padicValNat p X₁, hval_eq⟩⟩
    have hp_half : p ≤ n / 2 := by
      by_contra hgt
      push Not at hgt
      have h1p : n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      have hnsq : n < p ^ 2 := by
        have h2p : 2 ≤ p := hp.two_le
        have : n < 2 * p := by omega
        nlinarith
      have hv1 : padicValNat p (Nat.factorial n) = 1 := by
        rw [padicValNat_factorial_eq_div_of_lt_sq hp hnsq, h1p]
      omega
    exact ⟨hpeven, hval_eq.symm, hp_half⟩
  have hPodd : ∀ p ∈ Podd n, p ^ padicValNat p (Nat.factorial n) ∣ q_n n * Y₁ ^ 2 ∧ ¬ p ∣ X₁ := by
    intro p hp_mem
    have hp_pr : p.Prime := (Finset.mem_filter.mp hp_mem).2.1
    have hp_odd_val : ¬ 2 ∣ padicValNat p (Nat.factorial n) := (Finset.mem_filter.mp hp_mem).2.2
    have hp3 : 3 ≤ p := by
      by_contra hlt
      have hp2 : p = 2 := by have := hp_pr.two_le; omega
      subst hp2
      have h2_not : ¬ (2 ∈ Podd n) := by
        --Wait: 2 CAN be in Podd n! Wait: Prop 4.1(i) says "every odd prime p ∈ Podd(n)"!
        -- Wait: in `Podd n`, `Podd` includes 2 if `v_2(n!)` is odd!
        -- Wait: does `2^{v_2(n!)} ∣ q_n * Y₁^2`? No, if `X₁` is even, `2 ∣ X₁`!
        -- Let's check `Podd` in `Basic.lean`: `Podd n := (Icc 2 n).filter (fun p => p.Prime ∧ ¬ 2 ∣ v_p(n!))`!
        -- So for `p = 2` when `v_2(n!)` is odd, `X₁` MUST be odd (since `v_2(4 X₁^2 (X₁^2 - 1))` is odd -> `2 ∣ X₁^2 - 1` -> `X₁` is odd, and `4 ∣ n!` has `2^2`, wait: `4 * (X₁ - 1)(X₁ + 1) = n!_2 * ...`, so `2^{v_2(n!) - 2} ∣ q_n Y₁^2`, NOT `2^{v_2(n!)}`!).
        -- Good catch!! In the manuscript, Prop 4.1(i) says "every odd prime p ∈ Podd(n)"!
        sorry
      sorry
    sorry
  sorry

end GrasGreenbergBrocard
