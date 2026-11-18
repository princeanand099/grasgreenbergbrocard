import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic
import GrasGreenbergBrocard.ExternalAxiomsSec3
import GrasGreenbergBrocard.ExternalAxiomsSec4
import GrasGreenbergBrocard.ExternalAxiomsSec5
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.PellFundamental

/-!
# Proposition 5.1: Continued-Fraction Midpoint Denominator and Square-Root Conductor Bias

Formalizes Section 5.1, Proposition 5.1(i)–(ii) and equations (5.1)–(5.3) of the manuscript:
- `coreNat_mul_sqPartNat_sq`: `m = core(m) * sqPart(m)^2` with `core(m)` square-free
- `eq_5_1_midpoint_decomp`: `X₁ - 1 = δ₁^{mid} u_n^2`, `X₁ + 1 = δ₂^{mid} v_n^2`, `δ₂^{mid} v_n^2 - δ₁^{mid} u_n^2 = 2`
- `prop_5_1_part1`: coprime factorization `δ₁^{mid*} δ₂^{mid*} = q_n^*`, `δ_min < √(q_n^*) ≤ √q_n`,
  and Perron continued-fraction midpoint symmetry `Q_M^* = 2^a δ_{i_n}^{mid} < 2√q_n`
- `psi_eval_upper_half`: for `p ∈ (n/2, n]`, `ψ_i(p) = 0` if `p ∣ δ_i^{mid}` and `+1` otherwise
- `prop_5_1_part2_bias`: unconditional one-sided bias `∑_{p ∈ (n/2, n]} ψ_min(p) log p ≥ ((1 - log 2)/2 - o(1)) n`
-/

set_option maxHeartbeats 400000

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard

/-! ### Core & Odd-Part Arithmetic Helpers -/

lemma padicValNat_pow_eq {p a k : ℕ} [Fact p.Prime] :
    padicValNat p (a ^ k) = k * padicValNat p a := by
  rw [← Nat.factorization_def _ Fact.out, Nat.factorization_pow, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul, Nat.factorization_def _ Fact.out]

lemma padicValNat_prod_eq {ι : Type*} {p : ℕ} [Fact p.Prime] {s : Finset ι} {f : ι → ℕ}
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  rw [← Nat.factorization_def _ Fact.out, Nat.factorization_prod hf, Finsupp.coe_finset_sum,
      Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.factorization_def (f i) Fact.out


lemma coreNat_pos (m : ℕ) : 0 < coreNat m := by
  unfold coreNat
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

lemma sqPartNat_pos (m : ℕ) : 0 < sqPartNat m := by
  unfold sqPartNat
  exact Finset.prod_pos (fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)

lemma coreNat_squarefree (m : ℕ) : Squarefree (coreNat m) := by
  unfold coreNat
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hne : coreNat m ≠ 0 := (coreNat_pos m).ne'
  haveI : Fact p.Prime := ⟨hp⟩
  have hval := padicValNat_prod_eq (p := p)
    (s := m.primeFactors.filter (fun q => padicValNat q m % 2 = 1))
    (f := fun q => q)
    (fun q hq => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).ne_zero)
  have h2_le : 2 ≤ padicValNat p (coreNat m) := by
    exact (padicValNat_dvd_iff_le hne).mp (by simpa [sq] using hpp)
  have hle1 : padicValNat p (coreNat m) ≤ 1 := by
    unfold coreNat at hval ⊢
    rw [hval]
    have hsum : ∑ q ∈ m.primeFactors.filter (fun q => padicValNat q m % 2 = 1), padicValNat p q ≤
        ∑ q ∈ ({p} : Finset ℕ), padicValNat p q := by
      by_cases hmem : p ∈ m.primeFactors.filter (fun q => padicValNat q m % 2 = 1)
      · rw [Finset.sum_eq_single p]
        · simp
        · intro q hq hqp
          have hq_pr : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
          exact padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm)
        · intro habs; exact absurd hmem habs
      · rw [Finset.sum_eq_zero]
        · simp
        · intro q hq
          have hqp : q ≠ p := fun h => hmem (h ▸ hq)
          have hq_pr : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
          exact padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm)
    simpa [padicValNat_self] using hsum
  omega

lemma padicValNat_coreNat {m p : ℕ} (hp : p.Prime) (hm : 0 < m) :
    padicValNat p (coreNat m) = if padicValNat p m % 2 = 1 then 1 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold coreNat
  rw [padicValNat_prod_eq (fun q hq => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).ne_zero)]
  split_ifs with hodd
  · have hmem : p ∈ m.primeFactors.filter (fun q => padicValNat q m % 2 = 1) := by
      refine Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, ?_, hm.ne'⟩, hodd⟩
      simpa using (padicValNat_dvd_iff_le hm.ne').mpr (by omega : 1 ≤ padicValNat p m)
    rw [Finset.sum_eq_single p]
    · exact padicValNat_self
    · intro q hq hqp
      have hq_pr : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
      exact padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm)
    · intro habs; exact absurd hmem habs
  · apply Finset.sum_eq_zero
    intro q hq
    have hq_odd := (Finset.mem_filter.mp hq).2
    have hqp : q ≠ p := fun h => hodd (h ▸ hq_odd)
    have hq_pr : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    exact padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm)

lemma padicValNat_sqPartNat {m p : ℕ} (hp : p.Prime) :
    padicValNat p (sqPartNat m) = padicValNat p m / 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold sqPartNat
  rw [padicValNat_prod_eq (fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero)]
  by_cases hmem : p ∈ m.primeFactors
  · rw [Finset.sum_eq_single p]
    · rw [padicValNat_pow_eq, padicValNat_self, mul_one]
    · intro q hq hqp
      have hq_pr : q.Prime := Nat.prime_of_mem_primeFactors hq
      rw [padicValNat_pow_eq,
          padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm),
          mul_zero]
    · intro habs; exact absurd hmem habs
  · have hv0 : padicValNat p m = 0 := by
      by_cases hm0 : m = 0
      · subst hm0; simp
      · exact padicValNat.eq_zero_of_not_dvd (fun hd => hmem (Nat.mem_primeFactors.mpr ⟨hp, hd, hm0⟩))
    rw [hv0, Nat.zero_div]
    apply Finset.sum_eq_zero
    intro q hq
    have hqp : q ≠ p := fun h => hmem (h ▸ hq)
    have hq_pr : q.Prime := Nat.prime_of_mem_primeFactors hq
    rw [padicValNat_pow_eq,
        padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm),
        mul_zero]

theorem coreNat_mul_sqPartNat_sq {m : ℕ} (hm : 0 < m) :
    coreNat m * (sqPartNat m) ^ 2 = m := by
  have h_lhs : coreNat m * (sqPartNat m) ^ 2 ≠ 0 :=
    mul_ne_zero (coreNat_pos m).ne' (pow_ne_zero 2 (sqPartNat_pos m).ne')
  apply Nat.eq_of_factorization_eq h_lhs hm.ne'
  intro p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp, Nat.factorization_def m hp]
    rw [padicValNat.mul (coreNat_pos m).ne' (pow_ne_zero 2 (sqPartNat_pos m).ne'),
        padicValNat_pow_eq,
        padicValNat_coreNat hp hm, padicValNat_sqPartNat hp]
    split_ifs <;> omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma oddPartNat_pos {m : ℕ} (hm : 0 < m) : 0 < oddPartNat m := by
  unfold oddPartNat
  have hdvd : 2 ^ padicValNat 2 m ∣ m := pow_padicValNat_dvd
  exact Nat.div_pos (Nat.le_of_dvd hm hdvd) (pow_pos (by norm_num) _)

lemma oddPartNat_mul_two_pow {m : ℕ} (hm : 0 < m) :
    oddPartNat m * 2 ^ padicValNat 2 m = m :=
  Nat.div_mul_cancel pow_padicValNat_dvd

lemma oddPartNat_not_dvd_two {m : ℕ} (hm : 0 < m) : ¬ 2 ∣ oddPartNat m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hdvd
  have h1 : 2 ^ (padicValNat 2 m + 1) ∣ m := by
    calc 2 ^ (padicValNat 2 m + 1) = 2 * 2 ^ padicValNat 2 m := pow_succ' 2 _
      _ ∣ oddPartNat m * 2 ^ padicValNat 2 m := mul_dvd_mul_right hdvd _
      _ = m := oddPartNat_mul_two_pow hm
  have h2 : padicValNat 2 m + 1 ≤ padicValNat 2 m :=
    (padicValNat_dvd_iff_le hm.ne').mp h1
  omega

lemma oddPartNat_le {m : ℕ} : oddPartNat m ≤ m :=
  Nat.div_le_self _ _

lemma oddPartNat_dvd {m : ℕ} : oddPartNat m ∣ m := by
  unfold oddPartNat
  exact Nat.div_dvd_of_dvd pow_padicValNat_dvd

lemma oddPartNat_squarefree {m : ℕ} (hm : Squarefree m) : Squarefree (oddPartNat m) :=
  hm.squarefree_of_dvd oddPartNat_dvd

lemma padicValNat_oddPartNat {m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 0 < m) :
    padicValNat p (oddPartNat m) = padicValNat p m := by
  haveI : Fact p.Prime := ⟨hp⟩
  have heq := congrArg (padicValNat p) (oddPartNat_mul_two_pow hm)
  rw [padicValNat.mul (oddPartNat_pos hm).ne' (pow_ne_zero _ (by norm_num)),
      padicValNat.eq_zero_of_not_dvd (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)))] at heq
  omega

/-! ### Midpoint Core Definitions (Eq. 5.1) -/

/-- `δ₁^{mid}(n) = core(X₁(q_n) - 1)` (eq. 5.1). -/
def delta1Mid (X₁ : ℕ) : ℕ := coreNat (X₁ - 1)

/-- `δ₂^{mid}(n) = core(X₁(q_n) + 1)` (eq. 5.1). -/
def delta2Mid (X₁ : ℕ) : ℕ := coreNat (X₁ + 1)

/-- `u_n = sqPart(X₁(q_n) - 1)` (eq. 5.1). -/
def uMid (X₁ : ℕ) : ℕ := sqPartNat (X₁ - 1)

/-- `v_n = sqPart(X₁(q_n) + 1)` (eq. 5.1). -/
def vMid (X₁ : ℕ) : ℕ := sqPartNat (X₁ + 1)

/-- Odd part `δ₁^{mid*}(n)` (Proposition 5.1). -/
def delta1MidStar (X₁ : ℕ) : ℕ := oddPartNat (delta1Mid X₁)

/-- Odd part `δ₂^{mid*}(n)` (Proposition 5.1). -/
def delta2MidStar (X₁ : ℕ) : ℕ := oddPartNat (delta2Mid X₁)

/-- `δ_min(n) = min(δ₁^{mid*}(n), δ₂^{mid*}(n))` (eq. 5.2). -/
def deltaMin (X₁ : ℕ) : ℕ := min (delta1MidStar X₁) (delta2MidStar X₁)

lemma X1_gt_one {D X₁ Y₁ : ℕ} (hD : 2 ≤ D) (hfund : IsFundamentalPell D X₁ Y₁) : 1 < X₁ := by
  rcases hfund with ⟨_, hY1, hEq, _⟩
  have : 1 < D * Y₁ ^ 2 + 1 := by nlinarith
  nlinarith

lemma eq_5_1_midpoint_decomp {D X₁ Y₁ : ℕ} (hD : 2 ≤ D) (hfund : IsFundamentalPell D X₁ Y₁) :
    X₁ - 1 = delta1Mid X₁ * (uMid X₁) ^ 2 ∧
    X₁ + 1 = delta2Mid X₁ * (vMid X₁) ^ 2 ∧
    (delta2Mid X₁ : ℤ) * (vMid X₁ : ℤ) ^ 2 - (delta1Mid X₁ : ℤ) * (uMid X₁ : ℤ) ^ 2 = 2 := by
  have hX1 : 1 < X₁ := X1_gt_one hD hfund
  have h1 : delta1Mid X₁ * (uMid X₁) ^ 2 = X₁ - 1 := coreNat_mul_sqPartNat_sq (by omega)
  have h2 : delta2Mid X₁ * (vMid X₁) ^ 2 = X₁ + 1 := coreNat_mul_sqPartNat_sq (by omega)
  refine ⟨h1.symm, h2.symm, ?_⟩
  have h1z : (delta1Mid X₁ : ℤ) * (uMid X₁ : ℤ) ^ 2 = ((X₁ - 1 : ℕ) : ℤ) := by exact_mod_cast h1
  have h2z : (delta2Mid X₁ : ℤ) * (vMid X₁ : ℤ) ^ 2 = (X₁ : ℤ) + 1 := by exact_mod_cast h2
  rw [Nat.cast_sub hX1.le] at h1z
  push_cast at h1z
  linarith

lemma q_n_ge_two {n : ℕ} (hn : 2 ≤ n) : 2 ≤ q_n n := by
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  have hp_le_n : p ≤ n := le_trans hhi (by rw [mul_comm]; exact Nat.div_mul_le_self n 2)
  have hpn : p ∈ Podd n := by
    unfold Podd
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hp_le_n⟩, hp, ?_⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hv : padicValNat p (Nat.factorial n) = n / p := by
      apply padicValNat_factorial_eq_div_of_lt_sq hp
      have hlt : n < 2 * p := by omega
      have hp2 : 2 ≤ p := hp.two_le
      nlinarith
    have h1p : 1 * p ≤ n := by omega
    have h2p : n < (1 + 1) * p := by omega
    rw [hv, Nat.div_eq_of_lt_le h1p h2p]
    omega
  have hdvd : p ∣ q_n n := Finset.dvd_prod_of_mem _ hpn
  have hpos : 0 < q_n n := (q_n_squarefree n).ne_zero |> Nat.pos_of_ne_zero
  exact le_trans hp.two_le (Nat.le_of_dvd hpos hdvd)

lemma oddPartNat_q_n_gt_one {n : ℕ} (hn : 8 ≤ n) : 1 < oddPartNat (q_n n) := by
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  have hp_le_n : p ≤ n := le_trans hhi (by rw [mul_comm]; exact Nat.div_mul_le_self n 2)
  have hp2 : p ≠ 2 := by omega
  have hmem : p ∈ Podd n := (prime_in_upper_half_dvd_q_n hp hlo hp_le_n).1
  have hdvd_q : p ∣ q_n n := Finset.dvd_prod_of_mem _ hmem
  have hq_pos : 0 < q_n n := (q_n_squarefree n).ne_zero |> Nat.pos_of_ne_zero
  have hdvd_odd : p ∣ oddPartNat (q_n n) := by
    have hcop : Nat.Coprime p (2 ^ padicValNat 2 (q_n n)) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have hmul : p ∣ oddPartNat (q_n n) * 2 ^ padicValNat 2 (q_n n) := by
      rwa [oddPartNat_mul_two_pow hq_pos]
    exact hcop.dvd_of_dvd_mul_right hmul
  exact lt_of_lt_of_le (by omega) (Nat.le_of_dvd (oddPartNat_pos hq_pos) hdvd_odd)

/-! ### Proposition 5.1(i): Coprime Factorization, √q_n Bound, and Perron Midpoint Symmetry -/

theorem delta1MidStar_mul_delta2MidStar_eq {n X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁) :
    delta1MidStar X₁ * delta2MidStar X₁ = oddPartNat (q_n n) ∧
    Nat.Coprime (delta1MidStar X₁) (delta2MidStar X₁) ∧
    delta1MidStar X₁ ≠ delta2MidStar X₁ := by
  have hq_ge : 2 ≤ q_n n := q_n_ge_two (by omega)
  have hq_pos : 0 < q_n n := by omega
  have hX1 : 1 < X₁ := X1_gt_one hq_ge hfund
  have h1_pos : 0 < delta1Mid X₁ := coreNat_pos _
  have h2_pos : 0 < delta2Mid X₁ := coreNat_pos _
  have h1s_pos : 0 < delta1MidStar X₁ := oddPartNat_pos h1_pos
  have h2s_pos : 0 < delta2MidStar X₁ := oddPartNat_pos h2_pos
  have hqs_pos : 0 < oddPartNat (q_n n) := oddPartNat_pos hq_pos
  have h_prod : delta1MidStar X₁ * delta2MidStar X₁ = oddPartNat (q_n n) := by
    apply Nat.eq_of_factorization_eq (mul_pos h1s_pos h2s_pos).ne' hqs_pos.ne'
    intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
      rw [padicValNat.mul h1s_pos.ne' h2s_pos.ne']
      by_cases hp2 : p = 2
      · subst hp2
        have hnd1 : ¬ 2 ∣ delta1MidStar X₁ := oddPartNat_not_dvd_two h1_pos
        have hnd2 : ¬ 2 ∣ delta2MidStar X₁ := oddPartNat_not_dvd_two h2_pos
        have hndq : ¬ 2 ∣ oddPartNat (q_n n) := oddPartNat_not_dvd_two hq_pos
        rw [padicValNat.eq_zero_of_not_dvd hnd1, padicValNat.eq_zero_of_not_dvd hnd2,
            padicValNat.eq_zero_of_not_dvd hndq]
      · unfold delta1MidStar delta2MidStar
        rw [padicValNat_oddPartNat hp hp2 h1_pos, padicValNat_oddPartNat hp hp2 h2_pos,
            padicValNat_oddPartNat hp hp2 hq_pos]
        unfold delta1Mid delta2Mid
        rw [padicValNat_coreNat hp (by omega), padicValNat_coreNat hp (by omega)]
        have hdiff : (X₁ - 1) * (X₁ + 1) = q_n n * Y₁ ^ 2 := by
          zify [hX1.le]
          have : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
          linarith
        have hv_eq := congrArg (padicValNat p) hdiff
        rw [padicValNat.mul (by omega) (by omega),
            padicValNat.mul hq_pos.ne' (pow_ne_zero 2 hfund.2.1.ne'),
            padicValNat_pow_eq] at hv_eq
        have h_not_both : padicValNat p (X₁ - 1) = 0 ∨ padicValNat p (X₁ + 1) = 0 := by
          by_contra hboth
          push_neg at hboth
          have hd1 : p ∣ X₁ - 1 := by simpa using (padicValNat_dvd_iff_le (by omega)).mpr (Nat.pos_of_ne_zero hboth.1)
          have hd2 : p ∣ X₁ + 1 := by simpa using (padicValNat_dvd_iff_le (by omega)).mpr (Nat.pos_of_ne_zero hboth.2)
          have hd_sub : p ∣ (X₁ + 1) - (X₁ - 1) := Nat.dvd_sub hd2 hd1
          have h2eq : (X₁ + 1) - (X₁ - 1) = 2 := by omega
          rw [h2eq] at hd_sub
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd_sub)
        have hq_le1 : padicValNat p (q_n n) ≤ 1 := by
          by_contra hgt
          have hp2_dvd : p * p ∣ q_n n := by
            rw [← sq]
            exact dvd_trans (pow_dvd_pow p (by omega : 2 ≤ padicValNat p (q_n n))) pow_padicValNat_dvd
          exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp (by simpa [sq] using hp2_dvd)
        rcases h_not_both with h0 | h0 <;> rw [h0] at hv_eq ⊢ <;> split_ifs at * <;> omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hsf : Squarefree (delta1MidStar X₁ * delta2MidStar X₁) := by
    rw [h_prod]; exact oddPartNat_squarefree (q_n_squarefree n)
  have hcop : Nat.Coprime (delta1MidStar X₁) (delta2MidStar X₁) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1d : p ∣ delta1MidStar X₁ := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
    have h2d : p ∣ delta2MidStar X₁ := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
    exact (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp (mul_dvd_mul h1d h2d)
  have hne_delta : delta1MidStar X₁ ≠ delta2MidStar X₁ := by
    intro heq
    have hgt1 : 1 < oddPartNat (q_n n) := oddPartNat_q_n_gt_one hn
    rw [← h_prod, heq] at hgt1
    have h2_gt1 : 1 < delta2MidStar X₁ := by nlinarith
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h2_gt1.ne'
    have hsq : p * p ∣ delta1MidStar X₁ * delta2MidStar X₁ := by
      rw [heq]; exact mul_dvd_mul hpdvd hpdvd
    exact (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp hsq
  exact ⟨h_prod, hcop, hne_delta⟩

/-- **Proposition 5.1(i)**: Coprime factorization, `δ_min(n) < √(q_n^*) ≤ √q_n` (eq. 5.2),
and Perron's continued-fraction midpoint symmetry for `n ≥ 8`. -/
theorem prop_5_1_part1 {n X₁ Y₁ : ℕ} (hn : 8 ≤ n) (hfund : IsFundamentalPell (q_n n) X₁ Y₁) :
    delta1MidStar X₁ * delta2MidStar X₁ = oddPartNat (q_n n) ∧
    Nat.Coprime (delta1MidStar X₁) (delta2MidStar X₁) ∧
    delta1MidStar X₁ ≠ delta2MidStar X₁ ∧
    (deltaMin X₁ : ℝ) < Real.sqrt (oddPartNat (q_n n) : ℝ) ∧
    Real.sqrt (oddPartNat (q_n n) : ℝ) ≤ Real.sqrt (q_n n : ℝ) ∧
    Nonempty (CFMidpointData (q_n n) X₁ Y₁) := by
  obtain ⟨hprod, hcop, hne⟩ := delta1MidStar_mul_delta2MidStar_eq hn hfund
  have hmin_sq : (deltaMin X₁ : ℝ) ^ 2 < (oddPartNat (q_n n) : ℝ) := by
    have h12 : deltaMin X₁ ^ 2 < delta1MidStar X₁ * delta2MidStar X₁ := by
      unfold deltaMin
      rcases lt_trichotomy (delta1MidStar X₁) (delta2MidStar X₁) with hlt | heq | hgt
      · rw [min_eq_left hlt.le, sq]
        exact Nat.mul_lt_mul_of_pos_left hlt (oddPartNat_pos (coreNat_pos (X₁ - 1)))
      · exact absurd heq hne
      · rw [min_eq_right hgt.le, sq]
        exact Nat.mul_lt_mul_of_pos_right hgt (oddPartNat_pos (coreNat_pos (X₁ + 1)))
    rw [hprod] at h12
    exact_mod_cast h12
  have hmin_lt : (deltaMin X₁ : ℝ) < Real.sqrt (oddPartNat (q_n n) : ℝ) := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg _)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hmin_sq
  have hsqrt_le : Real.sqrt (oddPartNat (q_n n) : ℝ) ≤ Real.sqrt (q_n n : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (oddPartNat_le (m := q_n n))
  have hcf : Nonempty (CFMidpointData (q_n n) X₁ Y₁) := by
    have hnsq : ¬ IsSquare (q_n n) := by
      intro ⟨r, hr⟩
      have hq_ge : 2 ≤ q_n n := q_n_ge_two (by omega)
      have hr_ge : 2 ≤ r := by nlinarith
      obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd (by omega : r ≠ 1)
      have hpp : p * p ∣ q_n n := by rw [hr]; exact mul_dvd_mul hpr hpr
      exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp hpp
    have hn3 : 3 ≤ n := by omega
    have hn6 : n ≠ 6 := by omega
    obtain ⟨p, hp, hpq, hpmod⟩ := q_n_has_prime_mod4 hn3 hn6
    exact perron_cf_midpoint_symmetry (q_n n) X₁ Y₁ hnsq hfund (neg_pell_no_int_sol hp hpq hpmod)
  exact ⟨hprod, hcop, hne, hmin_lt, hsqrt_le, hcf⟩

/-! ### Proposition 5.1(ii): Character Bias on `I₁ = (n/2, n]` (Eq. 5.3) -/

/-- `ψ₁(p) = (-2 δ₁^{mid}(n) / p)`. -/
def psi1 (X₁ p : ℕ) : ℤ := chiLegendre (-2 * (delta1Mid X₁ : ℤ)) p

/-- `ψ₂(p) = (2 δ₂^{mid}(n) / p)`. -/
def psi2 (X₁ p : ℕ) : ℤ := chiLegendre (2 * (delta2Mid X₁ : ℤ)) p

/-- `ψ_min` is the character among `{ψ₁, ψ₂}` corresponding to `δ_min(n)`. -/
def psiMin (X₁ p : ℕ) : ℤ :=
  if delta1MidStar X₁ ≤ delta2MidStar X₁ then psi1 X₁ p else psi2 X₁ p

private lemma legendreSym_eq_one_of_sq_mul' {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a z : ℤ}
    (hz : (z : ZMod p) ≠ 0) (ha : (a : ZMod p) * (z : ZMod p) ^ 2 = (2 : ZMod p) ^ 2) :
    legendreSym p a = 1 := by
  have hsq : IsSquare (a : ZMod p) := by
    refine ⟨2 * (z : ZMod p)⁻¹, ?_⟩
    have hinv : (z : ZMod p) * (z : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hz
    calc (a : ZMod p) = (a : ZMod p) * ((z : ZMod p) * (z : ZMod p)⁻¹) ^ 2 := by rw [hinv, one_pow, mul_one]
      _ = ((a : ZMod p) * (z : ZMod p) ^ 2) * ((z : ZMod p)⁻¹) ^ 2 := by ring
      _ = (2 : ZMod p) ^ 2 * ((z : ZMod p)⁻¹) ^ 2 := by rw [ha]
      _ = (2 * (z : ZMod p)⁻¹) * (2 * (z : ZMod p)⁻¹) := by ring
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at ha
    have h4 : ((4 : ℕ) : ZMod p) = 0 := by
      have : (2 : ZMod p) ^ 2 = ((4 : ℕ) : ZMod p) := by norm_num
      rw [← this, ← ha]
    rw [ZMod.natCast_eq_zero_iff] at h4
    have hd2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow (show p ∣ 2 ^ 2 from by simpa using h4)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd2)
  exact (legendreSym.eq_one_iff p ha0).mpr hsq

/-- On `p ∈ (n/2, n]` (`n ≥ 8`), `ψ₁(p)` and `ψ₂(p)` satisfy `ψ_i(p) = 0` if `p ∣ δ_i^{mid}`
and `ψ_i(p) = 1` if `p ∤ δ_i^{mid}`. -/
theorem psi_eval_upper_half {n X₁ Y₁ p : ℕ} (hn : 8 ≤ n)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hp : p.Prime) (hlo : n / 2 < p) (hhi : p ≤ n) :
    (psi1 X₁ p = if p ∣ delta1Mid X₁ then 0 else 1) ∧
    (psi2 X₁ p = if p ∣ delta2Mid X₁ then 0 else 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hq_ge : 2 ≤ q_n n := q_n_ge_two (by omega)
  have ⟨_, _, hdiff⟩ := eq_5_1_midpoint_decomp hq_ge hfund
  have ⟨hprod, hcop, _⟩ := delta1MidStar_mul_delta2MidStar_eq hn hfund
  have hp_q : p ∣ q_n n := (prime_in_upper_half_dvd_q_n hp hlo hhi).2
  have hp_q_star : p ∣ oddPartNat (q_n n) := by
    have hq_pos : 0 < q_n n := (q_n_squarefree n).ne_zero |> Nat.pos_of_ne_zero
    have hcop2 : Nat.Coprime p (2 ^ padicValNat 2 (q_n n)) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    rw [← oddPartNat_mul_two_pow hq_pos] at hp_q
    exact hcop2.dvd_of_dvd_mul_right hp_q
  rw [← hprod] at hp_q_star
  have hp_dvd_1_or_2 : p ∣ delta1Mid X₁ ∨ p ∣ delta2Mid X₁ := by
    rcases hp.dvd_mul.mp hp_q_star with h1 | h2
    · exact Or.inl (dvd_trans h1 oddPartNat_dvd)
    · exact Or.inr (dvd_trans h2 oddPartNat_dvd)
  have hp_not_both : ¬ (p ∣ delta1Mid X₁ ∧ p ∣ delta2Mid X₁) := by
    rintro ⟨h1, h2⟩
    have h1s : p ∣ delta1MidStar X₁ := by
      unfold delta1MidStar
      have hcop2 : Nat.Coprime p (2 ^ padicValNat 2 (delta1Mid X₁)) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      have hm1 := oddPartNat_mul_two_pow (coreNat_pos (X₁ - 1))
      change oddPartNat (delta1Mid X₁) * _ = delta1Mid X₁ at hm1
      rw [← hm1] at h1
      exact hcop2.dvd_of_dvd_mul_right h1
    have h2s : p ∣ delta2MidStar X₁ := by
      unfold delta2MidStar
      have hcop2 : Nat.Coprime p (2 ^ padicValNat 2 (delta2Mid X₁)) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      have hm2 := oddPartNat_mul_two_pow (coreNat_pos (X₁ + 1))
      change oddPartNat (delta2Mid X₁) * _ = delta2Mid X₁ at hm2
      rw [← hm2] at h2
      exact hcop2.dvd_of_dvd_mul_right h2
    have hpg : p ∣ Nat.gcd (delta1MidStar X₁) (delta2MidStar X₁) := Nat.dvd_gcd h1s h2s
    rw [hcop.gcd_eq_one] at hpg
    exact hp.ne_one (Nat.dvd_one.mp hpg)
  unfold psi1 psi2 chiLegendre
  simp only [dif_pos hp]
  rcases hp_dvd_1_or_2 with h1 | h2
  · have h2_nd : ¬ p ∣ delta2Mid X₁ := fun h => hp_not_both ⟨h1, h⟩
    rw [if_pos h1, if_neg h2_nd]
    constructor
    · rw [legendreSym.eq_zero_iff]
      have hd1_z : ((delta1Mid X₁ : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (by exact_mod_cast h1)
      push_cast at hd1_z ⊢
      rw [hd1_z]; norm_num
    · have hv_nd : ¬ p ∣ vMid X₁ := by
        intro hv
        have ⟨h_eq1, h_eq2, _⟩ := eq_5_1_midpoint_decomp hq_ge hfund
        have h_dvd_X1p1 : p ∣ X₁ + 1 := h_eq2 ▸ dvd_mul_of_dvd_right (dvd_pow hv (by norm_num)) _
        have h_dvd_X1m1 : p ∣ X₁ - 1 := h_eq1 ▸ dvd_mul_of_dvd_left h1 _
        have h_dvd_2 : p ∣ (X₁ + 1) - (X₁ - 1) := Nat.dvd_sub h_dvd_X1p1 h_dvd_X1m1
        have hX1 : 1 < X₁ := X1_gt_one hq_ge hfund
        have : (X₁ + 1) - (X₁ - 1) = 2 := by omega
        rw [this] at h_dvd_2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h_dvd_2)
      have hv_z : ((vMid X₁ : ℤ) : ZMod p) ≠ 0 := by
        intro hz
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
        exact hv_nd (by exact_mod_cast hz)
      have hmod : ((2 * (delta2Mid X₁ : ℤ) : ℤ) : ZMod p) * ((vMid X₁ : ℤ) : ZMod p) ^ 2 = (2 : ZMod p) ^ 2 := by
        have h1_mod : (delta1Mid X₁ : ZMod p) = 0 := by
          simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (delta1Mid X₁ : ℤ) p).mpr (by exact_mod_cast h1)
        have hdiff_mod := congrArg (Int.cast (R := ZMod p)) hdiff
        push_cast at hdiff_mod
        rw [h1_mod, zero_mul, sub_zero] at hdiff_mod
        calc ((2 * (delta2Mid X₁ : ℤ) : ℤ) : ZMod p) * ((vMid X₁ : ℤ) : ZMod p) ^ 2
            = 2 * ((delta2Mid X₁ : ZMod p) * (vMid X₁ : ZMod p) ^ 2) := by push_cast; ring
          _ = 2 * 2 := by rw [hdiff_mod]
          _ = (2 : ZMod p) ^ 2 := by ring
      exact legendreSym_eq_one_of_sq_mul' hp2 hv_z hmod
  · have h1_nd : ¬ p ∣ delta1Mid X₁ := fun h => hp_not_both ⟨h, h2⟩
    rw [if_neg h1_nd, if_pos h2]
    constructor
    · have hu_nd : ¬ p ∣ uMid X₁ := by
        intro hu
        have ⟨h_eq1, h_eq2, _⟩ := eq_5_1_midpoint_decomp hq_ge hfund
        have h_dvd_X1m1 : p ∣ X₁ - 1 := h_eq1 ▸ dvd_mul_of_dvd_right (dvd_pow hu (by norm_num)) _
        have h_dvd_X1p1 : p ∣ X₁ + 1 := h_eq2 ▸ dvd_mul_of_dvd_left h2 _
        have h_dvd_2 : p ∣ (X₁ + 1) - (X₁ - 1) := Nat.dvd_sub h_dvd_X1p1 h_dvd_X1m1
        have hX1 : 1 < X₁ := X1_gt_one hq_ge hfund
        have : (X₁ + 1) - (X₁ - 1) = 2 := by omega
        rw [this] at h_dvd_2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h_dvd_2)
      have hu_z : ((uMid X₁ : ℤ) : ZMod p) ≠ 0 := by
        intro hz
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
        exact hu_nd (by exact_mod_cast hz)
      have hmod : ((-2 * (delta1Mid X₁ : ℤ) : ℤ) : ZMod p) * ((uMid X₁ : ℤ) : ZMod p) ^ 2 = (2 : ZMod p) ^ 2 := by
        have h2_mod : (delta2Mid X₁ : ZMod p) = 0 := by
          simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (delta2Mid X₁ : ℤ) p).mpr (by exact_mod_cast h2)
        have hdiff_mod := congrArg (Int.cast (R := ZMod p)) hdiff
        push_cast at hdiff_mod
        rw [h2_mod, zero_mul, zero_sub] at hdiff_mod
        calc ((-2 * (delta1Mid X₁ : ℤ) : ℤ) : ZMod p) * ((uMid X₁ : ℤ) : ZMod p) ^ 2
            = 2 * (-((delta1Mid X₁ : ZMod p) * (uMid X₁ : ZMod p) ^ 2)) := by push_cast; ring
          _ = 2 * 2 := by rw [hdiff_mod]
          _ = (2 : ZMod p) ^ 2 := by ring
      exact legendreSym_eq_one_of_sq_mul' hp2 hu_z hmod
    · rw [legendreSym.eq_zero_iff]
      have hd2_z : ((delta2Mid X₁ : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (by exact_mod_cast h2)
      push_cast at hd2_z ⊢
      rw [hd2_z]; norm_num

/-- **Proposition 5.1(ii)**: Exact identity and unconditional one-sided bias for `ψ_min` on `I₁ = (n/2, n]`
(eq. 5.3). -/
theorem prop_5_1_part2_identity {n X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁) :
    (∑ p ∈ (Finset.Ioc (n / 2) n).filter Nat.Prime, (psiMin X₁ p : ℝ) * Real.log (p : ℝ)) =
      (∑ p ∈ (Finset.Ioc (n / 2) n).filter Nat.Prime, Real.log (p : ℝ)) -
      (∑ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ p ∣ deltaMin X₁), Real.log (p : ℝ)) := by
  have hterm : ∀ p ∈ (Finset.Ioc (n / 2) n).filter Nat.Prime,
      (psiMin X₁ p : ℝ) * Real.log (p : ℝ) =
      Real.log (p : ℝ) - if p ∣ deltaMin X₁ then Real.log (p : ℝ) else 0 := by
    intro p hp_mem
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp_mem
    rcases hp_mem with ⟨⟨hlo, hhi⟩, hp⟩
    have hp2 : p ≠ 2 := by omega
    have ⟨h1, h2⟩ := psi_eval_upper_half hn hfund hp hlo hhi
    unfold psiMin deltaMin
    by_cases hle : delta1MidStar X₁ ≤ delta2MidStar X₁
    · rw [if_pos hle, min_eq_left hle, h1]
      have hdvd_iff : p ∣ delta1MidStar X₁ ↔ p ∣ delta1Mid X₁ := by
        constructor
        · intro h; exact dvd_trans h oddPartNat_dvd
        · intro h
          unfold delta1MidStar
          have hcop2 : Nat.Coprime p (2 ^ padicValNat 2 (delta1Mid X₁)) :=
            Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
          have hm1 := oddPartNat_mul_two_pow (coreNat_pos (X₁ - 1))
          change oddPartNat (delta1Mid X₁) * _ = delta1Mid X₁ at hm1
          rw [← hm1] at h
          exact hcop2.dvd_of_dvd_mul_right h
      simp only [hdvd_iff]
      split_ifs <;> simp
    · rw [if_neg hle, min_eq_right (le_of_not_ge hle), h2]
      have hdvd_iff : p ∣ delta2MidStar X₁ ↔ p ∣ delta2Mid X₁ := by
        constructor
        · intro h; exact dvd_trans h oddPartNat_dvd
        · intro h
          unfold delta2MidStar
          have hcop2 : Nat.Coprime p (2 ^ padicValNat 2 (delta2Mid X₁)) :=
            Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
          have hm2 := oddPartNat_mul_two_pow (coreNat_pos (X₁ + 1))
          change oddPartNat (delta2Mid X₁) * _ = delta2Mid X₁ at hm2
          rw [← hm2] at h
          exact hcop2.dvd_of_dvd_mul_right h
      simp only [hdvd_iff]
      split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  tauto

/-- **Proposition 5.1(ii) asymptotic lower bound (eq. 5.3)**:
For every `ε > 0`, for all sufficiently large `n`,
`∑_{p ∈ (n/2, n]} ψ_min(p) log p ≥ ((1 - log 2)/2 - ε) * n`. -/
theorem prop_5_1_part2_bias (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n X₁ Y₁ : ℕ, N₀ ≤ n →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      ((1 - Real.log 2) / 2 - ε) * (n : ℝ) ≤
        ∑ p ∈ (Finset.Ioc (n / 2) n).filter Nat.Prime, (psiMin X₁ p : ℝ) * Real.log (p : ℝ) := by
  obtain ⟨c₁, hc₁, hθ⟩ := de_la_vallee_poussin_theta
  obtain ⟨c₀, hc₀, hq_asym⟩ := log_q_n_asymptotic
  rw [Asymptotics.isBigO_iff] at hθ
  obtain ⟨Cθ, hθ_ev⟩ := hθ
  rw [Filter.eventually_atTop] at hθ_ev
  obtain ⟨M1, hM1⟩ := hθ_ev
  have hθ_exp_tend : Filter.Tendsto (fun x : ℝ => Cθ * Real.exp (-c₁ * Real.sqrt (Real.log x)))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => -c₁ * Real.sqrt (Real.log x)) Filter.atTop Filter.atBot :=
      Filter.Tendsto.const_mul_atTop_of_neg (by linarith) (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul Cθ
  rw [Metric.tendsto_atTop] at hθ_exp_tend
  obtain ⟨X1, hX1⟩ := hθ_exp_tend (ε / 6) (by linarith)
  rw [Asymptotics.isBigO_iff] at hq_asym
  obtain ⟨C, hq_ev⟩ := hq_asym
  rw [Filter.eventually_atTop] at hq_ev
  obtain ⟨M2, hM2⟩ := hq_ev
  have h_exp_tend : Filter.Tendsto (fun n : ℕ => C * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Filter.Tendsto (fun n : ℕ => -c₀ * Real.sqrt (Real.log (n : ℝ))) Filter.atTop Filter.atBot :=
      Filter.Tendsto.const_mul_atTop_of_neg (by linarith) (Real.tendsto_sqrt_atTop.comp h1)
    simpa using (Real.tendsto_exp_atBot.comp h2).const_mul C
  rw [Metric.tendsto_atTop] at h_exp_tend
  obtain ⟨M3, hM3⟩ := h_exp_tend (ε / 2) (by linarith)
  obtain ⟨K1, hK1⟩ := exists_nat_gt (max (max M1 X1) 1)
  refine ⟨max (max 8 (2 * K1 + 2)) (max M2 M3), le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro n X₁ Y₁ hn hfund
  have hn8 : 8 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn_K1 : K1 ≤ n := by
    have : 2 * K1 + 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    omega
  have hn2_K1 : K1 ≤ n / 2 := by
    have : 2 * K1 + 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    omega
  have hn_M2 : M2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn_M3 : M3 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  rw [prop_5_1_part2_identity hn8 hfund]
  have hθ_bound : ∀ x : ℝ, (K1 : ℝ) ≤ x → |thetaPrime x - x| ≤ (ε / 6) * x := by
    intro x hx
    have hx_gt : max (max M1 X1) 1 < x := lt_of_lt_of_le hK1 hx
    have hx_M1 : M1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx_gt.le
    have hx_X1 : X1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx_gt.le
    have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hx_gt.le)
    have h1 := hM1 x hx_M1
    have h3 := hX1 x hx_X1
    rw [Real.dist_eq, sub_zero] at h3
    simp only [Real.norm_eq_abs] at h1
    have h_exp_nn : 0 ≤ x * Real.exp (-c₁ * Real.sqrt (Real.log x)) := by positivity
    rw [abs_of_nonneg h_exp_nn] at h1
    have h_Cθ_le : Cθ * Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤ ε / 6 :=
      le_trans (le_abs_self _) h3.le
    calc |thetaPrime x - x| ≤ Cθ * (x * Real.exp (-c₁ * Real.sqrt (Real.log x))) := h1
      _ = (Cθ * Real.exp (-c₁ * Real.sqrt (Real.log x))) * x := by ring
      _ ≤ (ε / 6) * x := mul_le_mul_of_nonneg_right h_Cθ_le hx_pos.le
  have hθ_n := hθ_bound (n : ℝ) (by exact_mod_cast hn_K1)
  have hθ_n2 := hθ_bound ((n : ℝ) / 2) (by
    have h2K : (2 : ℝ) * (K1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 * K1 ≤ n)
    linarith)
  have h_theta_diff_eq :
      (∑ p ∈ (Finset.Ioc (n / 2) n).filter Nat.Prime, Real.log (p : ℝ)) =
      thetaPrime (n : ℝ) - thetaPrime ((n : ℝ) / 2) := by
    unfold thetaPrime
    have hsub : (Finset.Icc 2 (n / 2)).filter Nat.Prime ⊆ (Finset.Icc 2 n).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.div_le_self n 2)⟩, hp.2⟩
    have hsdiff : (Finset.Icc 2 n).filter Nat.Prime \ (Finset.Icc 2 (n / 2)).filter Nat.Prime =
        (Finset.Ioc (n / 2) n).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨⟨_, hpn⟩, hp⟩, hnot⟩
        refine ⟨⟨?_, hpn⟩, hp⟩
        by_contra hle; exact hnot ⟨⟨hp.two_le, by omega⟩, hp⟩
      · rintro ⟨⟨hlo, hhi⟩, hp⟩
        exact ⟨⟨⟨hp.two_le, hhi⟩, hp⟩, fun ⟨⟨_, h2⟩, _⟩ => by omega⟩
    have h_eq1 : (Finset.filter Nat.Prime (Finset.Icc 2 ⌊(n : ℝ)⌋₊)) = (Finset.Icc 2 n).filter Nat.Prime := by
      ext p; simp [Nat.floor_natCast]
    have h_eq2 : (Finset.filter Nat.Prime (Finset.Icc 2 ⌊(n : ℝ) / 2⌋₊)) = (Finset.Icc 2 (n / 2)).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc]
      have hfl : ⌊(n : ℝ) / 2⌋₊ = n / 2 := by
        rw [Nat.floor_eq_iff (by positivity)]
        have h1 : (n / 2) * 2 ≤ n := Nat.div_mul_le_self n 2
        have h2 : n < (n / 2 + 1) * 2 := by omega
        constructor
        · have : ((n / 2 : ℕ) : ℝ) * 2 ≤ (n : ℝ) := by exact_mod_cast h1
          linarith
        · have : (n : ℝ) < ((n / 2 : ℕ) + 1) * 2 := by exact_mod_cast h2
          linarith
      rw [hfl]
    rw [h_eq1, h_eq2, ← hsdiff, eq_sub_of_add_eq (Finset.sum_sdiff hsub)]
  have h_theta_diff_lb : (1 / 2 - ε / 4) * (n : ℝ) ≤
      ∑ p ∈ (Finset.Ioc (n / 2) n).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [h_theta_diff_eq]
    have h1 := (abs_le.mp hθ_n).1
    have h2 := (abs_le.mp hθ_n2).2
    linarith
  have h_sum_dvd_le_log :
      (∑ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ p ∣ deltaMin X₁), Real.log (p : ℝ)) ≤
      Real.log (deltaMin X₁ : ℝ) := by
    have hprod_dvd : (∏ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ p ∣ deltaMin X₁), p) ∣
        deltaMin X₁ := by
      apply Finset.prod_primes_dvd
      · intro p hp; exact (Finset.mem_filter.mp hp).2.1.prime
      · intro p hp; exact (Finset.mem_filter.mp hp).2.2
    have hdmin_pos : 0 < deltaMin X₁ := by
      unfold deltaMin
      exact lt_min (oddPartNat_pos (coreNat_pos _)) (oddPartNat_pos (coreNat_pos _))
    have hprod_le_nat : (∏ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ p ∣ deltaMin X₁), p) ≤
        deltaMin X₁ := Nat.le_of_dvd hdmin_pos hprod_dvd
    have hprod_le : (∏ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ p ∣ deltaMin X₁), (p : ℝ)) ≤
        (deltaMin X₁ : ℝ) := by
      simpa only [Nat.cast_prod] using (Nat.cast_le (α := ℝ)).mpr hprod_le_nat
    have hprod_pos : 0 < ∏ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ p ∣ deltaMin X₁), (p : ℝ) :=
      Finset.prod_pos (fun p hp => by exact_mod_cast (Finset.mem_filter.mp hp).2.1.pos)
    calc (∑ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ p ∣ deltaMin X₁), Real.log (p : ℝ))
        = Real.log (∏ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ p ∣ deltaMin X₁), (p : ℝ)) := by
          rw [Real.log_prod (fun p hp => (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.ne_zero))]
      _ ≤ Real.log (deltaMin X₁ : ℝ) := Real.log_le_log hprod_pos hprod_le
  have ⟨_, _, _, hmin_lt, hsqrt_le, _⟩ := prop_5_1_part1 hn8 hfund
  have hlog_dmin_le : Real.log (deltaMin X₁ : ℝ) ≤ (1 / 2 : ℝ) * Real.log (q_n n : ℝ) := by
    have hq_pos : (0 : ℝ) < (q_n n : ℝ) := by exact_mod_cast (q_n_squarefree n).ne_zero |> Nat.pos_of_ne_zero
    have hdmin_pos : (0 : ℝ) < (deltaMin X₁ : ℝ) := by
      unfold deltaMin
      exact_mod_cast lt_min (oddPartNat_pos (coreNat_pos _)) (oddPartNat_pos (coreNat_pos _))
    calc Real.log (deltaMin X₁ : ℝ)
        ≤ Real.log (Real.sqrt (q_n n : ℝ)) := Real.log_le_log hdmin_pos (le_trans hmin_lt.le hsqrt_le)
      _ = (1 / 2 : ℝ) * Real.log (q_n n : ℝ) := by rw [Real.log_sqrt hq_pos.le]; ring
  have hq_ub : Real.log (q_n n : ℝ) ≤ (Real.log 2 + ε / 2) * (n : ℝ) := by
    have h1 := hM2 n hn_M2
    have h3 := hM3 n hn_M3
    rw [Real.dist_eq, sub_zero] at h3
    simp only [Real.norm_eq_abs] at h1
    have hC_bound : C * ((n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ)))) ≤ (ε / 2) * (n : ℝ) := by
      have h_abs : C * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) ≤ ε / 2 := le_trans (le_abs_self _) h3.le
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
    have h_exp_nonneg : 0 ≤ (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by positivity
    have h_abs_eq : |((n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))))| =
        (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := abs_of_nonneg h_exp_nonneg
    rw [h_abs_eq] at h1
    have h_sub := (abs_le.mp h1).2
    linarith
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]

end GrasGreenbergBrocard
