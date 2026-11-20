import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsSec3
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.ValuationParityThm
import GrasGreenbergBrocard.ChebyshevLucas
import GrasGreenbergBrocard.PellFundamental

/-!
# Theorem 1.1: Unconditional Collapse of the Pell Index

Formalizes Section 3.2 (Theorem 1.1, eqs. 1.6–1.7 and 3.4–3.5) of the manuscript:
- `known_k4`, `known_k5`, `known_k7`: `k(4) = 1`, `k(5) = 1`, `k(7) = 2`
- `pell_index_collapse_large`: for all sufficiently large solutions `(n, m)` to `n! + 1 = m^2`,
  the Pell index satisfies `k ∈ {1, 2}` (eq. 1.6)
- `fundamental_regulator_quantization`: `log ε_n / (n log n) = 1 / (2k) + O(1 / log n)` (eq. 1.7)
- `q_n_ne_of_solutions`: no two solutions `4 ≤ n₁ < n₂` share `q_{n₁} = q_{n₂}`
-/

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard

private lemma q_n_s_n_unique {n q s : ℕ} (hq_sf : Squarefree q) (hfac : Nat.factorial n = q * s ^ 2) :
    q_n n = q ∧ s_n n = s := by
  have hfac_n : Nat.factorial n = q_n n * (s_n n) ^ 2 := factorial_eq_q_n_mul_s_n_sq n
  have hq_ne : q ≠ 0 := hq_sf.ne_zero
  have hqn_ne : q_n n ≠ 0 := (q_n_squarefree n).ne_zero
  have hq_eq : q_n n = q := by
    apply Nat.eq_of_factorization_eq hqn_ne hq_ne
    intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      have h1 : (q_n n).factorization p ≤ 1 := by
        by_contra hgt
        have h2 : p ^ 2 ∣ q_n n := by
          rw [padicValNat_dvd_iff_le hqn_ne, ← Nat.factorization_def _ hp]
          omega
        exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp (by simpa [sq] using h2)
      have h2 : q.factorization p ≤ 1 := by
        by_contra hgt
        have h2' : p ^ 2 ∣ q := by
          rw [padicValNat_dvd_iff_le hq_ne, ← Nat.factorization_def _ hp]
          omega
        exact (Nat.squarefree_iff_prime_squarefree.mp hq_sf) p hp (by simpa [sq] using h2')
      have hs_ne : s ≠ 0 := by
        intro h0; subst h0; simp at hfac; exact Nat.factorial_ne_zero n hfac
      have hsn_ne : s_n n ≠ 0 := by
        intro h0; rw [h0] at hfac_n; simp at hfac_n; exact Nat.factorial_ne_zero n hfac_n
      have heq_fac : (q_n n * (s_n n) ^ 2).factorization p = (q * s ^ 2).factorization p := by
        rw [← hfac_n, ← hfac]
      rw [Nat.factorization_mul hqn_ne (pow_ne_zero 2 hsn_ne),
          Nat.factorization_mul hq_ne (pow_ne_zero 2 hs_ne),
          Nat.factorization_pow, Nat.factorization_pow] at heq_fac
      simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at heq_fac
      omega
    · have h0a : (q_n n).factorization p = 0 := by
        by_contra h0; exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
      have h0b : q.factorization p = 0 := by
        by_contra h0; exact hp (Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr h0))
      omega
  refine ⟨hq_eq, ?_⟩
  have hsq : (s_n n) ^ 2 = s ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq_ne)
    calc q * (s_n n) ^ 2 = q_n n * (s_n n) ^ 2 := by rw [hq_eq]
      _ = Nat.factorial n := hfac_n.symm
      _ = q * s ^ 2 := hfac
  exact (Nat.pow_left_inj (by norm_num : 2 ≠ 0)).mp hsq

private lemma squarefree_6 : Squarefree 6 := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hle : p * p ≤ 6 := Nat.le_of_dvd (by norm_num) hpp
  have hp2 : p ≤ 2 := by nlinarith
  interval_cases p <;> (try norm_num at hp) <;> (try norm_num at hpp)

private lemma squarefree_30 : Squarefree 30 := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hle : p * p ≤ 30 := Nat.le_of_dvd (by norm_num) hpp
  have hp5 : p ≤ 5 := by nlinarith
  interval_cases p <;> (try norm_num at hp) <;> (try norm_num at hpp)

private lemma squarefree_35 : Squarefree 35 := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hle : p * p ≤ 35 := Nat.le_of_dvd (by norm_num) hpp
  have hp5 : p ≤ 5 := by nlinarith
  interval_cases p <;> (try norm_num at hp) <;> (try norm_num at hpp)

/-- `k(4) = 1` with `q_4 = 6`, `s_4 = 2`, `ε_4 = 5 + 2√6`. -/
theorem known_k4 :
    q_n 4 = 6 ∧ s_n 4 = 2 ∧ IsFundamentalPell 6 5 2 ∧
      (5 : ℝ) + 2 * Real.sqrt 6 = (pellUnit 6 5 2) ^ 1 := by
  obtain ⟨hq, hs⟩ := q_n_s_n_unique (n := 4) (q := 6) (s := 2) squarefree_6 (by norm_num [Nat.factorial])
  have hfund : IsFundamentalPell 6 5 2 := by
    refine ⟨by norm_num, by norm_num, by norm_num, fun x y hy heq => ?_⟩
    by_contra hlt
    have hy1 : y = 1 := by omega
    subst hy1
    have hx : x ^ 2 = 7 := by omega
    have h2 : x ≤ 2 ∨ 3 ≤ x := by omega
    rcases h2 with h2 | h3 <;> nlinarith
  refine ⟨hq, hs, hfund, ?_⟩
  unfold pellUnit
  simp

/-- `k(5) = 1` with `q_5 = 30`, `s_5 = 2`, `ε_5 = 11 + 2√30`. -/
theorem known_k5 :
    q_n 5 = 30 ∧ s_n 5 = 2 ∧ IsFundamentalPell 30 11 2 ∧
      (11 : ℝ) + 2 * Real.sqrt 30 = (pellUnit 30 11 2) ^ 1 := by
  obtain ⟨hq, hs⟩ := q_n_s_n_unique (n := 5) (q := 30) (s := 2) squarefree_30 (by norm_num [Nat.factorial])
  have hfund : IsFundamentalPell 30 11 2 := by
    refine ⟨by norm_num, by norm_num, by norm_num, fun x y hy heq => ?_⟩
    by_contra hlt
    have hy1 : y = 1 := by omega
    subst hy1
    have hx : x ^ 2 = 31 := by omega
    have h5 : x ≤ 5 ∨ 6 ≤ x := by omega
    rcases h5 with h5 | h6 <;> nlinarith
  refine ⟨hq, hs, hfund, ?_⟩
  unfold pellUnit
  simp

/-- `k(7) = 2` with `q_7 = 35`, `s_7 = 12`, `ε_7 = 6 + √35`, `71 + 12√35 = ε_7^2`. -/
theorem known_k7 :
    q_n 7 = 35 ∧ s_n 7 = 12 ∧ IsFundamentalPell 35 6 1 ∧
      (71 : ℝ) + 12 * Real.sqrt 35 = (pellUnit 35 6 1) ^ 2 := by
  obtain ⟨hq, hs⟩ := q_n_s_n_unique (n := 7) (q := 35) (s := 12) squarefree_35 (by norm_num [Nat.factorial])
  have hfund : IsFundamentalPell 35 6 1 :=
    ⟨by norm_num, by norm_num, by norm_num, fun _ _ hy _ => hy⟩
  refine ⟨hq, hs, hfund, ?_⟩
  unfold pellUnit
  have hsq : Real.sqrt 35 ^ 2 = 35 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [hsq]
  ring

private lemma prod_pow_dvd_of_prime_dvd {S : Finset ℕ} {f : ℕ → ℕ} {M : ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hdvd : ∀ p ∈ S, p ^ f p ∣ M) :
    (∏ p ∈ S, p ^ f p) ∣ M := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp_not ih =>
    rw [Finset.prod_insert hp_not]
    have hp : p.Prime := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have ih' := ih hS' (fun q hq => hdvd q (Finset.mem_insert_of_mem hq))
    have hcop : Nat.Coprime (p ^ f p) (∏ q ∈ S, q ^ f q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hq_pr : q.Prime := hS' q hq
      have hpq : p ≠ q := fun h => hp_not (h ▸ hq)
      exact ((hp.coprime_iff_not_dvd.mpr (fun h =>
        hpq ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp (hp.dvd_of_dvd_pow h)))).pow_left _)
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd p (Finset.mem_insert_self p S)) ih'

private lemma sum_padicValNat_log_le {k : ℕ} (hk : 1 ≤ k) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, (padicValNat p k : ℝ) * Real.log (p : ℝ) ≤ Real.log (k : ℝ) := by
  have hprod_dvd : (∏ p ∈ S, p ^ padicValNat p k) ∣ k := by
    apply prod_pow_dvd_of_prime_dvd hS
    intro p hp
    haveI : Fact p.Prime := ⟨hS p hp⟩
    exact pow_padicValNat_dvd
  have hprod_pos : 0 < ∏ p ∈ S, p ^ padicValNat p k := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (hS p hp).pos _
  have hle_nat : (∏ p ∈ S, p ^ padicValNat p k) ≤ k := Nat.le_of_dvd hk hprod_dvd
  have hle_real : ((∏ p ∈ S, p ^ padicValNat p k : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hle_nat
  have hlog_le : Real.log ((∏ p ∈ S, p ^ padicValNat p k : ℕ) : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by exact_mod_cast hprod_pos) hle_real
  have hlog_prod : Real.log ((∏ p ∈ S, p ^ padicValNat p k : ℕ) : ℝ) =
      ∑ p ∈ S, (padicValNat p k : ℝ) * Real.log (p : ℝ) := by
    push_cast
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Real.log_pow]
    · intro p hp
      exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (hS p hp).ne_zero)
  linarith

private lemma padicValNat_factorial_three_le (n : ℕ) :
    (padicValNat 3 (Nat.factorial n) : ℝ) ≤ (n : ℝ) / 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hlog_lt : Nat.log 3 n < n + 1 := by
    by_cases hn0 : n = 0
    · subst hn0; simp
    · have hlt : n < 3 ^ (n + 1) := by
        have hself : ∀ m : ℕ, m < 3 ^ m := by
          intro m
          induction m with
          | zero => norm_num
          | succ m ihm =>
            calc m + 1 ≤ 3 ^ m + 1 := by omega
              _ < 3 ^ m * 3 := by
                have : 1 ≤ 3 ^ m := Nat.one_le_pow m 3 (by norm_num)
                omega
              _ = 3 ^ (m + 1) := (pow_succ 3 m).symm
        exact lt_trans (hself n) (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n))
      exact Nat.log_lt_of_lt_pow hn0 hlt
  rw [padicValNat_factorial hlog_lt]
  push_cast
  calc ∑ i ∈ Finset.Ico 1 (n + 1), ((n / 3 ^ i : ℕ) : ℝ)
      ≤ ∑ i ∈ Finset.Ico 1 (n + 1), (n : ℝ) * (1 / 3 : ℝ) ^ i := by
        apply Finset.sum_le_sum
        intro i _
        have h1 : ((n / 3 ^ i : ℕ) : ℝ) ≤ (n : ℝ) / ((3 ^ i : ℕ) : ℝ) := Nat.cast_div_le
        simpa [one_div, inv_pow, div_eq_mul_inv] using h1
    _ = (n : ℝ) * ∑ i ∈ Finset.Ico 1 (n + 1), (1 / 3 : ℝ) ^ i := (Finset.mul_sum _ _ _).symm
    _ ≤ (n : ℝ) * (1 / 2 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hico_le : ∀ m : ℕ, ∑ i ∈ Finset.Ico 1 (m + 1), (1 / 3 : ℝ) ^ i ≤
            1 / 2 - (1 / 2 : ℝ) * (1 / 3 : ℝ) ^ m := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 1)]
            have : (1 / 3 : ℝ) ^ (m + 1) = (1 / 3 : ℝ) ^ m * (1 / 3 : ℝ) := pow_succ _ _
            linarith
        have hpow_nn : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ n := by positivity
        linarith [hico_le n]
    _ = (n : ℝ) / 2 := by ring

/-- **Theorem 1.1 (Unconditional Collapse of the Pell Index, eq. 1.6)**:
For all sufficiently large solutions `(n, m)` to `n! + 1 = m^2`, the Pell index `k`
satisfies `k = 1 ∨ k = 2`. -/
private lemma pellUnit_pow_eq_lucas (D X₁ Y₁ k : ℕ) :
    (pellUnit D X₁ Y₁) ^ k =
      (lucasX (D : ℤ) (X₁ : ℤ) (Y₁ : ℤ) k : ℝ) +
        (lucasY (D : ℤ) (X₁ : ℤ) (Y₁ : ℤ) k : ℝ) * Real.sqrt (D : ℝ) := by
  induction k with
  | zero =>
    unfold lucasX lucasY
    simp
  | succ k ih =>
    rw [pow_succ, ih]
    unfold pellUnit lucasX lucasY
    rw [pow_succ, Zsqrtd.mul_re, Zsqrtd.mul_im]
    push_cast
    have hsq : Real.sqrt (D : ℝ) ^ 2 = (D : ℝ) := by
      rw [sq]
      exact Real.mul_self_sqrt (Nat.cast_nonneg D)
    ring_nf
    rw [hsq]
    ring

theorem pell_index_collapse_large :
    ∃ N₀ : ℕ, ∀ n m k X₁ Y₁ : ℕ, N₀ ≤ n →
      Nat.factorial n + 1 = m ^ 2 →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ k →
      k = 1 ∨ k = 2 := by
  have hSodd := S_odd_asymptotic
  have hSodd_ev : ∀ᶠ n : ℕ in atTop,
      (0.45 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) ≤ S_odd n := by
    have h1 := hSodd.bound (by norm_num : (0 : ℝ) < 0.05)
    filter_upwards [h1, eventually_ge_atTop 2] with n hn hn2
    have hn_log_nn : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
    rw [Real.norm_of_nonneg hn_log_nn] at hn
    have h2 := (abs_le.mp (Real.norm_eq_abs _ ▸ hn)).1
    linarith
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_large : ∀ᶠ n : ℕ in atTop,
      (0.45 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) ≤ S_odd n ∧
      116 ≤ n ∧
      (n : ℝ) / 2 * Real.log 3 + 2 * Real.log (2.5 * Real.log (n : ℝ)) + 2 * Real.log 3 <
        (0.11 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by
    have hratio : Tendsto (fun n : ℕ =>
        ((n : ℝ) / 2 * Real.log 3 + 2 * Real.log (2.5 * Real.log (n : ℝ)) + 2 * Real.log 3) /
          ((n : ℝ) * Real.log (n : ℝ))) atTop (nhds 0) := by
      have h_eq : (fun n : ℕ =>
          ((n : ℝ) / 2 * Real.log 3 + 2 * Real.log (2.5 * Real.log (n : ℝ)) + 2 * Real.log 3) /
            ((n : ℝ) * Real.log (n : ℝ))) =ᶠ[atTop]
          (fun n : ℕ =>
            (Real.log 3 / 2) / Real.log (n : ℝ) +
            2 * (Real.log (2.5 * Real.log (n : ℝ)) / Real.log (n : ℝ)) / (n : ℝ) +
            (2 * Real.log 3) / ((n : ℝ) * Real.log (n : ℝ))) := by
        filter_upwards [eventually_ge_atTop 2] with n hn2
        have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
        have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        field_simp [hn_pos.ne', hlog_pos.ne']
      have ht1 : Tendsto (fun n : ℕ => (Real.log 3 / 2) / Real.log (n : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hlog_inf
      have ht2 : Tendsto (fun n : ℕ => 2 * (Real.log (2.5 * Real.log (n : ℝ)) / Real.log (n : ℝ)) / (n : ℝ))
          atTop (nhds 0) := by
        have hlog_div : Tendsto (fun t : ℝ => Real.log (2.5 * t) / t) atTop (nhds 0) := by
          have h1 : (fun t : ℝ => Real.log (2.5 * t) / t) =ᶠ[atTop]
              (fun t : ℝ => Real.log 2.5 / t + Real.log t / t) := by
            filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
            rw [Real.log_mul (by norm_num) ht.ne', add_div]
          have h2 : Tendsto (fun t : ℝ => Real.log 2.5 / t) atTop (nhds 0) :=
            tendsto_const_nhds.div_atTop tendsto_id
          have h3 : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) := by
            have h_inv_sqrt : Tendsto (fun t : ℝ => 2 / Real.sqrt t) atTop (nhds 0) := by
              have hsq : Tendsto (fun t : ℝ => Real.sqrt t) atTop atTop :=
                tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) |>.congr'
                  (Eventually.of_forall fun t => (Real.sqrt_eq_rpow t).symm)
              exact tendsto_const_nhds.div_atTop hsq
            refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_inv_sqrt ?_ ?_
            · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
              exact div_nonneg (Real.log_nonneg ht) (by linarith)
            · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
              have ht_pos : 0 < t := by linarith
              have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
              have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hsqrt_pos
              have h2 : Real.log t = 2 * Real.log (Real.sqrt t) := by
                rw [Real.sqrt_eq_rpow, Real.log_rpow ht_pos]; ring
              rw [div_le_div_iff₀ ht_pos hsqrt_pos]
              have hsq_t : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht_pos.le
              nlinarith
          simpa using (h2.add h3).congr' h1.symm
        have hcomp : Tendsto (fun n : ℕ => Real.log (2.5 * Real.log (n : ℝ)) / Real.log (n : ℝ))
            atTop (nhds 0) := hlog_div.comp hlog_inf
        have hmul : Tendsto (fun n : ℕ => 2 * (Real.log (2.5 * Real.log (n : ℝ)) / Real.log (n : ℝ)))
            atTop (nhds 0) := by simpa using hcomp.const_mul 2
        exact hmul.div_atTop tendsto_natCast_atTop_atTop
      have ht3 : Tendsto (fun n : ℕ => (2 * Real.log 3) / ((n : ℝ) * Real.log (n : ℝ)))
          atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ hlog_inf)
      have hsum : Tendsto (fun n : ℕ =>
          (Real.log 3 / 2) / Real.log (n : ℝ) +
          2 * (Real.log (2.5 * Real.log (n : ℝ)) / Real.log (n : ℝ)) / (n : ℝ) +
          (2 * Real.log 3) / ((n : ℝ) * Real.log (n : ℝ))) atTop (nhds 0) := by
        simpa using (ht1.add ht2).add ht3
      exact hsum.congr' h_eq.symm
    filter_upwards [hSodd_ev, eventually_ge_atTop 116,
      hratio.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 0.11))] with n hS hn116 hrat
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hnlog_pos : 0 < (n : ℝ) * Real.log (n : ℝ) := mul_pos hn_pos hlog_pos
    rw [div_lt_iff₀ hnlog_pos] at hrat
    exact ⟨hS, hn116, hrat⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h_large
  refine ⟨N₀, fun n m k X₁ Y₁ hn hm hfund hk_eq => ?_⟩
  obtain ⟨hS_bd, hn116, h_err_bd⟩ := hN₀ n hn
  have hq_log := log_q_n_gt_point4 hn116
  have hs_eq : (s_n n : ℤ) = (Y₁ : ℤ) * chebyshevU_eval (q_n n : ℤ) (X₁ : ℤ) (Y₁ : ℤ) k := by
    rw [← lucasY_eq_mul_chebyshevU]
    have hk_lucas := hk_eq
    rw [pellUnit_pow_eq_lucas] at hk_lucas
    by_contra hne
    have hsub_ne : (((s_n n : ℤ) - lucasY (q_n n : ℤ) (X₁ : ℤ) (Y₁ : ℤ) k : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr hne
    let r_q : ℚ :=
      (((lucasX (q_n n : ℤ) (X₁ : ℤ) (Y₁ : ℤ) k - (m : ℤ) : ℤ) : ℚ)) /
      ((((s_n n : ℤ) - lucasY (q_n n : ℤ) (X₁ : ℤ) (Y₁ : ℤ) k : ℤ) : ℚ))
    have hsqrt_rat : (r_q : ℝ) = Real.sqrt (q_n n : ℝ) := by
      dsimp only [r_q]
      push_cast
      rw [div_eq_iff hsub_ne]
      linarith
    have hq_nsq : ¬ IsSquare (q_n n) := by
      rintro ⟨r, hr⟩
      have hunit : IsUnit r := (q_n_squarefree n) r (by rw [hr])
      have hr1 : r = 1 := Nat.isUnit_iff.mp hunit
      have hq1 : q_n n = 1 := by rw [hr, hr1, mul_one]
      have hlog0 : Real.log (q_n n : ℝ) = 0 := by rw [hq1]; simp
      have : (0 : ℝ) < 0.4 * (n : ℝ) := by positivity
      linarith
    have hirr : Irrational (Real.sqrt (q_n n : ℝ)) :=
      irrational_sqrt_natCast_iff.mpr hq_nsq
    exact hirr ⟨r_q, hsqrt_rat⟩
  have heps_log := log_fund_pell_gt_point2 hq_log hfund
  obtain ⟨hk1, hk_lt, _⟩ := pell_index_upper_bound (by omega) hm hfund heps_log hk_eq
  have hpell_int : (X₁ : ℤ) ^ 2 - (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 = 1 := by
    have h1 : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
    linarith
  have hY1_pos : 0 < Y₁ := hfund.2.1
  have hq_pos : 0 < q_n n := by
    unfold q_n
    exact Finset.prod_pos (fun q hq => (Finset.mem_filter.mp hq).2.1.pos)
  -- Lower bound (3.5): `S_odd n - v_3(n!) * log 3 - 2 * log k ≤ log(q_n * Y₁^2)`
  have hlog_qY2_lower :
      S_odd n - (padicValNat 3 (Nat.factorial n) : ℝ) * Real.log 3 - 2 * Real.log (k : ℝ) ≤
        Real.log ((q_n n * Y₁ ^ 2 : ℕ) : ℝ) := by
    set S := (Podd n).erase 3
    have hS_pr : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2.1
    have hprod_dvd : (∏ p ∈ S, p ^ (padicValNat p (Nat.factorial n) - 2 * padicValNat p k)) ∣
        q_n n * Y₁ ^ 2 := by
      apply prod_pow_dvd_of_prime_dvd hS_pr
      intro p hp
      have hp_mem := Finset.mem_erase.mp hp
      have hval := padicValNat_pell_absorption hk1 hp_mem.2 hp_mem.1 hpell_int hY1_pos hs_eq
      rw [← hval]
      haveI : Fact p.Prime := ⟨hS_pr p hp⟩
      exact pow_padicValNat_dvd
    have hprod_pos : 0 < ∏ p ∈ S, p ^ (padicValNat p (Nat.factorial n) - 2 * padicValNat p k) :=
      Finset.prod_pos (fun p hp => pow_pos (hS_pr p hp).pos _)
    have hle_nat : (∏ p ∈ S, p ^ (padicValNat p (Nat.factorial n) - 2 * padicValNat p k)) ≤
        q_n n * Y₁ ^ 2 := Nat.le_of_dvd (mul_pos hq_pos (pow_pos hY1_pos 2)) hprod_dvd
    have hlog_le : Real.log ((∏ p ∈ S, p ^ (padicValNat p (Nat.factorial n) - 2 * padicValNat p k) : ℕ) : ℝ) ≤
        Real.log ((q_n n * Y₁ ^ 2 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hprod_pos) (by exact_mod_cast hle_nat)
    have hlog_prod : Real.log ((∏ p ∈ S, p ^ (padicValNat p (Nat.factorial n) - 2 * padicValNat p k) : ℕ) : ℝ) =
        ∑ p ∈ S, ((padicValNat p (Nat.factorial n) - 2 * padicValNat p k : ℕ) : ℝ) * Real.log (p : ℝ) := by
      push_cast
      rw [Real.log_prod]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Real.log_pow]
      · intro p hp
        exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (hS_pr p hp).ne_zero)
    have hsum_ge :
        ∑ p ∈ S, ((padicValNat p (Nat.factorial n) : ℝ) - 2 * (padicValNat p k : ℝ)) * Real.log (p : ℝ) ≤
          ∑ p ∈ S, ((padicValNat p (Nat.factorial n) - 2 * padicValNat p k : ℕ) : ℝ) * Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hlogp_nn : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (hS_pr p hp).one_lt.le)
      apply mul_le_mul_of_nonneg_right _ hlogp_nn
      by_cases hle : 2 * padicValNat p k ≤ padicValNat p (Nat.factorial n)
      · rw [Nat.cast_sub hle]; push_cast; linarith
      · push_neg at hle
        have h0 : padicValNat p (Nat.factorial n) - 2 * padicValNat p k = 0 := by omega
        rw [h0, Nat.cast_zero]
        have : (padicValNat p (Nat.factorial n) : ℝ) < 2 * (padicValNat p k : ℝ) := by exact_mod_cast hle
        linarith
    have hSodd_split : S_odd n - (padicValNat 3 (Nat.factorial n) : ℝ) * Real.log 3 ≤
        ∑ p ∈ S, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
      unfold S_odd
      have h3_nn : 0 ≤ (padicValNat 3 (Nat.factorial n) : ℝ) * Real.log 3 :=
        mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
      have hsub_le : ∑ p ∈ (Podd n).filter (3 ≤ ·), (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
          ∑ p ∈ Podd n, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro p hp _
        have hp_pr := (Finset.mem_filter.mp hp).2.1
        exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le))
      by_cases h3_mem : 3 ∈ Podd n
      · have hsub : Podd n = insert 3 S := (Finset.insert_erase h3_mem).symm
        have hnot : 3 ∉ S := Finset.notMem_erase 3 (Podd n)
        have hsum_eq : ∑ p ∈ Podd n, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) =
            (padicValNat 3 (Nat.factorial n) : ℝ) * Real.log 3 +
              ∑ p ∈ S, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
          rw [hsub, Finset.sum_insert hnot]
          norm_num
        linarith
      · have hS_eq : S = Podd n := Finset.erase_eq_of_notMem h3_mem
        rw [hS_eq]
        linarith
    have hk_sum := sum_padicValNat_log_le hk1 S hS_pr
    have hsum_sub :
        ∑ p ∈ S, ((padicValNat p (Nat.factorial n) : ℝ) - 2 * (padicValNat p k : ℝ)) * Real.log (p : ℝ) =
        ∑ p ∈ S, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) -
        2 * ∑ p ∈ S, (padicValNat p k : ℝ) * Real.log (p : ℝ) := by
      simp_rw [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    linarith
  -- Upper bound (3.4): `log(q_n * Y₁^2) < 2 * log ε_n`
  have hlog_qY2_upper :
      Real.log ((q_n n * Y₁ ^ 2 : ℕ) : ℝ) < 2 * Real.log (pellUnit (q_n n) X₁ Y₁) := by
    have hqY_pos : (0 : ℝ) < (Y₁ : ℝ) * Real.sqrt (q_n n : ℝ) := by
      have : (0 : ℝ) < (Y₁ : ℝ) := by exact_mod_cast hY1_pos
      positivity
    have h_lt : (Y₁ : ℝ) * Real.sqrt (q_n n : ℝ) < pellUnit (q_n n) X₁ Y₁ := by
      unfold pellUnit
      have : (0 : ℝ) < (X₁ : ℝ) := by exact_mod_cast hfund.1
      linarith
    have h_eq : Real.log ((q_n n * Y₁ ^ 2 : ℕ) : ℝ) =
        2 * Real.log ((Y₁ : ℝ) * Real.sqrt (q_n n : ℝ)) := by
      rw [show (2 : ℝ) * Real.log ((Y₁ : ℝ) * Real.sqrt (q_n n : ℝ)) = Real.log (((Y₁ : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2) by rw [Real.log_pow]; norm_num]
      congr 1
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      push_cast; ring
    rw [h_eq]
    exact mul_lt_mul_of_pos_left (Real.log_lt_log hqY_pos h_lt) (by norm_num)
  -- Also `2 * k * log ε_n = 2 * log(m + s_n √q_n) ≤ 2 * log 3 + n * log n`
  have h_upper_nlogn :
      (k : ℝ) * (2 * Real.log (pellUnit (q_n n) X₁ Y₁)) ≤
        (n : ℝ) * Real.log (n : ℝ) + 2 * Real.log 3 := by
    have hfac := factorial_eq_q_n_mul_s_n_sq n
    have hs_sqrt_eq : (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = Real.sqrt ((Nat.factorial n : ℕ) : ℝ) := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (s_n n : ℝ)), ← Real.sqrt_mul (by positivity)]
      congr 1
      have : Nat.factorial n = (s_n n) ^ 2 * q_n n := by rw [hfac]; ring
      exact_mod_cast this.symm
    have hm_lt : (m : ℝ) < 2 * Real.sqrt ((Nat.factorial n : ℕ) : ℝ) := by
      have hsq : (m : ℝ) ^ 2 < (2 * Real.sqrt ((Nat.factorial n : ℕ) : ℝ)) ^ 2 := by
        have hfac_ge1 : (1 : ℝ) ≤ ((Nat.factorial n : ℕ) : ℝ) := by
          exact_mod_cast Nat.factorial_pos n
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have hm_real : (m : ℝ) ^ 2 = ((Nat.factorial n : ℕ) : ℝ) + 1 := by exact_mod_cast hm.symm
        linarith
      have h1 := Real.sqrt_lt_sqrt (by positivity) hsq
      rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h1
    have hms_lt : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) ≤
        3 * Real.sqrt ((Nat.factorial n : ℕ) : ℝ) := by linarith
    have hms_sq_le : ((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2 ≤
        9 * ((Nat.factorial n : ℕ) : ℝ) := by
      calc ((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2
          ≤ (3 * Real.sqrt ((Nat.factorial n : ℕ) : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hms_lt 2
        _ = 9 * ((Nat.factorial n : ℕ) : ℝ) := by rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    have hfac_le_pow : Nat.factorial n ≤ n ^ n := Nat.factorial_le_pow n
    have h9_le : 9 * ((Nat.factorial n : ℕ) : ℝ) ≤ 9 * (n : ℝ) ^ n := by
      exact_mod_cast Nat.mul_le_mul_left 9 hfac_le_pow
    have hlog_ms : 2 * Real.log ((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) ≤
        Real.log (9 * (n : ℝ) ^ n) := by
      rw [show (2 : ℝ) * Real.log ((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) = Real.log (((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2) by rw [Real.log_pow]; norm_num]
      have hm_pos_r : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by nlinarith [Nat.factorial_pos n] : 0 < m)
      have hs_pos_r : (0 : ℝ) ≤ (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) := by positivity
      exact Real.log_le_log (by positivity) (le_trans hms_sq_le h9_le)
    have hlog9 : Real.log (9 * (n : ℝ) ^ n) = 2 * Real.log 3 + (n : ℝ) * Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
        show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
      ring
    have hlog_pow : Real.log ((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) =
        (k : ℝ) * Real.log (pellUnit (q_n n) X₁ Y₁) := by rw [hk_eq, Real.log_pow]
    linarith
  have hv3 := padicValNat_factorial_three_le n
  have hlog3_nn : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hv3_log : (padicValNat 3 (Nat.factorial n) : ℝ) * Real.log 3 ≤ (n : ℝ) / 2 * Real.log 3 :=
    mul_le_mul_of_nonneg_right hv3 hlog3_nn
  have h2logk : 2 * Real.log (k : ℝ) < 2 * Real.log (2.5 * Real.log (n : ℝ)) :=
    mul_lt_mul_of_pos_left (Real.log_lt_log (by exact_mod_cast hk1) hk_lt) (by norm_num)
  have h_eps2_lower : (0.34 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) + 2 * Real.log 3 <
      2 * Real.log (pellUnit (q_n n) X₁ Y₁) := by
    linarith
  have hk_lt_3 : k < 3 := by
    by_contra hge3
    push_neg at hge3
    have hk3_r : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hge3
    have h_pos_eps : 0 ≤ 2 * Real.log (pellUnit (q_n n) X₁ Y₁) := by
      have : (0 : ℝ) < (n : ℝ) := by positivity
      linarith
    have hmul : 3 * (2 * Real.log (pellUnit (q_n n) X₁ Y₁)) ≤
        (k : ℝ) * (2 * Real.log (pellUnit (q_n n) X₁ Y₁)) :=
      mul_le_mul_of_nonneg_right hk3_r h_pos_eps
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hnlog_pos : 0 < (n : ℝ) * Real.log (n : ℝ) := mul_pos hn_pos hlog_pos
    linarith
  omega

/-- **Theorem 1.1 (Fundamental Regulator Quantization Law, eq. 1.7)**:
There exists a constant `C > 0` such that for all `n ≥ 8` and any solution `(n, m)` to
`n! + 1 = m^2` with `m + s_n √q_n = ε_n^k`,
`|log ε_n / (n log n) - 1 / (2k)| ≤ C / log n`. -/
theorem fundamental_regulator_quantization :
    ∃ C : ℝ, 0 < C ∧ ∀ n m k X₁ Y₁ : ℕ, 8 ≤ n →
      Nat.factorial n + 1 = m ^ 2 →
      1 ≤ k →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ k →
      |Real.log (pellUnit (q_n n) X₁ Y₁) / ((n : ℝ) * Real.log (n : ℝ)) - 1 / (2 * (k : ℝ))| ≤
        C / Real.log (n : ℝ) := by
  -- From `log_s_n_sqrt_q_n_asymptotic`: `|log(s_n √q_n) - ((1/2) n log n - (1/2) n + (1/4) log(2πn))| ≤ C₁ * n⁻¹`
  obtain ⟨C₁, hC₁⟩ := log_s_n_sqrt_q_n_asymptotic.bound
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hC₁
  -- Since we quantify over all `n ≥ 8`, `log(s_n √q_n) - (1/2) n log n = O(n)` for all `n ≥ 8`
  -- Let's use `log(n!) = n log n - n + O(log n)` or directly `|log(s_n √q_n) - (1/2) n log n| ≤ C₀ * n` for `n ≥ 8`!
  -- Actually `log(n!) ≤ n log n` and `n log n - n ≤ log(n!)` (already in `ValuationParityThm.lean` as `n_log_n_sub_n_le_log_factorial`!)
  refine ⟨10, by norm_num, fun n m k X₁ Y₁ hn hm hk1 hfund hk_eq => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hfac_lower : (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) ≤ Real.log ((Nat.factorial n : ℕ) : ℝ) :=
    (n_log_n_sub_n_le_log_factorial n (by omega)).1
  have hfac_upper : Real.log ((Nat.factorial n : ℕ) : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    have hle : Nat.factorial n ≤ n ^ n := Nat.factorial_le_pow n
    have h1 := Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) (by exact_mod_cast hle : ((Nat.factorial n : ℕ) : ℝ) ≤ (n : ℝ) ^ n)
    rwa [Real.log_pow] at h1
  have hfac := factorial_eq_q_n_mul_s_n_sq n
  have hs_sqrt_eq : (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = Real.sqrt ((Nat.factorial n : ℕ) : ℝ) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (s_n n : ℝ)), ← Real.sqrt_mul (by positivity)]
    congr 1
    have : Nat.factorial n = (s_n n) ^ 2 * q_n n := by rw [hfac]; ring
    exact_mod_cast this.symm
  have hlog_ssq : Real.log ((s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) =
      (1 / 2 : ℝ) * Real.log ((Nat.factorial n : ℕ) : ℝ) := by
    rw [hs_sqrt_eq, Real.sqrt_eq_rpow, Real.log_rpow (by positivity)]
  have hm_ge : (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) < (m : ℝ) := by
    rw [hs_sqrt_eq]
    have h1 : Real.sqrt ((Nat.factorial n : ℕ) : ℝ) < Real.sqrt ((m : ℝ) ^ 2) := by
      apply Real.sqrt_lt_sqrt (by positivity)
      have hm_r : (m : ℝ) ^ 2 = ((Nat.factorial n : ℕ) : ℝ) + 1 := by exact_mod_cast hm.symm
      linarith
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hm_lt : (m : ℝ) < 2 * ((s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) := by
    rw [hs_sqrt_eq]
    have h1 : Real.sqrt ((m : ℝ) ^ 2) < Real.sqrt ((2 * Real.sqrt ((Nat.factorial n : ℕ) : ℝ)) ^ 2) := by
      apply Real.sqrt_lt_sqrt (by positivity)
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hm_r : (m : ℝ) ^ 2 = ((Nat.factorial n : ℕ) : ℝ) + 1 := by exact_mod_cast hm.symm
      have hfac_ge1 : (1 : ℝ) ≤ ((Nat.factorial n : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
      linarith
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h1
  have hssq_pos : 0 < (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) := by
    rw [hs_sqrt_eq]; positivity
  have hms_lo : 2 * ((s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) < (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) := by linarith
  have hms_hi : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) < 3 * ((s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) := by linarith
  have hlog_ms_lo : Real.log 2 + Real.log ((s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) <
      Real.log ((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) := by
    rw [← Real.log_mul (by norm_num) hssq_pos.ne']
    exact Real.log_lt_log (by positivity) hms_lo
  have hlog_ms_hi : Real.log ((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) <
      Real.log 3 + Real.log ((s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) := by
    rw [← Real.log_mul (by norm_num) hssq_pos.ne']
    exact Real.log_lt_log (by positivity) hms_hi
  have hlog_pow : Real.log ((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) =
      (k : ℝ) * Real.log (pellUnit (q_n n) X₁ Y₁) := by rw [hk_eq, Real.log_pow]
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3_le : Real.log 3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.718 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have he2 : (2.718 : ℝ) ^ 2 < Real.exp 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
    norm_num at he2
    linarith
  have hdiff_bound : |(k : ℝ) * Real.log (pellUnit (q_n n) X₁ Y₁) - (1 / 2 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))| ≤
      2 * (n : ℝ) := by
    rw [abs_le]
    have hn_ge8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    constructor <;> linarith
  have hdiv :
      Real.log (pellUnit (q_n n) X₁ Y₁) / ((n : ℝ) * Real.log (n : ℝ)) - 1 / (2 * (k : ℝ)) =
        ((k : ℝ) * Real.log (pellUnit (q_n n) X₁ Y₁) - (1 / 2 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))) /
          ((k : ℝ) * ((n : ℝ) * Real.log (n : ℝ))) := by
    field_simp [hk_pos.ne', hn_pos.ne', hlogn_pos.ne']
  rw [hdiv, abs_div, abs_of_pos (mul_pos hk_pos (mul_pos hn_pos hlogn_pos))]
  calc |(k : ℝ) * Real.log (pellUnit (q_n n) X₁ Y₁) - (1 / 2 : ℝ) * ((n : ℝ) * Real.log (n : ℝ))| /
        ((k : ℝ) * ((n : ℝ) * Real.log (n : ℝ)))
      ≤ (2 * (n : ℝ)) / ((k : ℝ) * ((n : ℝ) * Real.log (n : ℝ))) :=
        div_le_div_of_nonneg_right hdiff_bound (by positivity)
    _ ≤ (2 * (n : ℝ)) / (1 * ((n : ℝ) * Real.log (n : ℝ))) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hk_ge1 (by positivity)
    _ = 2 / Real.log (n : ℝ) := by field_simp [hn_pos.ne', hlogn_pos.ne']
    _ ≤ 10 / Real.log (n : ℝ) := div_le_div_of_nonneg_right (by norm_num) hlogn_pos.le

/-- **Theorem 1.1 (Distinctness of Square-Free Cores)**: No two solutions `4 ≤ n₁ < n₂`
to `n! + 1 = m^2` share the same square-free core (`q_{n₁} ≠ q_{n₂}`). -/
theorem q_n_ne_of_solutions {n₁ n₂ m₁ m₂ : ℕ} (hn₁ : 4 ≤ n₁) (hlt : n₁ < n₂)
    (hm₁ : Nat.factorial n₁ + 1 = m₁ ^ 2) (hm₂ : Nat.factorial n₂ + 1 = m₂ ^ 2) :
    q_n n₁ ≠ q_n n₂ := by
  intro hq_eq
  have hfac1 := factorial_eq_q_n_mul_s_n_sq n₁
  have hfac2 := factorial_eq_q_n_mul_s_n_sq n₂
  have hdvd_fac : Nat.factorial n₁ ∣ Nat.factorial n₂ := Nat.factorial_dvd_factorial hlt.le
  have hq_pos : 0 < q_n n₁ := by
    unfold q_n
    exact Finset.prod_pos (fun q hq => (Finset.mem_filter.mp hq).2.1.pos)
  have hs_sq_dvd : (s_n n₁) ^ 2 ∣ (s_n n₂) ^ 2 := by
    rw [hfac1, hfac2, hq_eq] at hdvd_fac
    rw [hq_eq] at hq_pos
    exact Nat.dvd_of_mul_dvd_mul_left hq_pos hdvd_fac
  have hs_dvd : s_n n₁ ∣ s_n n₂ := (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp hs_sq_dvd
  obtain ⟨t, ht_eq⟩ := hs_dvd
  have hratio : Nat.factorial n₂ / Nat.factorial n₁ = t ^ 2 := by
    have hs1_pos : 0 < s_n n₁ := by
      unfold s_n
      exact Finset.prod_pos (fun q hq => pow_pos (Finset.mem_filter.mp hq).2.pos _)
    have hmul : Nat.factorial n₂ = Nat.factorial n₁ * t ^ 2 := by
      rw [hfac2, hfac1, hq_eq, ht_eq, mul_pow]
      ring
    rw [hmul, Nat.mul_div_cancel_left _ (Nat.factorial_pos n₁)]
  -- Also `n₂! / n₁! = ∏ j ∈ Finset.range (n₂ - n₁), (n₁ + 1 + j)`
  have hprod_eq : Nat.factorial n₂ / Nat.factorial n₁ =
      ∏ j ∈ Finset.range (n₂ - n₁), (n₁ + 1 + j) := by
    have hmul : Nat.factorial n₂ = Nat.factorial n₁ * ∏ j ∈ Finset.range (n₂ - n₁), (n₁ + 1 + j) := by
      have h_ind : ∀ d : ℕ, Nat.factorial (n₁ + d) =
          Nat.factorial n₁ * ∏ j ∈ Finset.range d, (n₁ + 1 + j) := by
        intro d
        induction d with
        | zero => simp
        | succ d ih =>
          rw [show n₁ + (d + 1) = (n₁ + d) + 1 by omega, Nat.factorial_succ, ih,
            Finset.prod_range_succ]
          ring
      simpa [Nat.add_sub_of_le hlt.le] using h_ind (n₂ - n₁)
    rw [hmul, Nat.mul_div_cancel_left _ (Nat.factorial_pos n₁)]
  have hsq_prod : IsSquare (∏ j ∈ Finset.range (n₂ - n₁), (n₁ + 1 + j)) := by
    rw [← hprod_eq, hratio]
    exact ⟨t, by ring⟩
  have hn_diff : n₂ - n₁ < 2 := by
    by_contra hge2
    push_neg at hge2
    exact erdos_selfridge_consecutive_product_not_square (n₁ + 1) (n₂ - n₁) (by omega) hge2 hsq_prod
  have hn2_eq : n₂ = n₁ + 1 := by omega
  subst hn2_eq
  simp only [Nat.add_sub_cancel_left, Finset.prod_range_one, add_zero] at hprod_eq
  have hn1_sq : n₁ + 1 = t ^ 2 := by linarith
  have ht3 : 3 ≤ t := by
    by_contra hlt3
    have ht_le2 : t ≤ 2 := by omega
    have hsq4 : t ^ 2 ≤ 4 := by nlinarith
    omega
  -- `(t * m₁ - m₂) * (t * m₁ + m₂) = t^2 - 1`
  have hid : (t * m₁) ^ 2 = m₂ ^ 2 + (t ^ 2 - 1) := by
    have hfac_succ : Nat.factorial (n₁ + 1) = (n₁ + 1) * Nat.factorial n₁ := Nat.factorial_succ n₁
    have h1 : m₂ ^ 2 = t ^ 2 * Nat.factorial n₁ + 1 := by rw [← hm₂, hfac_succ, ← hn1_sq]; ring
    have h2 : (t * m₁) ^ 2 = t ^ 2 * Nat.factorial n₁ + t ^ 2 := by
      calc (t * m₁) ^ 2 = t ^ 2 * m₁ ^ 2 := by ring
        _ = t ^ 2 * (Nat.factorial n₁ + 1) := by rw [hm₁]
        _ = t ^ 2 * Nat.factorial n₁ + t ^ 2 := by ring
    omega
  have hlt_tm : m₂ < t * m₁ := by
    have hsq_lt : m₂ ^ 2 < (t * m₁) ^ 2 := by omega
    exact (Nat.pow_lt_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsq_lt
  have hdiff_ge1 : 1 ≤ t * m₁ - m₂ := by omega
  have hprod_factor : (t * m₁ - m₂) * (t * m₁ + m₂) = t ^ 2 - 1 := by
    zify [hlt_tm.le, (by nlinarith : 1 ≤ t ^ 2)]
    have hid_z : ((t : ℤ) * (m₁ : ℤ)) ^ 2 = (m₂ : ℤ) ^ 2 + ((t : ℤ) ^ 2 - 1) := by
      zify [(by nlinarith : 1 ≤ t ^ 2)] at hid
      push_cast at hid
      exact hid
    linarith
  have hsum_le : t * m₁ + m₂ ≤ t ^ 2 - 1 := by
    calc t * m₁ + m₂ = 1 * (t * m₁ + m₂) := by ring
      _ ≤ (t * m₁ - m₂) * (t * m₁ + m₂) := Nat.mul_le_mul_right _ hdiff_ge1
      _ = t ^ 2 - 1 := hprod_factor
  -- On the other hand, `n₁ ≥ 8` and `n₁ + 1 = t^2` gives `m₁^2 > t^2`, so `m₁ > t`, hence `t * m₁ + m₂ > t^2`!
  have hm1_gt_t : t < m₁ := by
    have hfac_gt : t ^ 2 < Nat.factorial n₁ + 1 := by
      have h1 : n₁ < Nat.factorial n₁ := by
        have : ∀ k : ℕ, 4 ≤ k → k < Nat.factorial k := by
          intro k hk
          induction k with
          | zero => omega
          | succ k ihk =>
            rcases Nat.eq_or_lt_of_le hk with h4 | hk4
            · have hk3 : k = 3 := by omega
              subst hk3
              norm_num [Nat.factorial]
            · have := ihk (by omega)
              rw [Nat.factorial_succ]
              nlinarith
        exact this n₁ hn₁
      omega
    have hsq : t ^ 2 < m₁ ^ 2 := by linarith [hm₁, hfac_gt]
    exact (Nat.pow_lt_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsq
  have hsum_gt : t ^ 2 < t * m₁ + m₂ := by
    have : t * t < t * m₁ := Nat.mul_lt_mul_of_pos_left hm1_gt_t (by omega)
    nlinarith
  linarith

end GrasGreenbergBrocard
