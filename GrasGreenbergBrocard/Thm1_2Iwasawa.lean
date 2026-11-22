import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsSec3
import GrasGreenbergBrocard.PellFundamental
import GrasGreenbergBrocard.PadicRegulator

/-!
# Theorem 1.2: Non-p-Rationality, Iwasawa Invariants, and Conditional Finiteness

Formalizes Section 3.3 (Theorem 1.2(i)–(iii), eqs. 1.8 and 3.6–3.7) of the manuscript:
- `nagura_prime_in_band`: for every `n ≥ 116`, there exists a prime `p ∈ (n/5, n/4] ⊆ (n/5, n/3]`
  with `v_p(n!) = 4`
- `prime_in_band_val_and_coprime_k`: `v_p(n!) ∈ {3, 4}` and `p ∤ k` on `(n/5, n/3]`
- `val_s_n_ge_one_on_half`: `v_p(s_n) = ⌊v_p(n!)/2⌋ ≥ 1` on `[5, n/2]` (eq. 3.6)
- `thm_1_2_eq_3_6_regulator_valuation`: proves `realQuadPadicRegVal (q_n n) p = ⌊v_p(n!)/2⌋`
  directly from `PadicRegulator.realQuadPadicRegVal_pell_power` (zero Iwasawa axioms!)
- `thm_1_2_part1_valuation_law`: eq. 1.8 and `λ_p^*(K_n) = λ_p(χ_{D_n}) ≥ 1`
- `thm_1_2_part2_split_primes`: split-prime unramified Iwasawa module and Taya criterion
- `thm_1_2_part3_conditional_finiteness`: conditional finiteness under (a), (b), or (c)
-/

noncomputable section

open Real Finset

namespace GrasGreenbergBrocard

private lemma padicValNat_factorial_ge_div {n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n) :
    n / p ≤ padicValNat p (Nat.factorial n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlog_lt : Nat.log p n < n + 1 :=
    Nat.log_lt_of_lt_pow (by omega)
      (lt_trans (Nat.lt_pow_self hp.one_lt) (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self n)))
  rw [padicValNat_factorial hlog_lt]
  have h1_mem : 1 ∈ Finset.Ico 1 (n + 1) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  simpa using Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1_mem

/-- For every `n ≥ 116`, there exists a prime `p` with `n / 5 < p ≤ n / 4` (hence `p ≤ n / 3`),
`p > √n`, and `v_p(n!) = 4`. -/
theorem nagura_prime_in_band {n : ℕ} (hn : 116 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ (n : ℝ) / 5 < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) / 4 ∧
      padicValNat p (Nat.factorial n) = 4 := by
  have hx : ∃ p : ℕ, p.Prime ∧ (n : ℝ) / 5 < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) / 4 := by
    by_cases h125 : 125 ≤ n
    · have h25 : (25 : ℝ) ≤ (n : ℝ) / 5 := by
        have : (125 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h125
        linarith
      obtain ⟨p, hp, hlo, hhi⟩ := nagura_prime_in_interval ((n : ℝ) / 5) h25
      refine ⟨p, hp, hlo, ?_⟩
      have : (6 / 5 : ℝ) * ((n : ℝ) / 5) ≤ (n : ℝ) / 4 := by
        have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by positivity
        linarith
      linarith
    · refine ⟨29, by decide, ?_, ?_⟩
      · have hn_le : (n : ℝ) ≤ 124 := by exact_mod_cast (by omega : n ≤ 124)
        linarith
      · have hn_ge : (116 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
  obtain ⟨p, hp, hlo, hhi⟩ := hx
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_gt : (23 : ℝ) < (p : ℝ) := by
    have : (116 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hp_ge24 : 24 ≤ p := by
    by_contra hle
    push_neg at hle
    have : (p : ℝ) ≤ 23 := by exact_mod_cast (by omega : p ≤ 23)
    linarith
  have hp_sq_gt : n < p ^ 2 := by
    have h1 : (n : ℝ) < 5 * (p : ℝ) := by linarith
    have h2 : (5 : ℝ) * (p : ℝ) < (p : ℝ) ^ 2 := by
      have : (24 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_ge24
      nlinarith
    exact_mod_cast lt_trans h1 h2
  have hv_div : padicValNat p (Nat.factorial n) = n / p :=
    padicValNat_factorial_eq_div_of_lt_sq hp hp_sq_gt
  have h4p : 4 * p ≤ n := by exact_mod_cast (by linarith : 4 * (p : ℝ) ≤ (n : ℝ))
  have hn5p : n < 5 * p := by exact_mod_cast (by linarith : (n : ℝ) < 5 * (p : ℝ))
  have hdiv4 : n / p = 4 := Nat.div_eq_of_lt_le h4p hn5p
  exact ⟨p, hp, hlo, hhi, by rw [hv_div, hdiv4]⟩

/-- Every prime `p ∈ (n/5, n/3]` with `n ≥ 116` satisfies `v_p(n!) ∈ {3, 4}` and `p ∤ k`. -/
theorem prime_in_band_val_and_coprime_k {n p k : ℕ} (hn : 116 ≤ n) (hp : p.Prime)
    (hlo : (n : ℝ) / 5 < (p : ℝ)) (hhi : (p : ℝ) ≤ (n : ℝ) / 3)
    (hk1 : 1 ≤ k) (hk_lt : (k : ℝ) < 2.5 * Real.log (n : ℝ)) :
    (padicValNat p (Nat.factorial n) = 3 ∨ padicValNat p (Nat.factorial n) = 4) ∧
      ¬ p ∣ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_gt23 : (23 : ℝ) < (p : ℝ) := by
    have : (116 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hp_ge24 : 24 ≤ p := by
    by_contra hle
    push_neg at hle
    have : (p : ℝ) ≤ 23 := by exact_mod_cast (by omega : p ≤ 23)
    linarith
  have hp_sq_gt : n < p ^ 2 := by
    have h1 : (n : ℝ) < 5 * (p : ℝ) := by linarith
    have h2 : (5 : ℝ) * (p : ℝ) < (p : ℝ) ^ 2 := by
      have : (24 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_ge24
      nlinarith
    exact_mod_cast lt_trans h1 h2
  have hv_div : padicValNat p (Nat.factorial n) = n / p :=
    padicValNat_factorial_eq_div_of_lt_sq hp hp_sq_gt
  have h3p : 3 * p ≤ n := by exact_mod_cast (by linarith : 3 * (p : ℝ) ≤ (n : ℝ))
  have hn5p : n < 5 * p := by exact_mod_cast (by linarith : (n : ℝ) < 5 * (p : ℝ))
  have hdiv_ge : 3 ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).mpr h3p
  have hdiv_lt : n / p < 5 := Nat.div_lt_of_lt_mul (by omega : n < p * 5)
  have hval_or : padicValNat p (Nat.factorial n) = 3 ∨ padicValNat p (Nat.factorial n) = 4 := by
    rw [hv_div]; omega
  have hk_lt_p : k < p := by
    have h125 : (12.5 : ℝ) * Real.log (n : ℝ) < (n : ℝ) := by
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      have hn_ge : (116 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hlog_div : Real.log ((n : ℝ) / 20) ≤ (n : ℝ) / 20 - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hlog20 : Real.log 20 < 3 := by
        rw [Real.log_lt_iff_lt_exp (by norm_num)]
        have he1 : (2.718 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
        have he3 : (2.718 : ℝ) ^ 3 < Real.exp 3 := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
          exact pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
        norm_num at he3
        linarith
      have hlog_n : Real.log (n : ℝ) = Real.log ((n : ℝ) / 20) + Real.log 20 := by
        rw [← Real.log_mul (by positivity) (by norm_num)]; ring_nf
      linarith
    have hkp : (k : ℝ) < (p : ℝ) := by linarith
    exact_mod_cast hkp
  exact ⟨hval_or, Nat.not_dvd_of_pos_of_lt hk1 hk_lt_p⟩

/-- **Equation (3.6)**: For `p ∈ [5, n/2]`, `v_p(n!) ≥ 2` and `v_p(s_n) = ⌊v_p(n!)/2⌋ ≥ 1`. -/
theorem val_s_n_ge_one_on_half {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp_half : p ≤ n / 2) :
    2 ≤ padicValNat p (Nat.factorial n) ∧
      padicValNat p (s_n n) = padicValNat p (Nat.factorial n) / 2 ∧
      1 ≤ padicValNat p (s_n n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn1 : 1 ≤ n := by omega
  have h2p : 2 * p ≤ n := by omega
  have hv2 : 2 ≤ padicValNat p (Nat.factorial n) :=
    le_trans ((Nat.le_div_iff_mul_le hp.pos).mpr h2p) (padicValNat_factorial_ge_div hp hn1)
  have hs_val : padicValNat p (s_n n) = padicValNat p (Nat.factorial n) / 2 := by
    unfold s_n
    rw [← Nat.factorization_def _ hp,
      Nat.factorization_prod (fun q hq => pow_ne_zero _ (Finset.mem_filter.mp hq).2.ne_zero)]
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Nat.factorization_pow, Finsupp.smul_apply,
      smul_eq_mul]
    have hmem : p ∈ (Finset.Icc 2 n).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, by omega⟩, hp⟩
    rw [Finset.sum_eq_single p]
    · rw [hp.factorization_self, mul_one]
    · intro q hq hqp
      have hq_pr : q.Prime := (Finset.mem_filter.mp hq).2
      have hnd : ¬ p ∣ q := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp h).symm
      rw [Nat.factorization_eq_zero_of_not_dvd hnd, mul_zero]
    · intro habs; exact absurd hmem habs
  exact ⟨hv2, hs_val, by omega⟩

private lemma p_dvd_q_n_iff {n p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    p ∣ q_n n ↔ padicValNat p (Nat.factorial n) % 2 = 1 := by
  constructor
  · intro hdvd
    unfold q_n at hdvd
    have hmem : p ∈ Podd n := by
      by_contra hnot
      have hcop : Nat.Coprime p (∏ q ∈ Podd n, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        have hq_pr : q.Prime := by
          unfold Podd at hq
          exact (Finset.mem_filter.mp hq).2.1
        exact (Nat.coprime_primes hp hq_pr).mpr (fun h => hnot (h ▸ hq))
      have h1 : p ∣ Nat.gcd p (∏ q ∈ Podd n, q) := Nat.dvd_gcd dvd_rfl hdvd
      rw [hcop.gcd_eq_one] at h1
      exact hp.not_dvd_one h1
    unfold Podd at hmem
    have hodd := (Finset.mem_filter.mp hmem).2.2
    omega
  · intro hodd
    unfold q_n
    apply Finset.dvd_prod_of_mem
    unfold Podd
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpn⟩, hp, by omega⟩

private lemma two_le_q_n {n : ℕ} (hn : 2 ≤ n) : 2 ≤ q_n n := by
  have hpos : 1 ≤ q_n n := by
    unfold q_n
    exact Nat.succ_le_of_lt (Finset.prod_pos (fun q hq => by
      unfold Podd at hq
      exact (Finset.mem_filter.mp hq).2.1.pos))
  by_contra hlt
  have hq1 : q_n n = 1 := by omega
  have hfac : Nat.factorial n = s_n n * s_n n := by
    have h := factorial_eq_q_n_mul_s_n_sq n
    rw [hq1, one_mul, sq] at h
    exact h
  have hprod : ∏ j ∈ Finset.range n, (1 + j) = Nat.factorial n := by
    have hall : ∀ k : ℕ, ∏ j ∈ Finset.range k, (1 + j) = Nat.factorial k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
        ring
    exact hall n
  exact erdos_selfridge_consecutive_product_not_square 1 n le_rfl hn ⟨s_n n, by rw [hprod, hfac]⟩

/-- If `n! + 1 = m^2` and `p` is a prime with `p ≤ n`, then `p ∤ m`. -/
theorem brocard_p_not_dvd_m {n m p : ℕ} (hm : Nat.factorial n + 1 = m ^ 2)
    (hp : p.Prime) (hpn : p ≤ n) : ¬ p ∣ m := by
  intro hpm
  have hpfac : p ∣ Nat.factorial n := Nat.dvd_factorial hp.pos hpn
  have hpm2 : p ∣ m ^ 2 := dvd_pow hpm (by norm_num)
  have hp1 : p ∣ 1 := (Nat.dvd_add_right hpfac).mp (hm ▸ hpm2)
  exact hp.not_dvd_one hp1

/-- For any prime `p ≥ 5` and integers `j ≥ 1`, `v ≥ 1`, we have `v_p(2j + 1) < 2 j v`,
ensuring strict ultrametric dominance of the linear term in the `p`-adic logarithm series. -/
theorem padicValNat_odd_series_strict_dom {p j v : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hj : 1 ≤ j) (hv : 1 ≤ v) :
    padicValNat p (2 * j + 1) < 2 * j * v := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : 2 * j + 1 < p ^ (2 * j) := by
    have h5 : 2 * j + 1 < 5 ^ (2 * j) := by
      induction j with
      | zero => omega
      | succ k ih =>
        cases k with
        | zero => norm_num
        | succ k' =>
          have ih' := ih (by omega)
          have hpow_step : 5 ^ (2 * (k' + 1 + 1)) = 25 * 5 ^ (2 * (k' + 1)) := by
            rw [show 2 * (k' + 1 + 1) = 2 * (k' + 1) + 2 by omega, pow_add]; ring
          omega
    exact lt_of_lt_of_le h5 (Nat.pow_le_pow_left hp5 (2 * j))
  have hdv : p ^ padicValNat p (2 * j + 1) ≤ 2 * j + 1 :=
    Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have hlt_pow : p ^ padicValNat p (2 * j + 1) < p ^ (2 * j) := lt_of_le_of_lt hdv hpow
  have hlt_2j : padicValNat p (2 * j + 1) < 2 * j :=
    (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt_pow
  have hle_mul : 2 * j ≤ 2 * j * v := Nat.le_mul_of_pos_right (2 * j) (by omega)
  omega

/-- **Equation (3.6) (Normalized `p`-Adic Regulator Valuation — Proved Directly in `ℚ_[p]`)**:
For any Brocard–Ramanujan solution `n! + 1 = m^2` with fundamental Pell unit `ε_n = X₁ + Y₁ √q_n`
and Pell index `k` (`m + s_n √q_n = ε_n^k`), if `p ∈ [5, n/2]` is a prime with `p ∤ k`, then
`realQuadPadicRegVal (q_n n) p = ⌊v_p(n!)/2⌋`. Proved with **zero Iwasawa axioms**. -/
theorem thm_1_2_eq_3_6_regulator_valuation {n m p X₁ Y₁ k : ℕ}
    (hm : Nat.factorial n + 1 = m ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hp_half : p ≤ n / 2)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk_eq : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ k)
    (hpk : ¬ p ∣ k) :
    realQuadPadicRegVal (q_n n) p = padicValNat p (Nat.factorial n) / 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, hs_val, hs_ge1⟩ := val_s_n_ge_one_on_half hp hp5 hp_half
  have hq2 : 2 ≤ q_n n := two_le_q_n (by omega)
  have hnsq : ¬ IsSquare (q_n n : ℤ) := q_n_not_isSquare (by omega) (by omega)
  have hpm : ¬ p ∣ m := brocard_p_not_dvd_m hm hp (by omega)
  have hm_pell : m ^ 2 = q_n n * (s_n n) ^ 2 + 1 := by
    have hfac := factorial_eq_q_n_mul_s_n_sq n
    omega
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at hk_eq
    have hs_pos : 0 < s_n n := by
      by_contra hs0; have hs0' : s_n n = 0 := by omega
      have hfac := factorial_eq_q_n_mul_s_n_sq n
      rw [hs0'] at hfac; simp at hfac
      exact Nat.factorial_ne_zero n hfac
    have hm_pos : 1 ≤ m := by
      by_contra hm0; have : m = 0 := by omega
      rw [this] at hm; simp at hm
    have hsqrt_pos : (0 : ℝ) < Real.sqrt (q_n n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < q_n n))
    have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
    have hsr : (0 : ℝ) < (s_n n : ℝ) := by exact_mod_cast hs_pos
    nlinarith
  have hreg_add := realQuadPadicRegVal_pell_power hp hp5 hq2 hnsq hfund hm_pell hk_eq hk1 hs_ge1 hpm
  have hvk : padicValNat p k = 0 := by
    rw [← Nat.factorization_def _ hp]
    exact Nat.factorization_eq_zero_of_not_dvd hpk
  omega

/-- **Theorem 1.2(i) (Parity-Independent Non-p-Rationality and p-Ramified Iwasawa Rank, eq. 1.8)**:
For any Brocard–Ramanujan solution `n! + 1 = m^2` and any prime `p ∈ [5, n/2]` with `p ∤ k`,
`v_p(R̃_p(K_n)) = ⌊v_p(n!)/2⌋` (proved directly in `ℚ_[p]`),
`v_p(L_p(1, χ_{D_n})) = v_p(#T_{K_n, p}) = v_p(h(q_n)) + ⌈v_p(n!)/2⌉ - 1`,
and for `p ∈ [5, n/3]` we have `v_p(#T_{K_n, p}) ≥ 1`, `K_n` is non-`p`-rational, and
`λ_p^*(K_n) = λ_p(χ_{D_n}) ≥ 1`. -/
theorem thm_1_2_part1_valuation_law {n m p X₁ Y₁ k : ℕ}
    (hm : Nat.factorial n + 1 = m ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hp_half : p ≤ n / 2)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk_eq : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ k)
    (hpk : ¬ p ∣ k) :
    let inv := canonicalRealQuadIwasawa (q_n n) p
    inv.v_Lp = padicValNat p (realQuadClassNumber (q_n n)) + (padicValNat p (Nat.factorial n) + 1) / 2 - 1 ∧
    inv.v_T = padicValNat p (realQuadClassNumber (q_n n)) + (padicValNat p (Nat.factorial n) + 1) / 2 - 1 ∧
    (p ≤ n / 3 →
      1 ≤ inv.v_T ∧ inv.is_p_rational = false ∧
      inv.lambda_star = inv.lambda_chi ∧ 1 ≤ inv.lambda_star) := by
  dsimp only
  have h_reg : realQuadPadicRegVal (q_n n) p = padicValNat p (Nat.factorial n) / 2 :=
    thm_1_2_eq_3_6_regulator_valuation hm hp hp5 hp_half hfund hk_eq hpk
  obtain ⟨hv2, _, _⟩ := val_s_n_ge_one_on_half hp hp5 hp_half
  have hreg_ge1 : 1 ≤ realQuadPadicRegVal (q_n n) p := by omega
  obtain ⟨h_unram, h_ram⟩ := leopoldt_coates_valuation_law (q := q_n n) (p := p) hp hp5 (q_n_squarefree n) hreg_ge1
  have hpn : p ≤ n := by omega
  have hp_dvd_q_iff := p_dvd_q_n_iff hp hpn
  have hLp_eq : (canonicalRealQuadIwasawa (q_n n) p).v_Lp =
      padicValNat p (realQuadClassNumber (q_n n)) +
      (padicValNat p (Nat.factorial n) + 1) / 2 - 1 := by
    by_cases hpd : p ∣ q_n n
    · have hodd := hp_dvd_q_iff.mp hpd
      rw [(h_ram hpd).1, h_reg]
      omega
    · have heven : padicValNat p (Nat.factorial n) % 2 = 0 := by
        by_contra h1
        exact hpd (hp_dvd_q_iff.mpr (by omega))
      rw [(h_unram hpd).1, h_reg]
      omega
  have hT_eq : (canonicalRealQuadIwasawa (q_n n) p).v_T =
      padicValNat p (realQuadClassNumber (q_n n)) +
      (padicValNat p (Nat.factorial n) + 1) / 2 - 1 := by
    by_cases hpd : p ∣ q_n n
    · have hodd := hp_dvd_q_iff.mp hpd
      rw [(h_ram hpd).2, h_reg]
      omega
    · have heven : padicValNat p (Nat.factorial n) % 2 = 0 := by
        by_contra h1
        exact hpd (hp_dvd_q_iff.mpr (by omega))
      rw [(h_unram hpd).2, h_reg]
      omega
  refine ⟨hLp_eq, hT_eq, fun hp_third => ?_⟩
  have h3p : 3 * p ≤ n := by omega
  have hv3 : 3 ≤ padicValNat p (Nat.factorial n) :=
    le_trans ((Nat.le_div_iff_mul_le hp.pos).mpr h3p) (padicValNat_factorial_ge_div hp (by omega))
  have hT_ge1 : 1 ≤ (canonicalRealQuadIwasawa (q_n n) p).v_T := by omega
  have h_not_prat : (canonicalRealQuadIwasawa (q_n n) p).is_p_rational = false := by
    by_contra htrue
    have hbool : (canonicalRealQuadIwasawa (q_n n) p).is_p_rational = true := by
      cases h : (canonicalRealQuadIwasawa (q_n n) p).is_p_rational <;> simp_all
    have h0 := (canonicalRealQuadIwasawa (q_n n) p).h_prat_iff.mp hbool
    omega
  obtain ⟨hlam_eq, hlam_ge1⟩ := iwasawa_main_conjecture_free_rank (q := q_n n) (p := p) hp hp5 hT_ge1
  exact ⟨hT_ge1, h_not_prat, hlam_eq, hlam_ge1⟩

/-- **Theorem 1.2(ii) (Unramified Iwasawa Module at Split Primes)**:
For any Brocard–Ramanujan solution `n! + 1 = m^2` and every split prime
`p ∈ Peven(n) ∩ [5, n/4]` (`realQuadSplits (q_n n) p = true`) with `p ∤ k`,
`|X(K_∞)_Γ| = |A_m^Γ| = |T_{K_n, p}|` for all `m ≥ v_p(n!)/2 - 1`,
`λ_p(K_n) + ν_p(K_n) ≥ v_p(n!)/2 - 1 ≥ 1`, and `n_0^(r) > r + 1 → λ_p(K_n) ≥ 1`. -/
theorem thm_1_2_part2_split_primes {n m p X₁ Y₁ k : ℕ}
    (hm : Nat.factorial n + 1 = m ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hp_quarter : p ≤ n / 4)
    (hp_even : p ∈ Peven n)
    (h_splits : realQuadSplits (q_n n) p = true)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk_eq : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ k)
    (hpk : ¬ p ∣ k) :
    let inv := canonicalRealQuadIwasawa (q_n n) p
    2 ≤ realQuadPadicRegVal (q_n n) p ∧
    (∀ m' : ℕ, padicValNat p (Nat.factorial n) / 2 - 1 ≤ m' →
      inv.v_X_Gamma = inv.v_T ∧ inv.v_A_m_Gamma m' = inv.v_T) ∧
    1 ≤ inv.lambda_p + inv.nu_p ∧
    inv.X_trivial = false ∧
    ((∀ r : ℕ, r + 1 < inv.n0_r r) → 1 ≤ inv.lambda_p) := by
  dsimp only
  have hp_half : p ≤ n / 2 := by omega
  have h_reg : realQuadPadicRegVal (q_n n) p = padicValNat p (Nat.factorial n) / 2 :=
    thm_1_2_eq_3_6_regulator_valuation hm hp hp5 hp_half hfund hk_eq hpk
  have h4p : 4 * p ≤ n := by omega
  have hv4 : 4 ≤ padicValNat p (Nat.factorial n) :=
    le_trans ((Nat.le_div_iff_mul_le hp.pos).mpr h4p) (padicValNat_factorial_ge_div hp (by omega))
  have hreg_ge2 : 2 ≤ realQuadPadicRegVal (q_n n) p := by omega
  have hp_ndvd_q : ¬ p ∣ q_n n := by
    have hev : padicValNat p (Nat.factorial n) % 2 = 0 := by
      unfold Peven at hp_even
      have := (Finset.mem_filter.mp hp_even).2.2
      omega
    intro hdvd
    have hodd := (p_dvd_q_n_iff hp (by omega)).mp hdvd
    omega
  obtain ⟨h_eqs, h_lam_nu, h_taya⟩ :=
    ozaki_taya_split_prime_iwasawa (q := q_n n) (p := p) hp hp5 hp_ndvd_q h_splits hreg_ge2
  have h_lam_nu_ge1 : 1 ≤ (canonicalRealQuadIwasawa (q_n n) p).lambda_p +
      (canonicalRealQuadIwasawa (q_n n) p).nu_p := by omega
  have h_X_not_triv : (canonicalRealQuadIwasawa (q_n n) p).X_trivial = false := by
    by_contra htrue
    have hbool : (canonicalRealQuadIwasawa (q_n n) p).X_trivial = true := by
      cases h : (canonicalRealQuadIwasawa (q_n n) p).X_trivial <;> simp_all
    obtain ⟨hl0, hn0⟩ := (canonicalRealQuadIwasawa (q_n n) p).h_X_triv.mp hbool
    omega
  refine ⟨hreg_ge2, ?_, h_lam_nu_ge1, h_X_not_triv, h_taya⟩
  intro m' hm'
  exact h_eqs m' (by omega)

/-! ### Explicit Finite Verification for `1 ≤ n < 116` (`n ∉ {4, 5, 7}`) -/

private def factMod : ℕ → ℕ → ℕ
  | 0, M => 1 % M
  | n + 1, M => ((n + 1) * factMod n M) % M

private lemma factMod_eq (n M : ℕ) : factMod n M = Nat.factorial n % M := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [factMod, Nat.factorial_succ, ih, Nat.mul_mod_mod]

private def isNotSqMod (n M : ℕ) : Bool :=
  let r := (factMod n M + 1) % M
  (List.range M).all (fun x => (x * x) % M != r)

private def brocardSmallWitnesses : List (ℕ × ℕ) :=
[
  (1, 4), (2, 4), (3, 4), (6, 11), (8, 11), (9, 11), (10, 13), (11, 13),
  (12, 29), (13, 23), (14, 31), (15, 37), (16, 19), (17, 19), (18, 31), (19, 23),
  (20, 29), (21, 31), (22, 37), (23, 59), (24, 31), (25, 31), (26, 29), (27, 29),
  (28, 43), (29, 37), (30, 37), (31, 41), (32, 41), (33, 37), (34, 37), (35, 37),
  (36, 41), (37, 43), (38, 53), (39, 43), (40, 43), (41, 43), (42, 47), (43, 61),
  (44, 53), (45, 53), (46, 71), (47, 53), (48, 53), (49, 67), (50, 53), (51, 53),
  (52, 59), (53, 59), (54, 67), (55, 59), (56, 59), (57, 59), (58, 61), (59, 61),
  (60, 67), (61, 67), (62, 89), (63, 67), (64, 67), (65, 67), (66, 71), (67, 71),
  (68, 79), (69, 73), (70, 83), (71, 79), (72, 83), (73, 79), (74, 79), (75, 83),
  (76, 97), (77, 89), (78, 83), (79, 83), (80, 83), (81, 83), (82, 89), (83, 89),
  (84, 97), (85, 103), (86, 101), (87, 101), (88, 101), (89, 101), (90, 101), (91, 97),
  (92, 97), (93, 97), (94, 101), (95, 103), (96, 107), (97, 101), (98, 101), (99, 101),
  (100, 139), (101, 113), (102, 107), (103, 109), (104, 107), (105, 107), (106, 109), (107, 109),
  (108, 127), (109, 113), (110, 137), (111, 131), (112, 127), (113, 127), (114, 139), (115, 151)
]

set_option maxRecDepth 8000 in
private lemma brocardSmallWitnesses_valid :
    brocardSmallWitnesses.all (fun p => decide (0 < p.2) && isNotSqMod p.1 p.2) = true := by
  decide

set_option maxRecDepth 8000 in
private lemma brocardSmallWitnesses_cover :
    (List.range 116).all (fun n =>
      decide (n = 0 ∨ n = 4 ∨ n = 5 ∨ n = 7) ||
      brocardSmallWitnesses.any (fun p => p.1 == n)) = true := by
  decide

/-- Pure kernel-verified finite check: for `1 ≤ n < 116`, the only solutions to
`n! + 1 = m^2` are `n ∈ {4, 5, 7}`. -/
theorem brocard_small_solutions_lt_116 {n m : ℕ} (hn1 : 1 ≤ n) (hn116 : n < 116)
    (hm : Nat.factorial n + 1 = m ^ 2) :
    n = 4 ∨ n = 5 ∨ n = 7 := by
  by_contra hnot
  have hcov := List.all_eq_true.mp brocardSmallWitnesses_cover n (List.mem_range.mpr hn116)
  have hnot_exc : decide (n = 0 ∨ n = 4 ∨ n = 5 ∨ n = 7) = false := by
    simp only [decide_eq_false_iff_not]; omega
  rw [hnot_exc, Bool.false_or] at hcov
  obtain ⟨⟨n', M⟩, hmem, hbeq⟩ := List.any_eq_true.mp hcov
  have hn_eq : n' = n := beq_iff_eq.mp hbeq
  subst hn_eq
  have hval := List.all_eq_true.mp brocardSmallWitnesses_valid (n', M) hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hval
  obtain ⟨hM_pos, hnsq⟩ := hval
  unfold isNotSqMod at hnsq
  have hx := List.all_eq_true.mp hnsq (m % M) (List.mem_range.mpr (Nat.mod_lt m hM_pos))
  have hsq_mod : (m % M * (m % M)) % M = (factMod n' M + 1) % M := by
    rw [factMod_eq, Nat.mod_add_mod, hm, sq]
    simp only [Nat.mod_mod, Nat.mul_mod]
  rw [hsq_mod] at hx; simp at hx

/-- **Theorem 1.2(iii) (Conditional Finiteness for `n ≥ 116`)**:
For any Brocard–Ramanujan solution `n! + 1 = m^2` with `n ≥ 116`, fundamental Pell unit
`ε_n = X₁ + Y₁ √q_n`, and Pell index `k` (`m + s_n √q_n = ε_n^k`):
- (a) `K_n` cannot be `p`-rational at any prime `p ∈ (n/5, n/3]`;
- (b) `X(K_∞)` cannot be trivial at any split prime `p ∈ Peven(n) ∩ [5, n/4]` with `p ∤ k`;
- (c) `λ_p(K_n) = 0` and `∀ r, r + 1 < n_0^(r)` cannot both hold at any split prime
  `p ∈ Peven(n) ∩ [5, n/4]` with `p ∤ k`. -/
theorem thm_1_2_part3_conditional_finiteness {n m p X₁ Y₁ k : ℕ}
    (hn : 116 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) (hp : p.Prime)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk_eq : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ k) :
    let inv := canonicalRealQuadIwasawa (q_n n) p
    ((n : ℝ) / 5 < (p : ℝ) → (p : ℝ) ≤ (n : ℝ) / 3 → inv.is_p_rational = true → False) ∧
    (5 ≤ p → p ≤ n / 4 → p ∈ Peven n → realQuadSplits (q_n n) p = true → ¬ p ∣ k → inv.X_trivial = true → False) ∧
    (5 ≤ p → p ≤ n / 4 → p ∈ Peven n → realQuadSplits (q_n n) p = true → ¬ p ∣ k →
      inv.lambda_p = 0 → (∀ r : ℕ, r + 1 < inv.n0_r r) → False) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro hlo hhi hprat
    have hp_gt23 : (23 : ℝ) < (p : ℝ) := by
      have : (116 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hp5 : 5 ≤ p := by
      by_contra hlt
      push_neg at hlt
      have : (p : ℝ) ≤ 4 := by exact_mod_cast (by omega : p ≤ 4)
      linarith
    have hp_third : p ≤ n / 3 := by
      have h3p : p * 3 ≤ n := by exact_mod_cast (by linarith : (p : ℝ) * 3 ≤ (n : ℝ))
      exact (Nat.le_div_iff_mul_le (by norm_num)).mpr h3p
    have hp_half : p ≤ n / 2 := by omega
    have hq_log := log_q_n_gt_point4 hn
    have heps_log := log_fund_pell_gt_point2 hq_log hfund
    obtain ⟨hk1, hk_lt, _⟩ := pell_index_upper_bound (by omega) hm hfund heps_log hk_eq
    have hpk : ¬ p ∣ k := (prime_in_band_val_and_coprime_k hn hp hlo hhi hk1 hk_lt).2
    have h_false := (thm_1_2_part1_valuation_law hm hp hp5 hp_half hfund hk_eq hpk).2.2 hp_third
    rw [h_false.2.1] at hprat
    contradiction
  · intro hp5 hp_q hp_ev h_spl hpk h_triv
    have h_res := thm_1_2_part2_split_primes hm hp hp5 hp_q hp_ev h_spl hfund hk_eq hpk
    rw [h_res.2.2.2.1] at h_triv
    contradiction
  · intro hp5 hp_q hp_ev h_spl hpk h_lam0 h_n0
    have h_res := thm_1_2_part2_split_primes hm hp hp5 hp_q hp_ev h_spl hfund hk_eq hpk
    have h1 := h_res.2.2.2.2 h_n0
    omega

/-- **Wieferich Congruence in `ℤ[√q_n]` (Manuscript Section 3.3, eq. for `p ∈ [5, n/4]`)**:
For any Brocard–Ramanujan solution `n! + 1 = m^2` and any prime `p ∈ [5, n/4]`, we have
`p^2 ∣ s_n n` and the Brocard Pell unit `u = m + s_n √q_n ∈ ℤ[√q_n]` satisfies
`u^2 ≡ 1 (mod p^2 ℤ[√q_n])` and hence `u^(p^2 - 1) ≡ 1 (mod p^2 ℤ[√q_n])` (pure kernel proof,
zero external axioms). -/
theorem thm_1_2_wieferich_congruence {n m p : ℕ}
    (hm : Nat.factorial n + 1 = m ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hp_q : p ≤ n / 4) :
    p ^ 2 ∣ s_n n ∧
    let u : Zsqrtd (q_n n : ℤ) := ⟨(m : ℤ), (s_n n : ℤ)⟩
    ((p : ℤ) ^ 2 ∣ (u ^ (p ^ 2 - 1) - 1).re) ∧
    ((p : ℤ) ^ 2 ∣ (u ^ (p ^ 2 - 1) - 1).im) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hv4 : 4 ≤ padicValNat p (Nat.factorial n) := by
    have hle : 4 * p ≤ n := by omega
    have h4 : 4 ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).mpr (by omega)
    have h1 := padicValNat_factorial_ge_div hp (by omega : 1 ≤ n)
    exact le_trans h4 h1
  have hfac_eq := factorial_eq_q_n_mul_s_n_sq n
  have hq_pos : 0 < q_n n := by
    unfold q_n; exact Finset.prod_pos (fun q hq => (Finset.mem_filter.mp hq).2.1.pos)
  have hs_pos : 0 < s_n n := by
    by_contra h0; push_neg at h0
    have hs0 : s_n n = 0 := by omega
    rw [hs0] at hfac_eq; simp at hfac_eq; exact (Nat.factorial_pos n).ne' hfac_eq
  have hv_split : padicValNat p (Nat.factorial n) =
      padicValNat p (q_n n) + 2 * padicValNat p (s_n n) := by
    rw [hfac_eq, sq, padicValNat.mul hq_pos.ne' (mul_ne_zero hs_pos.ne' hs_pos.ne'),
        padicValNat.mul hs_pos.ne' hs_pos.ne']
    omega
  have hv_q : padicValNat p (q_n n) ≤ 1 := by
    by_contra hgt; push_neg at hgt
    have hp2_dvd : p ^ 2 ∣ q_n n := by
      have := pow_padicValNat_dvd (p := p) (n := q_n n)
      exact dvd_trans (pow_dvd_pow p (by omega : 2 ≤ padicValNat p (q_n n))) this
    have hunit := (q_n_squarefree n) p (by simpa [sq] using hp2_dvd)
    rw [Nat.isUnit_iff] at hunit; exact hp.ne_one hunit
  have hv_s : 2 ≤ padicValNat p (s_n n) := by omega
  have hp2_s : p ^ 2 ∣ s_n n :=
    dvd_trans (pow_dvd_pow p hv_s) pow_padicValNat_dvd
  refine ⟨hp2_s, ?_⟩
  dsimp only
  set u : Zsqrtd (q_n n : ℤ) := ⟨(m : ℤ), (s_n n : ℤ)⟩
  have hp2_sz : (p : ℤ) ^ 2 ∣ (s_n n : ℤ) := by exact_mod_cast hp2_s
  have hu2 : ((p : ℤ) ^ 2 ∣ (u ^ 2 - 1).re) ∧ ((p : ℤ) ^ 2 ∣ (u ^ 2 - 1).im) := by
    have hre : (u ^ 2 - 1).re = 2 * (q_n n : ℤ) * (s_n n : ℤ) ^ 2 := by
      have hm_z : (m : ℤ) ^ 2 = (q_n n : ℤ) * (s_n n : ℤ) ^ 2 + 1 := by
        have : Nat.factorial n = q_n n * (s_n n) ^ 2 := hfac_eq
        zify at hm this; linarith
      rw [sq]
      change (m : ℤ) * (m : ℤ) + (q_n n : ℤ) * (s_n n : ℤ) * (s_n n : ℤ) - 1 = _
      rw [← sq, mul_assoc, ← sq]; linarith
    have him : (u ^ 2 - 1).im = 2 * (m : ℤ) * (s_n n : ℤ) := by
      rw [sq]
      change (m : ℤ) * (s_n n : ℤ) + (s_n n : ℤ) * (m : ℤ) - 0 = _
      ring
    rw [hre, him]
    exact ⟨dvd_mul_of_dvd_right (dvd_pow hp2_sz (by norm_num)) _, dvd_mul_of_dvd_right hp2_sz _⟩
  have hp_odd : p % 2 = 1 := by
    have h2 : p ≠ 2 := by omega
    exact Nat.Prime.eq_two_or_odd hp |>.resolve_left h2
  have heven : 2 ∣ p ^ 2 - 1 := by
    have : (p ^ 2) % 2 = 1 := by rw [sq, Nat.mul_mod, hp_odd]
    omega
  obtain ⟨t, ht⟩ := heven
  rw [ht]
  have hind : ∀ t : ℕ, ((p : ℤ) ^ 2 ∣ (u ^ (2 * t) - 1).re) ∧ ((p : ℤ) ^ 2 ∣ (u ^ (2 * t) - 1).im) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hpow : u ^ (2 * (t + 1)) - 1 = (u ^ (2 * t) - 1) * u ^ 2 + (u ^ 2 - 1) := by
        rw [show 2 * (t + 1) = 2 * t + 2 by omega, pow_add]; ring
      rw [hpow]
      set a := u ^ (2 * t) - 1
      set b := u ^ 2
      have hre : (a * b + (u ^ 2 - 1)).re = a.re * b.re + (q_n n : ℤ) * a.im * b.im + (u ^ 2 - 1).re := rfl
      have him : (a * b + (u ^ 2 - 1)).im = a.re * b.im + a.im * b.re + (u ^ 2 - 1).im := rfl
      rw [hre, him]
      refine ⟨dvd_add (dvd_add (dvd_mul_of_dvd_left ih.1 _) ?_) hu2.1,
              dvd_add (dvd_add (dvd_mul_of_dvd_left ih.1 _) (dvd_mul_of_dvd_left ih.2 _)) hu2.2⟩
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ih.2 _) _
  exact hind t

/-- **Theorem 1.2(iii) (Complete Conditional Finiteness over all `n ≥ 1`, Branches (a)–(c))**:
Combining `brocard_small_solutions_lt_116` with `thm_1_2_part3_conditional_finiteness`. -/
theorem thm_1_2_part3_complete_finiteness {n m X₁ Y₁ k : ℕ}
    (hn1 : 1 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk_eq : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ k)
    (h_cond : 116 ≤ n →
      (∃ p : ℕ, p.Prime ∧ (n : ℝ) / 5 < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) / 3 ∧
        (canonicalRealQuadIwasawa (q_n n) p).is_p_rational = true) ∨
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ≤ n / 4 ∧ p ∈ Peven n ∧
        realQuadSplits (q_n n) p = true ∧ ¬ p ∣ k ∧
        (canonicalRealQuadIwasawa (q_n n) p).X_trivial = true) ∨
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ≤ n / 4 ∧ p ∈ Peven n ∧
        realQuadSplits (q_n n) p = true ∧ ¬ p ∣ k ∧
        (canonicalRealQuadIwasawa (q_n n) p).lambda_p = 0 ∧
        (∀ r : ℕ, r + 1 < (canonicalRealQuadIwasawa (q_n n) p).n0_r r))) :
    n = 4 ∨ n = 5 ∨ n = 7 := by
  by_cases hn116 : n < 116
  · exact brocard_small_solutions_lt_116 hn1 hn116 hm
  · have hn_ge : 116 ≤ n := by omega
    exfalso
    rcases h_cond hn_ge with ⟨p, hp, hlo, hhi, hprat⟩ | ⟨p, hp, hp5, hpq, hpev, hspl, hpk, htriv⟩ |
      ⟨p, hp, hp5, hpq, hpev, hspl, hpk, hlam0, hn0⟩
    · exact (thm_1_2_part3_conditional_finiteness hn_ge hm hp hfund hk_eq).1 hlo hhi hprat
    · exact (thm_1_2_part3_conditional_finiteness hn_ge hm hp hfund hk_eq).2.1 hp5 hpq hpev hspl hpk htriv
    · exact (thm_1_2_part3_conditional_finiteness hn_ge hm hp hfund hk_eq).2.2 hp5 hpq hpev hspl hpk hlam0 hn0

end GrasGreenbergBrocard
