import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsSec3
import GrasGreenbergBrocard.PellFundamental

/-!
# Theorem 1.2: Non-p-Rationality, Iwasawa Invariants, and Conditional Finiteness

Formalizes Section 3.3 (Theorem 1.2(i)–(iii), eqs. 1.8 and 3.6–3.7) of the manuscript:
- `nagura_prime_in_band`: for every `n ≥ 116`, there exists a prime `p ∈ (n/5, n/4] ⊆ (n/5, n/3]`
  with `v_p(n!) = 4`
- `prime_in_band_val_and_coprime_k`: `v_p(n!) ∈ {3, 4}` and `p ∤ k` on `(n/5, n/3]`
- `val_s_n_ge_one_on_half`: `v_p(s_n) = ⌊v_p(n!)/2⌋ ≥ 1` on `[5, n/2]` (eq. 3.6)
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
    push Not at hle
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
    push Not at hle
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
  have hdiv_lt : n / p < 5 := Nat.div_lt_of_lt_mul (by linarith : n < p * 5)
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
        have hq_pr : q.Prime := (Finset.mem_filter.mp hq).2.1
        exact (Nat.coprime_primes hp hq_pr).mpr (fun h => hnot (h ▸ hq))
      exact hp.not_dvd_one (hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using dvd_mul_of_dvd_right hdvd 1))
    have hnd : ¬ 2 ∣ padicValNat p (Nat.factorial n) := (Finset.mem_filter.mp hmem).2.2
    omega
  · intro hodd
    unfold q_n
    apply Finset.dvd_prod_of_mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hpn⟩, hp, by omega⟩

/-- **Theorem 1.2(i) (Parity-Independent Non-p-Rationality and p-Ramified Iwasawa Rank, eq. 1.8)**:
For any prime `p ∈ [5, n/2]` with `v_p(R̃_p(K_n)) = ⌊v_p(n!)/2⌋`,
`v_p(L_p(1, χ_{D_n})) = v_p(#T_{K_n, p}) = v_p(h(q_n)) + ⌈v_p(n!)/2⌉ - 1`,
and for `p ∈ [5, n/3]` we have `v_p(#T_{K_n, p}) ≥ 1`, `K_n` is non-`p`-rational, and
`λ_p^*(K_n) = λ_p(χ_{D_n}) ≥ 1`. -/
theorem thm_1_2_part1_valuation_law {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp_half : p ≤ n / 2)
    (h_reg : (canonicalRealQuadIwasawa (q_n n) p).v_reg = padicValNat p (Nat.factorial n) / 2) :
    let inv := canonicalRealQuadIwasawa (q_n n) p
    inv.v_Lp = padicValNat p inv.classNumber + (padicValNat p (Nat.factorial n) + 1) / 2 - 1 ∧
    inv.v_T = padicValNat p inv.classNumber + (padicValNat p (Nat.factorial n) + 1) / 2 - 1 ∧
    (p ≤ n / 3 →
      1 ≤ inv.v_T ∧ inv.is_p_rational = false ∧
      inv.lambda_star = inv.lambda_chi ∧ 1 ≤ inv.lambda_star) := by
  dsimp only
  obtain ⟨hv2, _, _⟩ := val_s_n_ge_one_on_half hp hp5 hp_half
  have hreg_ge1 : 1 ≤ (canonicalRealQuadIwasawa (q_n n) p).v_reg := by omega
  obtain ⟨h_unram, h_ram⟩ := leopoldt_coates_valuation_law (q := q_n n) (p := p) hp hp5 hreg_ge1
  have hpn : p ≤ n := by omega
  have hp_dvd_q_iff := p_dvd_q_n_iff hp hpn
  have hLp_eq : (canonicalRealQuadIwasawa (q_n n) p).v_Lp =
      padicValNat p (canonicalRealQuadIwasawa (q_n n) p).classNumber +
        (padicValNat p (Nat.factorial n) + 1) / 2 - 1 := by
    by_cases hpd : p ∣ q_n n
    · have hodd := hp_dvd_q_iff.mp hpd
      have h1 := (h_ram hpd).1
      rw [h1, h_reg]
      omega
    · have heven : padicValNat p (Nat.factorial n) % 2 = 0 := by
        by_contra h1
        exact hpd (hp_dvd_q_iff.mpr (by omega))
      have h1 := (h_unram hpd).1
      rw [h1, h_reg]
      omega
  have hT_eq : (canonicalRealQuadIwasawa (q_n n) p).v_T =
      padicValNat p (canonicalRealQuadIwasawa (q_n n) p).classNumber +
        (padicValNat p (Nat.factorial n) + 1) / 2 - 1 := by
    by_cases hpd : p ∣ q_n n
    · have hodd := hp_dvd_q_iff.mp hpd
      have h1 := (h_ram hpd).2
      rw [h1, h_reg]
      omega
    · have heven : padicValNat p (Nat.factorial n) % 2 = 0 := by
        by_contra h1
        exact hpd (hp_dvd_q_iff.mpr (by omega))
      have h1 := (h_unram hpd).2
      rw [h1, h_reg]
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
For every split prime `p ∈ Peven(n) ∩ [5, n/4]` with `v_p(R̃_p(K_n)) = v_p(n!)/2`,
`|X(K_∞)_Γ| = |A_m^Γ| = |T_{K_n, p}|` for all `m ≥ v_p(n!)/2 - 1`,
`λ_p(K_n) + ν_p(K_n) ≥ v_p(n!)/2 - 1 ≥ 1`, and `n_0^{(r)} > r + 1 → λ_p(K_n) ≥ 1`. -/
theorem thm_1_2_part2_split_primes {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp_quarter : p ≤ n / 4)
    (hp_even : p ∈ Peven n)
    (h_splits : (canonicalRealQuadIwasawa (q_n n) p).splits = true)
    (h_reg : (canonicalRealQuadIwasawa (q_n n) p).v_reg = padicValNat p (Nat.factorial n) / 2) :
    let inv := canonicalRealQuadIwasawa (q_n n) p
    2 ≤ inv.v_reg ∧
    (∀ m : ℕ, padicValNat p (Nat.factorial n) / 2 - 1 ≤ m →
      inv.v_X_Gamma = inv.v_T ∧ inv.v_A_m_Gamma m = inv.v_T) ∧
    1 ≤ inv.lambda_p + inv.nu_p ∧
    inv.X_trivial = false ∧
    ((∀ r : ℕ, r + 1 < inv.n0_r r) → 1 ≤ inv.lambda_p) := by
  dsimp only
  have h4p : 4 * p ≤ n := by omega
  have hv4 : 4 ≤ padicValNat p (Nat.factorial n) :=
    le_trans ((Nat.le_div_iff_mul_le hp.pos).mpr h4p) (padicValNat_factorial_ge_div hp (by omega))
  have hreg_ge2 : 2 ≤ (canonicalRealQuadIwasawa (q_n n) p).v_reg := by omega
  have hp_ndvd_q : ¬ p ∣ q_n n := by
    have hev : padicValNat p (Nat.factorial n) % 2 = 0 := by
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
  intro m hm
  exact h_eqs m (by omega)

/-- **Theorem 1.2(iii) (Conditional Finiteness)**:
If for a solution `(n, m)` with `n ≥ 116`, any of (a) `K_n` is `p`-rational at some
`p ∈ (n/5, n/3]`, (b) `X(K_∞)` is trivial at some split `p ∈ Peven(n) ∩ [5, n/4]`, or
(c) `λ_p(K_n) = 0` and `n_0^{(r)} > r + 1` at some split `p ∈ Peven(n) ∩ [5, n/4]`,
then we obtain a contradiction. -/
theorem thm_1_2_part3_conditional_finiteness {n p : ℕ} (hn : 116 ≤ n) (hp : p.Prime)
    (h_reg : (canonicalRealQuadIwasawa (q_n n) p).v_reg = padicValNat p (Nat.factorial n) / 2) :
    let inv := canonicalRealQuadIwasawa (q_n n) p
    ((n : ℝ) / 5 < (p : ℝ) → (p : ℝ) ≤ (n : ℝ) / 3 → inv.is_p_rational = true → False) ∧
    (5 ≤ p → p ≤ n / 4 → p ∈ Peven n → inv.splits = true → inv.X_trivial = true → False) ∧
    (5 ≤ p → p ≤ n / 4 → p ∈ Peven n → inv.splits = true →
      inv.lambda_p = 0 → (∀ r : ℕ, r + 1 < inv.n0_r r) → False) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro hlo hhi hprat
    have hp_gt23 : (23 : ℝ) < (p : ℝ) := by
      have : (116 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hp5 : 5 ≤ p := by
      by_contra hlt
      push Not at hlt
      have : (p : ℝ) ≤ 4 := by exact_mod_cast (by omega : p ≤ 4)
      linarith
    have hp_third : p ≤ n / 3 := by
      have h3p : 3 * p ≤ n := by exact_mod_cast (by linarith : 3 * (p : ℝ) ≤ (n : ℝ))
      omega
    have hp_half : p ≤ n / 2 := by omega
    have h_false := (thm_1_2_part1_valuation_law hp hp5 hp_half h_reg).2.2 hp_third
    rw [h_false.2.1] at hprat
    contradiction
  · intro hp5 hp_q hp_ev h_spl h_triv
    have h_res := thm_1_2_part2_split_primes hp hp5 hp_q hp_ev h_spl h_reg
    rw [h_res.2.2.2.1] at h_triv
    contradiction
  · intro hp5 hp_q hp_ev h_spl h_lam0 h_n0
    have h_res := thm_1_2_part2_split_primes hp hp5 hp_q hp_ev h_spl h_reg
    have h1 := h_res.2.2.2.2 h_n0
    omega

end GrasGreenbergBrocard
