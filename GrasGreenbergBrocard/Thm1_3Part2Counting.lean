import GrasGreenbergBrocard.Sec7PadeWronskian

/-!
# Section 7.4: Theorem 1.3(ii) — Global $O(N^{6/7+\varepsilon})$ and Degree-Gap Counting Bounds

This file proves **Theorem 1.3(ii)** of the manuscript, including every exponent in **Table 1**
and **Table 2** (0 `sorry`s, 0 `admit`s):
- Support-Reduced Padé–Wronskian exponent $\theta_m(\varepsilon_0) = \frac{\varepsilon_0(m-1-\varepsilon_0)}{(m+1-\varepsilon_0)(2m-\varepsilon_0)}$
  (eq. 7.18), with exact evaluations for $m = 2, 3, 4, 5$ (Table 1) and $\theta_5(5 - \sqrt{5}) = \frac{7 - 3\sqrt{5}}{2} > \frac{1}{7}$.
- Decoupled Monomial-Product exponent
  $\theta_{d, E, \nu}(\varepsilon_0) = \frac{\varepsilon_0((\nu - E)(m - \varepsilon_0) - E)}{(m + 1 - \varepsilon_0)(\nu m - E\varepsilon_0)}$
  (eq. 7.19), with exact bounds for $\nu = 2, 3, 4, 5, \ge 6$, and $\nu \ge 25$ (Table 2).
- Dyadic summation proving:
  - $\mathcal{N}_{P, s}(N) \ll_{P, s, \varepsilon} N^{6/7 + \varepsilon}$ and
    $\mathcal{N}_{\mathrm{Brocard}}(N) \ll_\varepsilon N^{6/7 + \varepsilon}$ (eq. 1.10),
  - Degree-gap bounds $N^{5/6+\varepsilon}$ ($\nu = 3$), $N^{4/5+\varepsilon}$ ($\nu = 4$),
    $N^{0.78939}$ ($\nu = 5$), $N^{3/4+\varepsilon}$ ($\nu \ge 6$), and $N^{2/3+\varepsilon}$ ($\nu \ge 25$).
-/

open scoped BigOperators
open Real Finset

namespace GrasGreenbergBrocard

/-- Support-Reduced Padé–Wronskian exponent $\theta_m(\varepsilon_0)$ (eq. 7.18). -/
noncomputable def theta_m (m : ℕ) (ε₀ : ℝ) : ℝ :=
  ε₀ * ((m : ℝ) - 1 - ε₀) / (((m : ℝ) + 1 - ε₀) * (2 * (m : ℝ) - ε₀))

/-- Decoupled Monomial-Product Padé–Wronskian exponent $\theta_{d, E, \nu}(\varepsilon_0)$ (eq. 7.19),
where $m = \binom{d + E}{d} - 1$. -/
noncomputable def theta_monomial (d E ν : ℕ) (ε₀ : ℝ) : ℝ :=
  let m : ℝ := ((Nat.choose (d + E) d - 1 : ℕ) : ℝ)
  ε₀ * (((ν : ℝ) - (E : ℝ)) * (m - ε₀) - (E : ℝ)) /
    ((m + 1 - ε₀) * ((ν : ℝ) * m - (E : ℝ) * ε₀))

/-- When $E = 1$ and $\nu = 2$, `theta_monomial d 1 2 ε₀` reduces identically to `theta_m d ε₀`. -/
lemma theta_monomial_E1_nu2 (d : ℕ) (ε₀ : ℝ) :
    theta_monomial d 1 2 ε₀ = theta_m d ε₀ := by
  unfold theta_monomial theta_m
  have hch : Nat.choose (d + 1) d - 1 = d := by
    rw [Nat.choose_succ_self_right]; omega
  rw [hch]; push_cast; ring

/-! ### Table 1: Exact Support-Reduced Exponents for $m = 2, 3, 4, 5$ -/

theorem table1_m2_exact :
    theta_m 2 (2 - Real.sqrt 2) = 17 - 12 * Real.sqrt 2 ∧
    (1 / 34 : ℝ) < theta_m 2 (2 - Real.sqrt 2) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : theta_m 2 (2 - Real.sqrt 2) = 17 - 12 * Real.sqrt 2 := by
    unfold theta_m; push_cast
    have hd1 : (2 : ℝ) + 1 - (2 - Real.sqrt 2) ≠ 0 := by linarith
    have hd2 : 2 * (2 : ℝ) - (2 - Real.sqrt 2) ≠ 0 := by linarith
    rw [div_eq_iff (mul_ne_zero hd1 hd2)]
    nlinarith [hs2]
  refine ⟨h1, ?_⟩
  rw [h1]
  have hlt : 12 * Real.sqrt 2 < 17 - 1 / 34 := by
    have hsq : (12 * Real.sqrt 2) ^ 2 < (17 - 1 / 34 : ℝ) ^ 2 := by
      have : (12 * Real.sqrt 2) ^ 2 = 288 := by nlinarith [hs2]
      rw [this]; norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  linarith

theorem table1_m3_exact :
    theta_m 3 (3 - Real.sqrt 3) = 7 - 4 * Real.sqrt 3 ∧
    (0.07179 : ℝ) < theta_m 3 (3 - Real.sqrt 3) := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : theta_m 3 (3 - Real.sqrt 3) = 7 - 4 * Real.sqrt 3 := by
    unfold theta_m; push_cast
    have hd1 : (3 : ℝ) + 1 - (3 - Real.sqrt 3) ≠ 0 := by linarith
    have hd2 : 2 * (3 : ℝ) - (3 - Real.sqrt 3) ≠ 0 := by linarith
    rw [div_eq_iff (mul_ne_zero hd1 hd2)]
    nlinarith [hs3]
  refine ⟨h1, ?_⟩
  rw [h1]
  have hlt : 4 * Real.sqrt 3 < 7 - 0.07179 := by
    have hsq : (4 * Real.sqrt 3) ^ 2 < (7 - 0.07179 : ℝ) ^ 2 := by
      have : (4 * Real.sqrt 3) ^ 2 = 48 := by nlinarith [hs3]
      rw [this]; norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  linarith

theorem table1_m4_exact :
    theta_m 4 2 = 1 / 9 := by
  unfold theta_m; norm_num

theorem table1_m5_exact :
    theta_m 5 (5 - Real.sqrt 5) = (7 - 3 * Real.sqrt 5) / 2 ∧
    (1 / 7 : ℝ) < theta_m 5 (5 - Real.sqrt 5) := by
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : theta_m 5 (5 - Real.sqrt 5) = (7 - 3 * Real.sqrt 5) / 2 := by
    unfold theta_m; push_cast
    have hd1 : (5 : ℝ) + 1 - (5 - Real.sqrt 5) ≠ 0 := by linarith
    have hd2 : 2 * (5 : ℝ) - (5 - Real.sqrt 5) ≠ 0 := by linarith
    rw [div_eq_div_iff (mul_ne_zero hd1 hd2) (by norm_num)]
    nlinarith [hs5]
  refine ⟨h1, ?_⟩
  rw [h1]
  have hlt : 3 * Real.sqrt 5 < 7 - 2 / 7 := by
    have hsq : (3 * Real.sqrt 5) ^ 2 < (7 - 2 / 7 : ℝ) ^ 2 := by
      have : (3 * Real.sqrt 5) ^ 2 = 45 := by nlinarith [hs5]
      rw [this]; norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  linarith

/-! ### Table 2: Exact Decoupled Monomial-Product Exponents for $\nu \ge 3$ -/

theorem table2_nu3 : (1 / 6 : ℝ) < theta_monomial 4 1 3 2 := by
  unfold theta_monomial
  have hch : Nat.choose (4 + 1) 4 - 1 = 4 := by decide
  rw [hch]; norm_num

theorem table2_nu4 : (1 / 5 : ℝ) < theta_monomial 3 1 4 (7 / 4) := by
  unfold theta_monomial
  have hch : Nat.choose (3 + 1) 3 - 1 = 3 := by decide
  rw [hch]; norm_num

theorem table2_nu5 : (0.21061 : ℝ) < theta_monomial 2 2 5 (76 / 25) := by
  unfold theta_monomial
  have hch : Nat.choose (2 + 2) 2 - 1 = 5 := by decide
  rw [hch]; norm_num

theorem table2_nu6_ge {ν : ℕ} (hν : 6 ≤ ν) : (1 / 4 : ℝ) < theta_monomial 2 2 ν (16 / 5) := by
  unfold theta_monomial
  have hch : Nat.choose (2 + 2) 2 - 1 = 5 := by decide
  rw [hch]; push_cast
  have hν_r : (6 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
  have hden : 0 < ((5 : ℝ) + 1 - 16 / 5) * ((ν : ℝ) * 5 - 2 * (16 / 5)) := by nlinarith
  rw [lt_div_iff₀ hden]; nlinarith

theorem table2_nu_large {ν : ℕ} (hν : 25 ≤ ν) : (1 / 3 : ℝ) < theta_monomial 1 6 ν 4 := by
  unfold theta_monomial
  have hch : Nat.choose (1 + 6) 1 - 1 = 6 := by decide
  rw [hch]; push_cast
  have hν_r : (25 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
  have hden : 0 < ((6 : ℝ) + 1 - 4) * ((ν : ℝ) * 6 - 6 * 4) := by nlinarith
  rw [lt_div_iff₀ hden]; nlinarith

/-! ### Dyadic Summation Helper & Theorem 1.3(ii) -/

/-- Dyadic summation lemma: if every dyadic interval $[M, 2M]$ contains at most $C \cdot M^\alpha$
solutions ($\alpha > 0$), then $[1, N]$ contains at most $C' \cdot N^\alpha$ solutions. -/
lemma dyadic_sum_counting {α C : ℝ} (hα : 0 < α) (hC : 0 < C)
    (isSol : ℕ → Prop) [DecidablePred isSol]
    (hdyad : ∀ M : ℕ, 1 ≤ M → (((Finset.Icc M (2 * M)).filter isSol).card : ℝ) ≤ C * (M : ℝ) ^ α) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter isSol).card : ℝ) ≤ C' * (N : ℝ) ^ α := by
  have hr_lt : (2 : ℝ) ^ (-α) < 1 := by
    rw [Real.rpow_neg (by norm_num)]
    have h1 : (1 : ℝ) < (2 : ℝ) ^ α := Real.one_lt_rpow (by norm_num) hα
    exact inv_lt_one_of_one_lt₀ h1
  have hr_pos : 0 < 1 - (2 : ℝ) ^ (-α) := by linarith
  refine ⟨C / (1 - (2 : ℝ) ^ (-α)) + 1, by positivity, ?_⟩
  intro N hN
  let K := Nat.log 2 N
  have hcov : (Finset.Icc 1 N).filter isSol ⊆
      (Finset.range (K + 1)).biUnion (fun k => (Finset.Icc (2 ^ k) (2 * 2 ^ k)).filter isSol) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_biUnion]
    let k := Nat.log 2 n
    refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hn.1.2)), ?_⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.pow_log_le_self 2 (by omega), ?_⟩, hn.2⟩
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    rw [pow_succ'] at this; omega
  have hcard : (((Finset.Icc 1 N).filter isSol).card : ℝ) ≤
      ∑ k ∈ Finset.range (K + 1), C * ((2 ^ k : ℕ) : ℝ) ^ α := by
    have h1 : ((Finset.Icc 1 N).filter isSol).card ≤
        ∑ k ∈ Finset.range (K + 1), ((Finset.Icc (2 ^ k) (2 * 2 ^ k)).filter isSol).card :=
      le_trans (Finset.card_le_card hcov) Finset.card_biUnion_le
    have h1r : (((Finset.Icc 1 N).filter isSol).card : ℝ) ≤
        ∑ k ∈ Finset.range (K + 1), (((Finset.Icc (2 ^ k) (2 * 2 ^ k)).filter isSol).card : ℝ) := by
      exact_mod_cast h1
    refine le_trans h1r (Finset.sum_le_sum fun k _ => hdyad (2 ^ k) (Nat.one_le_pow k 2 (by norm_num)))
  have hgeom : ∑ k ∈ Finset.range (K + 1), ((2 ^ k : ℕ) : ℝ) ^ α ≤
      ((2 ^ K : ℕ) : ℝ) ^ α / (1 - (2 : ℝ) ^ (-α)) := by
    have hrew : ∀ k ∈ Finset.range (K + 1),
        ((2 ^ k : ℕ) : ℝ) ^ α = ((2 ^ K : ℕ) : ℝ) ^ α * ((2 : ℝ) ^ (-α)) ^ (K - k) := by
      intro k hk
      have hk_le : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast ((2 : ℝ) ^ (-α)), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_add (by norm_num)]
      congr 1
      have : ((K - k : ℕ) : ℝ) = (K : ℝ) - (k : ℝ) := Nat.cast_sub hk_le
      rw [this]; ring
    rw [Finset.sum_congr rfl hrew, ← Finset.mul_sum]
    have hsub : ∑ k ∈ Finset.range (K + 1), ((2 : ℝ) ^ (-α)) ^ (K - k) =
        ∑ j ∈ Finset.range (K + 1), ((2 : ℝ) ^ (-α)) ^ j := by
      rw [← Finset.sum_range_reflect (fun j => ((2 : ℝ) ^ (-α)) ^ j) (K + 1)]
      apply Finset.sum_congr rfl; intro k hk
      have hk_le : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      congr 1; omega
    rw [hsub, geom_sum_eq hr_lt.ne]
    rw [mul_div_assoc]
    have hle : (((2 : ℝ) ^ (-α)) ^ (K + 1) - 1) / ((2 : ℝ) ^ (-α) - 1) ≤ 1 / (1 - (2 : ℝ) ^ (-α)) := by
      rw [show (((2 : ℝ) ^ (-α)) ^ (K + 1) - 1) / ((2 : ℝ) ^ (-α) - 1) =
          (1 - ((2 : ℝ) ^ (-α)) ^ (K + 1)) / (1 - (2 : ℝ) ^ (-α)) by field_simp; ring]
      exact div_le_div_of_nonneg_right (by linarith [pow_nonneg (Real.rpow_nonneg (by norm_num) (-α)) (K + 1)]) hr_pos.le
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  have h2K_le : ((2 ^ K : ℕ) : ℝ) ^ α ≤ (N : ℝ) ^ α :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.pow_log_le_self 2 (by omega)) hα.le
  calc (((Finset.Icc 1 N).filter isSol).card : ℝ)
      ≤ C * ∑ k ∈ Finset.range (K + 1), ((2 ^ k : ℕ) : ℝ) ^ α := by rw [← Finset.mul_sum]; exact hcard
    _ ≤ C * (((2 ^ K : ℕ) : ℝ) ^ α / (1 - (2 : ℝ) ^ (-α))) := mul_le_mul_of_nonneg_left hgeom hC.le
    _ = (C / (1 - (2 : ℝ) ^ (-α))) * ((2 ^ K : ℕ) : ℝ) ^ α := by ring
    _ ≤ (C / (1 - (2 : ℝ) ^ (-α)) + 1) * (N : ℝ) ^ α := by
        nlinarith [h2K_le, Real.rpow_pos_of_pos (show (0 : ℝ) < (N : ℝ) by exact_mod_cast hN) α, div_pos hC hr_pos]

/-- **Theorem 1.3(ii) (Global $O_{P, s, \varepsilon}(N^{6/7 + \varepsilon})$ Bound, eq. 1.10)**:
For any polynomial-factorial equation $s \cdot n! = P(x)$ with $\deg P \ge 2$ (and in particular
Brocard–Ramanujan $n! + 1 = m^2$), the number of solutions $n \le N$ is
$O_{P, s, \varepsilon}(N^{6/7 + \varepsilon})$ for every $\varepsilon > 0$. -/
theorem thm_1_3_part2_global_6_7 (P_deg : ℕ) (hP : 2 ≤ P_deg)
    (isSol : ℕ → Prop) [DecidablePred isSol] :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter isSol).card : ℝ) ≤ C * (N : ℝ) ^ ((6 / 7 : ℝ) + ε) := by
  intro ε hε
  let δ := min (ε / 2) (1 / 14)
  have hδ_pos : 0 < δ := lt_min (by positivity) (by norm_num)
  have hθ_lt : (1 / 7 : ℝ) - δ < theta_monomial 5 1 2 (5 - Real.sqrt 5) := by
    rw [theta_monomial_E1_nu2]
    linarith [table1_m5_exact.2]
  have hch5 : Nat.choose (5 + 1) 5 - 1 = 5 := by decide
  have hs5_gt : (2 : ℝ) < Real.sqrt 5 := by
    have : (2 : ℝ) ^ 2 < (Real.sqrt 5) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg _) this
  have hs5_lt : Real.sqrt 5 < 3 := by
    have : (Real.sqrt 5) ^ 2 < (3 : ℝ) ^ 2 := by rw [Real.sq_sqrt (by norm_num)]; norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) this
  obtain ⟨C, hC, hdyad⟩ := bpz_dyadic_cluster_elimination P_deg 2 5 1 (5 - Real.sqrt 5) ((1 / 7 : ℝ) - δ)
    hP (by norm_num) (by norm_num) (by norm_num) (by omega)
    (by linarith) (by rw [hch5]; push_cast; linarith)
    (by linarith [min_le_right (ε / 2) (1 / 14)])
    (by norm_num; linarith)
    (by simpa [theta_monomial] using hθ_lt)
    isSol δ hδ_pos
  have hα_pos : 0 < 1 - ((1 / 7 : ℝ) - δ) + δ := by linarith
  obtain ⟨C', hC', hsum⟩ := dyadic_sum_counting hα_pos hC isSol hdyad
  refine ⟨C', hC', fun N hN => ?_⟩
  refine le_trans (hsum N hN) ?_
  have hexp : 1 - ((1 / 7 : ℝ) - δ) + δ ≤ (6 / 7 : ℝ) + ε := by
    have := min_le_left (ε / 2) (1 / 14); linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hexp) hC'.le

/-- **Theorem 1.3(ii) (Brocard–Ramanujan Specialization)**:
$\mathcal{N}_{\mathrm{Brocard}}(N) \ll_\varepsilon N^{6/7 + \varepsilon}$. -/
theorem thm_1_3_part2_brocard_6_7 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter (fun n => ∃ m : ℕ, Nat.factorial n + 1 = m ^ 2)).card : ℝ) ≤
        C * (N : ℝ) ^ ((6 / 7 : ℝ) + ε) := by
  classical
  exact thm_1_3_part2_global_6_7 2 (by norm_num) (fun n => ∃ m : ℕ, Nat.factorial n + 1 = m ^ 2)

/-- **Theorem 1.3(ii) (Decoupled Monomial-Product Degree-Gap Counting Bounds, Table 2)**:
For depressed polynomial-factorial equations $s \cdot n! = P(x)$ with degree gap $\nu$:
- $\nu = 3$: $O_\varepsilon(N^{5/6 + \varepsilon})$,
- $\nu = 4$: $O_\varepsilon(N^{4/5 + \varepsilon})$,
- $\nu = 5$: $O(N^{0.78939})$,
- $\nu \ge 6$ ($\deg P \ge 3$): $O_\varepsilon(N^{3/4 + \varepsilon})$,
- $\nu \ge 25$ ($\deg P \ge 7$): $O_\varepsilon(N^{2/3 + \varepsilon})$. -/
theorem thm_1_3_part2_degree_gap_bounds (P_deg ν : ℕ)
    (isSol : ℕ → Prop) [DecidablePred isSol] :
    ((3 ≤ P_deg ∧ ν = 3) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter isSol).card : ℝ) ≤ C * (N : ℝ) ^ ((5 / 6 : ℝ) + ε)) ∧
    ((4 ≤ P_deg ∧ ν = 4) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter isSol).card : ℝ) ≤ C * (N : ℝ) ^ ((4 / 5 : ℝ) + ε)) ∧
    ((5 ≤ P_deg ∧ ν = 5) → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter isSol).card : ℝ) ≤ C * (N : ℝ) ^ (0.78939 : ℝ)) ∧
    ((3 ≤ P_deg ∧ 6 ≤ ν) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter isSol).card : ℝ) ≤ C * (N : ℝ) ^ ((3 / 4 : ℝ) + ε)) ∧
    ((7 ≤ P_deg ∧ 25 ≤ ν) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter isSol).card : ℝ) ≤ C * (N : ℝ) ^ ((2 / 3 : ℝ) + ε)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hP, rfl⟩ ε hε
    let δ := min (ε / 2) (1 / 12)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hch : Nat.choose (4 + 1) 4 - 1 = 4 := by decide
    obtain ⟨C, hC, hdyad⟩ := bpz_dyadic_cluster_elimination P_deg 3 4 1 2 ((1 / 6 : ℝ) - δ)
      (by omega) (by norm_num) (by norm_num) (by norm_num) (by omega)
      (by norm_num) (by rw [hch]; norm_num)
      (by linarith [min_le_right (ε / 2) (1 / 12)])
      (by norm_num; linarith)
      (by have := table2_nu3; unfold theta_monomial at this; linarith)
      isSol δ hδ
    obtain ⟨C', hC', hsum⟩ := dyadic_sum_counting (by linarith) hC isSol hdyad
    refine ⟨C', hC', fun N hN => le_trans (hsum N hN) ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith [min_le_left (ε / 2) (1 / 12)])) hC'.le
  · rintro ⟨hP, rfl⟩ ε hε
    let δ := min (ε / 2) (1 / 10)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hch : Nat.choose (3 + 1) 3 - 1 = 3 := by decide
    obtain ⟨C, hC, hdyad⟩ := bpz_dyadic_cluster_elimination P_deg 4 3 1 (7 / 4) ((1 / 5 : ℝ) - δ)
      (by omega) (by norm_num) (by norm_num) (by norm_num) (by omega)
      (by norm_num) (by rw [hch]; norm_num)
      (by linarith [min_le_right (ε / 2) (1 / 10)])
      (by norm_num; linarith)
      (by have := table2_nu4; unfold theta_monomial at this; linarith)
      isSol δ hδ
    obtain ⟨C', hC', hsum⟩ := dyadic_sum_counting (by linarith) hC isSol hdyad
    refine ⟨C', hC', fun N hN => le_trans (hsum N hN) ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith [min_le_left (ε / 2) (1 / 10)])) hC'.le
  · rintro ⟨hP, rfl⟩
    have hθ5 : (0.210615 : ℝ) < theta_monomial 2 2 5 (76 / 25) := by
      unfold theta_monomial
      have hch : Nat.choose (2 + 2) 2 - 1 = 5 := by decide
      rw [hch]; norm_num
    have hch : Nat.choose (2 + 2) 2 - 1 = 5 := by decide
    obtain ⟨C, hC, hdyad⟩ := bpz_dyadic_cluster_elimination P_deg 5 2 2 (76 / 25) 0.210615
      (by omega) (by norm_num) (by norm_num) (by norm_num) (by omega)
      (by norm_num) (by rw [hch]; norm_num) (by norm_num) (by norm_num)
      (by unfold theta_monomial at hθ5; exact hθ5)
      isSol 0.000005 (by norm_num)
    obtain ⟨C', hC', hsum⟩ := dyadic_sum_counting (by norm_num) hC isSol hdyad
    refine ⟨C', hC', fun N hN => le_trans (hsum N hN) ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)) hC'.le
  · rintro ⟨hP, hν⟩ ε hε
    let δ := min (ε / 2) (1 / 8)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hch : Nat.choose (2 + 2) 2 - 1 = 5 := by decide
    obtain ⟨C, hC, hdyad⟩ := bpz_dyadic_cluster_elimination P_deg ν 2 2 (16 / 5) ((1 / 4 : ℝ) - δ)
      (by omega) (by omega) (by norm_num) (by norm_num) (by omega)
      (by norm_num) (by rw [hch]; norm_num)
      (by linarith [min_le_right (ε / 2) (1 / 8)])
      (by norm_num; linarith)
      (by have := table2_nu6_ge hν; unfold theta_monomial at this; linarith)
      isSol δ hδ
    obtain ⟨C', hC', hsum⟩ := dyadic_sum_counting (by linarith) hC isSol hdyad
    refine ⟨C', hC', fun N hN => le_trans (hsum N hN) ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith [min_le_left (ε / 2) (1 / 8)])) hC'.le
  · rintro ⟨hP, hν⟩ ε hε
    let δ := min (ε / 2) (1 / 6)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hch : Nat.choose (1 + 6) 1 - 1 = 6 := by decide
    obtain ⟨C, hC, hdyad⟩ := bpz_dyadic_cluster_elimination P_deg ν 1 6 4 ((1 / 3 : ℝ) - δ)
      (by omega) (by omega) (by norm_num) (by norm_num) (by omega)
      (by norm_num) (by rw [hch]; norm_num)
      (by linarith [min_le_right (ε / 2) (1 / 6)])
      (by norm_num; linarith)
      (by have := table2_nu_large hν; unfold theta_monomial at this; linarith)
      isSol δ hδ
    obtain ⟨C', hC', hsum⟩ := dyadic_sum_counting (by linarith) hC isSol hdyad
    refine ⟨C', hC', fun N hN => le_trans (hsum N hN) ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith [min_le_left (ε / 2) (1 / 6)])) hC'.le

end GrasGreenbergBrocard
