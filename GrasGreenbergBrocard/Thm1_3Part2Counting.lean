import GrasGreenbergBrocard.Sec7PadeWronskian
import GrasGreenbergBrocard.Sec7ClusterReduction

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
open Polynomial Real Finset

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
  -- Cover [1, N] by dyadic intervals [2^k, 2^(k+1)] for 0 ≤ k ≤ Nat.log 2 N
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
    dsimp only [k]
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
  -- Bound ∑_{k=0}^K (2^k)^α ≤ (2^K)^α / (1 - 2^(-α)) ≤ N^α / (1 - 2^(-α))
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
      refine Finset.sum_congr rfl fun k _ => by congr 1
    rw [hsub, geom_sum_eq hr_lt.ne]
    rw [div_eq_mul_one_div (((2 ^ K : ℕ) : ℝ) ^ α)]
    have hle : (((2 : ℝ) ^ (-α)) ^ (K + 1) - 1) / ((2 : ℝ) ^ (-α) - 1) ≤ 1 / (1 - (2 : ℝ) ^ (-α)) := by
      have hden_ne : (2 : ℝ) ^ (-α) - 1 ≠ 0 := sub_ne_zero.mpr hr_lt.ne
      have heq : (((2 : ℝ) ^ (-α)) ^ (K + 1) - 1) / ((2 : ℝ) ^ (-α) - 1) =
          (1 - ((2 : ℝ) ^ (-α)) ^ (K + 1)) / (1 - (2 : ℝ) ^ (-α)) := by
        field_simp [hden_ne, hr_pos.ne']; ring
      rw [heq]
      have hnum : 1 - ((2 : ℝ) ^ (-α)) ^ (K + 1) ≤ 1 := by
        have : (0 : ℝ) ≤ ((2 : ℝ) ^ (-α)) ^ (K + 1) := by positivity
        linarith
      exact div_le_div_of_nonneg_right hnum hr_pos.le
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  have h2K_le : ((2 ^ K : ℕ) : ℝ) ^ α ≤ (N : ℝ) ^ α :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.pow_log_le_self 2 (by omega)) hα.le
  calc (((Finset.Icc 1 N).filter isSol).card : ℝ)
      ≤ C * ∑ k ∈ Finset.range (K + 1), ((2 ^ k : ℕ) : ℝ) ^ α := by rw [Finset.mul_sum]; exact hcard
    _ ≤ C * (((2 ^ K : ℕ) : ℝ) ^ α / (1 - (2 : ℝ) ^ (-α))) := mul_le_mul_of_nonneg_left hgeom hC.le
    _ = (C / (1 - (2 : ℝ) ^ (-α))) * ((2 ^ K : ℕ) : ℝ) ^ α := by ring
    _ ≤ (C / (1 - (2 : ℝ) ^ (-α)) + 1) * (N : ℝ) ^ α := by
        nlinarith [h2K_le, Real.rpow_pos_of_pos (show (0 : ℝ) < (N : ℝ) by exact_mod_cast hN) α, div_pos hC hr_pos]

set_option maxHeartbeats 2000000 in
/-- **Theorem 7.4 (Dyadic Cluster Elimination via Support-Reduced Padé–Wronskian)**:
Proved directly in Lean by wiring:
1. `pigeonhole_cluster_reduction` (eq. 7.17) + `short_interval_pigeonhole`,
2. `bpz_lemma_4_2_taylor_family` + `lem_7_1_initial_pade_polynomials` (Siegel's Lemma),
3. Support extraction `S = {0} ∪ {i.succ | P_i ≠ 0}` + `siegel_ode_wronskian_on_support`,
4. `lem_7_3_support_reduced_wronskian` (Gauss's Lemma divisibility & multiplicity sum bound),
5. `bpz_cauchy_leibniz_pade_eval` + `lem_7_4_denominator_clearing`,
6. `pade_chi_lt_ratio_iff_theta_lt` (strict exponent contradiction $\chi(\theta) < (\nu - E)/E$). -/
theorem dyadic_cluster_elimination_proved (P_deg ν d E : ℕ) (ε₀ θ : ℝ)
    (hP : 2 ≤ P_deg) (hν : 2 ≤ ν) (hd : 1 ≤ d) (hE : 1 ≤ E)
    (hE_le : E ≤ min (P_deg - 1) (ν - 1))
    (hε0_pos : 0 < ε₀)
    (hε0_lt : ε₀ < ((Nat.choose (d + E) d - 1 : ℕ) : ℝ) - 1)
    (hθ_pos : 0 < θ)
    (hθ_cap : θ < 1 / ((d : ℝ) + 2))
    (hθ_pade : θ <
      ε₀ * (((ν : ℝ) - (E : ℝ)) * (((Nat.choose (d + E) d - 1 : ℕ) : ℝ) - ε₀) - (E : ℝ)) /
        ((((Nat.choose (d + E) d - 1 : ℕ) : ℝ) + 1 - ε₀) *
          ((ν : ℝ) * ((Nat.choose (d + E) d - 1 : ℕ) : ℝ) - (E : ℝ) * ε₀)))
    (s_mult : ℕ) (hs_mult : 1 ≤ s_mult) (P : ℤ[X])
    (hP_deg : P.natDegree = P_deg) (hP_gap : HasDepressedDegreeGap P ν)
    [DecidablePred (IsPolyFactSol s_mult P)] :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc N (2 * N)).filter (IsPolyFactSol s_mult P)).card : ℝ) ≤
        C * (N : ℝ) ^ (1 - θ + δ) := by
  intro δ hδ
  set m : ℕ := Nat.choose (d + E) d - 1
  have hm_gt1 : (1 : ℝ) < (m : ℝ) := by linarith
  have hm1 : 1 ≤ m := by
    by_contra hlt; push_neg at hlt
    have : (m : ℝ) = 0 := by exact_mod_cast (show m = 0 by omega)
    linarith
  have hEν : E < ν := by omega
  have hEr : E ≤ P_deg - 1 := by omega
  obtain ⟨hB_pos, hchi_lt⟩ := pade_chi_lt_ratio_iff_theta_lt hE hEν hε0_pos hε0_lt hθ_pos hθ_pade
  set α₁ : ℝ := ((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) / ε₀
  set α₂ : ℝ := (m : ℝ) * ((m : ℝ) + 1 - ε₀) / ε₀
  set A_num : ℝ := 1 + α₁ * θ
  set B_den : ℝ := ((m : ℝ) - ε₀) - α₂ * θ
  have hα₁_pos : 0 < α₁ := by
    have : 0 < (m : ℝ) - ε₀ := by linarith
    have : 0 < (m : ℝ) + 1 - ε₀ := by linarith
    positivity
  have hα₂_pos : 0 < α₂ := by
    have : 0 < (m : ℝ) := by positivity
    have : 0 < (m : ℝ) + 1 - ε₀ := by linarith
    positivity
  have hA_pos : 0 < A_num := by dsimp [A_num]; nlinarith
  have hE_pos : (0 : ℝ) < (E : ℝ) := by exact_mod_cast (show 0 < E by omega)
  have hP_rpos : (0 : ℝ) < (P_deg : ℝ) := by exact_mod_cast (show 0 < P_deg by omega)
  have hνE_pos : (0 : ℝ) < (ν : ℝ) - (E : ℝ) := by
    have : (E : ℝ) < (ν : ℝ) := by exact_mod_cast hEν
    linarith
  set γ : ℝ := ((ν : ℝ) - (E : ℝ)) * B_den - (E : ℝ) * A_num
  have hγ_pos : 0 < γ := by
    have h1 := (div_lt_div_iff₀ hB_pos hE_pos).mp hchi_lt
    dsimp [γ]; linarith
  set η : ℝ := min (B_den / 8) (min (γ / (16 * ((ν : ℝ) + 1) * (B_den + A_num + 1))) (1 / 16))
  have hη_pos : 0 < η := by positivity
  have hη_le_B : η ≤ B_den / 8 := min_le_left _ _
  have hη_le_16 : η ≤ 1 / 16 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hη_le_γ : η ≤ γ / (16 * ((ν : ℝ) + 1) * (B_den + A_num + 1)) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hBη_pos : 0 < B_den - η := by linarith
  obtain ⟨C_1, C_2, C_3, C_0, hC1, hC2, hC3, hC0, h_bpz_eval⟩ :=
    bpz_cauchy_leibniz_pade_eval P_deg ν d E ε₀ s_mult P hP hν hd hE hE_le hε0_pos hε0_lt
      hs_mult hP_deg hP_gap
  have h_gap_theta : 0 < 1 - ((d : ℝ) + 2) * θ := by
    have hd2_pos : (0 : ℝ) < (d : ℝ) + 2 := by positivity
    have h1 := (lt_div_iff₀ hd2_pos).mp hθ_cap
    linarith
  have hθ_lt_1 : θ < 1 := by
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  -- Collect all asymptotic thresholds via Filter.Eventually atTop
  have hN_top : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlog_top : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hN_top
  set K_lin : ℝ := (32 * (B_den + 1) * (P_deg : ℝ) / η) *
      (((m : ℝ) / ε₀) * Real.log 10 + (E : ℝ) + Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) +
        (10 * (m : ℝ) + 2) + C_0 + 10 +
        Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1)
  have h_ev : ∀ᶠ N : ℕ in Filter.atTop,
      4 ≤ N ∧
      (max 2 (d * P_deg : ℕ) : ℝ) + 2 ≤ (N : ℝ) ^ θ ∧
      (8 : ℝ) < (N : ℝ) ^ (1 - θ) ∧
      (8 * (d * P_deg : ℕ) + 4 : ℝ) ≤ (N : ℝ) ^ δ ∧
      ((1024 * (2 : ℝ) ^ d * ((m + 1 : ℕ) : ℝ) / η) + 8 * (2 : ℝ) ^ d) * Real.log (N : ℝ) <
        (N : ℝ) ^ (1 - ((d : ℝ) + 2) * θ + δ) ∧
      max 4 (max ((α₂ * Real.log C_2 + Real.log 2 + (η / 16) * Real.log C_3 + 1) * (8 / η))
        ((α₁ * Real.log C_1 + Real.log 2 + Real.log (P_deg : ℝ) + 1) * (8 / η))) ≤ Real.log (N : ℝ) ∧
      K_lin * (N : ℝ) < ((N / 2 : ℕ) : ℝ) * Real.log ((N / 2 : ℕ) : ℝ) ∧
      ((2048 * ((m + 1 : ℕ) : ℝ) * (P_deg : ℝ) * (B_den - η) / (η * (E : ℝ))) + 1) * Real.log (N : ℝ) <
        (N : ℝ) ^ (1 - θ) := by
    refine Filter.Eventually.and (Filter.eventually_ge_atTop 4) ?_
    refine Filter.Eventually.and (((tendsto_rpow_atTop hθ_pos).comp hN_top).eventually (Filter.eventually_ge_atTop _)) ?_
    refine Filter.Eventually.and (((tendsto_rpow_atTop (by linarith : 0 < 1 - θ)).comp hN_top).eventually (Filter.eventually_gt_atTop 8)) ?_
    refine Filter.Eventually.and (((tendsto_rpow_atTop hδ).comp hN_top).eventually (Filter.eventually_ge_atTop _)) ?_
    refine Filter.Eventually.and (eventually_mul_log_lt_rpow (by linarith : 0 < 1 - ((d : ℝ) + 2) * θ + δ)) ?_
    refine Filter.Eventually.and (hlog_top.eventually (Filter.eventually_ge_atTop _)) ?_
    refine Filter.Eventually.and (eventually_linear_lt_half_log K_lin) ?_
    exact eventually_mul_log_lt_rpow (by linarith : 0 < 1 - θ)
  rw [Filter.eventually_atTop] at h_ev
  obtain ⟨N₀, hN₀⟩ := h_ev
  refine ⟨max 1 ((N₀ + 2 : ℕ) : ℝ), by positivity, ?_⟩
  intro N hN1
  by_cases hN_small : N < N₀
  · have hcard_le : ((Finset.Icc N (2 * N)).filter (IsPolyFactSol s_mult P)).card ≤ N + 1 := by
      calc ((Finset.Icc N (2 * N)).filter (IsPolyFactSol s_mult P)).card
          ≤ (Finset.Icc N (2 * N)).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = N + 1 := by rw [Nat.card_Icc]; omega
    have hcard_r : (((Finset.Icc N (2 * N)).filter (IsPolyFactSol s_mult P)).card : ℝ) ≤ ((N₀ + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show ((Finset.Icc N (2 * N)).filter (IsPolyFactSol s_mult P)).card ≤ N₀ + 2 by omega)
    have hpow_ge1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - θ + δ) :=
      Real.one_le_rpow (by exact_mod_cast hN1) (by linarith)
    have hC_ge : ((N₀ + 2 : ℕ) : ℝ) ≤ max 1 ((N₀ + 2 : ℕ) : ℝ) := le_max_right _ _
    nlinarith
  · have hN_ge : N₀ ≤ N := by omega
    obtain ⟨hN4, hM_big, hN1mθ, hNδ, hgap_log, hlogN_big, hKlin, hM_D_log⟩ := hN₀ N hN_ge
    by_contra hgt
    push_neg at hgt
    set S_sol := (Finset.Icc N (2 * N)).filter (IsPolyFactSol s_mult P)
    set M : ℕ := Nat.floor ((N : ℝ) ^ θ)
    set L : ℕ := max 1 (Nat.ceil (Real.log (N : ℝ)))
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hlogN_ge4 : (4 : ℝ) ≤ Real.log (N : ℝ) := le_trans (le_max_left _ _) hlogN_big
    have hlogN_le_N : Real.log (N : ℝ) ≤ (N : ℝ) := le_trans (Real.log_le_sub_one_of_pos hN_pos) (by linarith)
    have hM_le_rpow : (M : ℝ) ≤ (N : ℝ) ^ θ := Nat.floor_le (by positivity)
    have hrpow_lt_M1 : (N : ℝ) ^ θ < (M : ℝ) + 1 := Nat.lt_floor_add_one _
    have hM_ge_max : max 2 (d * P_deg) ≤ M := by
      have : ((max 2 (d * P_deg) : ℕ) : ℝ) < (M : ℝ) + 1 := by simp only [Nat.cast_max, Nat.cast_ofNat]; linarith
      have : (max 2 (d * P_deg) : ℕ) < M + 1 := by exact_mod_cast this
      omega
    have hM1 : 1 ≤ M := by omega
    have hMdP : d * P_deg ≤ M := le_trans (le_max_right _ _) hM_ge_max
    have hM2_r : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_trans (le_max_left _ _) hM_ge_max)
    have hM_half : (1 / 2 : ℝ) * (N : ℝ) ^ θ ≤ (M : ℝ) := by linarith
    have hM1_le : ((M + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ θ := by push_cast; linarith
    have h8M : 8 * M < N := by
      have hmul : (N : ℝ) ^ (1 - θ) * (N : ℝ) ^ θ = (N : ℝ) := by rw [← Real.rpow_add hN_pos]; simp
      have : ((8 * M : ℕ) : ℝ) < (N : ℝ) := by push_cast; nlinarith [Real.rpow_pos_of_pos hN_pos θ]
      exact_mod_cast this
    have hL1 : 1 ≤ L := le_max_left _ _
    have hL_le : (L : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      have h1_le : 1 ≤ Nat.ceil (Real.log (N : ℝ)) := Nat.one_le_iff_ne_zero.mpr (by
        intro h0; have := Nat.ceil_eq_zero.mp h0; linarith)
      have hL_eq : L = Nat.ceil (Real.log (N : ℝ)) := max_eq_right h1_le
      rw [hL_eq]; linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ Real.log (N : ℝ))]
    have hL_ge_log : Real.log (N : ℝ) ≤ (L : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right 1 _)
    have hS_gt : (N : ℝ) ^ (1 - θ + δ) < (S_sol.card : ℝ) := by
      have h1 : (1 : ℝ) ≤ max 1 ((N₀ + 2 : ℕ) : ℝ) := le_max_left _ _
      nlinarith [Real.rpow_pos_of_pos hN_pos (1 - θ + δ)]
    -- Step 1 & 2: Pigeonhole cluster reduction (eq. 7.17) + short-interval Pigeonhole
    obtain ⟨β, hβ_prop, hβ_mono, T, hT_sub, hT_sol, hT_card⟩ :=
      pigeonhole_cluster_reduction hM1 hd hP hMdP S_sol (Finset.filter_subset _ _)
    obtain ⟨N', hN'_lo, hN'_hi, T', hT'_sub, hT'_int, hT'_card⟩ :=
      short_interval_pigeonhole hL1 T (Finset.Subset.trans hT_sub (Finset.filter_subset _ _))
    have hbad_bd : ((d * P_deg * (N / M + 1) : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * (N : ℝ) ^ (1 - θ + δ) := by
      have hdiv : ((N / M : ℕ) : ℝ) ≤ (N : ℝ) / (M : ℝ) := Nat.cast_div_le
      have hNdivM : (N : ℝ) / (M : ℝ) ≤ 2 * (N : ℝ) ^ (1 - θ) := by
        rw [div_le_iff₀ (by exact_mod_cast (show 0 < M by omega))]
        have hmul : (N : ℝ) ^ (1 - θ) * (N : ℝ) ^ θ = (N : ℝ) := by rw [← Real.rpow_add hN_pos]; simp
        nlinarith [Real.rpow_pos_of_pos hN_pos (1 - θ)]
      have h1mθ_ge1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - θ) := Real.one_le_rpow (by linarith) (by linarith)
      have hcomb : (N : ℝ) ^ (1 - θ) * (N : ℝ) ^ δ = (N : ℝ) ^ (1 - θ + δ) := (Real.rpow_add hN_pos _ _).symm
      have hNM1 : ((N / M : ℕ) : ℝ) + 1 ≤ 3 * (N : ℝ) ^ (1 - θ) := by linarith
      have hdP_nn : (0 : ℝ) ≤ ((d * P_deg : ℕ) : ℝ) := by positivity
      have h1 : ((d * P_deg * (N / M + 1) : ℕ) : ℝ) ≤
          ((d * P_deg : ℕ) : ℝ) * (3 * (N : ℝ) ^ (1 - θ)) := by
        push_cast; exact mul_le_mul_of_nonneg_left hNM1 hdP_nn
      have h2 : 3 * ((d * P_deg : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * (N : ℝ) ^ δ := by linarith
      calc ((d * P_deg * (N / M + 1) : ℕ) : ℝ)
          ≤ (3 * ((d * P_deg : ℕ) : ℝ)) * (N : ℝ) ^ (1 - θ) := by linarith
        _ ≤ ((1 / 2 : ℝ) * (N : ℝ) ^ δ) * (N : ℝ) ^ (1 - θ) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = (1 / 2 : ℝ) * (N : ℝ) ^ (1 - θ + δ) := by rw [← hcomb]; ring
    have hT'_lower : (1 / 2 : ℝ) * (N : ℝ) ^ (1 - ((d : ℝ) + 2) * θ + δ) * (N : ℝ) ^ θ ≤
        (2 : ℝ) ^ d * (L : ℝ) * (T'.card : ℝ) := by
      have h1 : (1 / 2 : ℝ) * (N : ℝ) ^ (1 - θ + δ) ≤ ((M + 1) ^ d : ℝ) * (T.card : ℝ) := by
        have hT_r : (S_sol.card : ℝ) ≤ ((d * P_deg * (N / M + 1) : ℕ) : ℝ) + ((M + 1) ^ d : ℝ) * (T.card : ℝ) := by
          exact_mod_cast hT_card
        linarith
      have h2 : ((M + 1) ^ d : ℝ) ≤ (2 : ℝ) ^ d * (N : ℝ) ^ ((d : ℝ) * θ) := by
        have ha : (((M + 1 : ℕ) : ℝ) ^ d) ≤ (2 * (N : ℝ) ^ θ) ^ d := pow_le_pow_left₀ (by positivity) hM1_le d
        rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ θ) d, ← Real.rpow_mul hN_pos.le, mul_comm θ (d : ℝ)] at ha
        exact_mod_cast ha
      have hT'_r : (T.card : ℝ) ≤ (L : ℝ) * (T'.card : ℝ) := by exact_mod_cast hT'_card
      have hsplit : (N : ℝ) ^ (1 - θ + δ) = (N : ℝ) ^ (1 - ((d : ℝ) + 2) * θ + δ) * (N : ℝ) ^ θ * (N : ℝ) ^ ((d : ℝ) * θ) := by
        rw [← Real.rpow_add hN_pos, ← Real.rpow_add hN_pos]; congr 1; ring
      have hprod : ((1 / 2 : ℝ) * (N : ℝ) ^ (1 - ((d : ℝ) + 2) * θ + δ) * (N : ℝ) ^ θ) * (N : ℝ) ^ ((d : ℝ) * θ) ≤
          ((2 : ℝ) ^ d * (L : ℝ) * (T'.card : ℝ)) * (N : ℝ) ^ ((d : ℝ) * θ) := by
        calc ((1 / 2 : ℝ) * (N : ℝ) ^ (1 - ((d : ℝ) + 2) * θ + δ) * (N : ℝ) ^ θ) * (N : ℝ) ^ ((d : ℝ) * θ)
            = (1 / 2 : ℝ) * (N : ℝ) ^ (1 - θ + δ) := by rw [hsplit]; ring
          _ ≤ ((M + 1) ^ d : ℝ) * (T.card : ℝ) := h1
          _ ≤ ((2 : ℝ) ^ d * (N : ℝ) ^ ((d : ℝ) * θ)) * ((L : ℝ) * (T'.card : ℝ)) :=
              mul_le_mul h2 hT'_r (by positivity) (by positivity)
          _ = ((2 : ℝ) ^ d * (L : ℝ) * (T'.card : ℝ)) * (N : ℝ) ^ ((d : ℝ) * θ) := by ring
      exact le_of_mul_le_mul_right hprod (Real.rpow_pos_of_pos hN_pos ((d : ℝ) * θ))
    have hT'_pos : 1 ≤ T'.card := by
      have h1 : (2 : ℝ) ^ d * (L : ℝ) ≤ (2 : ℝ) ^ d * (2 * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hL_le (by positivity)
      have hrθ_ge1 : (1 : ℝ) ≤ (N : ℝ) ^ θ := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) hθ_pos.le
      have h2 : (2 : ℝ) ^ d * (L : ℝ) < (1 / 2 : ℝ) * (N : ℝ) ^ (1 - ((d : ℝ) + 2) * θ + δ) * (N : ℝ) ^ θ := by
        have ha : 8 * (2 : ℝ) ^ d * Real.log (N : ℝ) < (N : ℝ) ^ (1 - ((d : ℝ) + 2) * θ + δ) := by
          have : 0 ≤ (1024 * (2 : ℝ) ^ d * ((m + 1 : ℕ) : ℝ) / η) * Real.log (N : ℝ) := by positivity
          linarith
        nlinarith
      have h3 : (1 : ℝ) ≤ (T'.card : ℝ) := by
        by_contra hlt; push_neg at hlt
        have h0 : (T'.card : ℝ) = 0 := by
          have : T'.card = 0 := by exact_mod_cast (show (T'.card : ℝ) < 1 from hlt) |> Nat.lt_one_iff.mp
          exact_mod_cast this
        rw [h0, mul_zero] at hT'_lower; linarith [show (0 : ℝ) < (2 : ℝ) ^ d * (L : ℝ) by positivity]
      exact_mod_cast h3
    have hT'_M_small : (((m + 1 : ℕ) : ℝ) * (M : ℝ)) / (T'.card : ℝ) ≤ η / 256 := by
      rw [div_le_iff₀ (by exact_mod_cast (show 0 < T'.card by omega))]
      have ha : (1024 * (2 : ℝ) ^ d * ((m + 1 : ℕ) : ℝ) / η) * Real.log (N : ℝ) <
          (N : ℝ) ^ (1 - ((d : ℝ) + 2) * θ + δ) := by
        have : 0 ≤ 8 * (2 : ℝ) ^ d * Real.log (N : ℝ) := by positivity
        linarith
      have hb : (2 : ℝ) ^ d * (L : ℝ) * (((m + 1 : ℕ) : ℝ) * (M : ℝ)) ≤
          (η / 256) * ((1 / 2 : ℝ) * (N : ℝ) ^ (1 - ((d : ℝ) + 2) * θ + δ) * (N : ℝ) ^ θ) := by
        have h1 : (2 : ℝ) ^ d * (L : ℝ) * (((m + 1 : ℕ) : ℝ) * (M : ℝ)) ≤
            (2 * (2 : ℝ) ^ d * ((m + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) * (N : ℝ) ^ θ := by
          have hL' : (2 : ℝ) ^ d * (L : ℝ) ≤ (2 : ℝ) ^ d * (2 * Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hL_le (by positivity)
          have hM' : ((m + 1 : ℕ) : ℝ) * (M : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (N : ℝ) ^ θ :=
            mul_le_mul_of_nonneg_left hM_le_rpow (by positivity)
          calc (2 : ℝ) ^ d * (L : ℝ) * (((m + 1 : ℕ) : ℝ) * (M : ℝ))
              ≤ ((2 : ℝ) ^ d * (2 * Real.log (N : ℝ))) * (((m + 1 : ℕ) : ℝ) * (N : ℝ) ^ θ) :=
                mul_le_mul hL' hM' (by positivity) (by positivity)
            _ = (2 * (2 : ℝ) ^ d * ((m + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) * (N : ℝ) ^ θ := by ring
        have h2 : 2 * (2 : ℝ) ^ d * ((m + 1 : ℕ) : ℝ) * Real.log (N : ℝ) ≤
            (η / 512) * (N : ℝ) ^ (1 - ((d : ℝ) + 2) * θ + δ) := by
          have hmul := mul_lt_mul_of_pos_left ha (show 0 < η / 512 by positivity)
          have hsimp : η / 512 * ((1024 * (2 : ℝ) ^ d * ((m + 1 : ℕ) : ℝ) / η) * Real.log (N : ℝ)) =
              2 * (2 : ℝ) ^ d * ((m + 1 : ℕ) : ℝ) * Real.log (N : ℝ) := by field_simp [hη_pos.ne']; ring
          rw [hsimp] at hmul; linarith
        calc (2 : ℝ) ^ d * (L : ℝ) * (((m + 1 : ℕ) : ℝ) * (M : ℝ))
            ≤ (2 * (2 : ℝ) ^ d * ((m + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) * (N : ℝ) ^ θ := h1
          _ ≤ ((η / 512) * (N : ℝ) ^ (1 - ((d : ℝ) + 2) * θ + δ)) * (N : ℝ) ^ θ :=
              mul_le_mul_of_nonneg_right h2 (Real.rpow_pos_of_pos hN_pos θ).le
          _ = (η / 256) * ((1 / 2 : ℝ) * (N : ℝ) ^ (1 - ((d : ℝ) + 2) * θ + δ) * (N : ℝ) ^ θ) := by ring
      have hc : (2 : ℝ) ^ d * (L : ℝ) * (((m + 1 : ℕ) : ℝ) * (M : ℝ)) ≤
          (2 : ℝ) ^ d * (L : ℝ) * ((η / 256) * (T'.card : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hT'_lower (show 0 ≤ η / 256 by positivity)
        linarith
      exact le_of_mul_le_mul_left hc (by positivity)
    -- Step 3 & 4: BPZ Lemma 4.2 + Uniform choice of D
    obtain ⟨fam⟩ := bpz_lemma_4_2_taylor_family hd hE hP hEr hM1 β
      (fun i => (hβ_prop i).1) (fun i => (hβ_prop i).2.1) (fun i => (hβ_prop i).2.2) hβ_mono
    set L_base : ℝ := Real.log ((Nat.factorial N' : ℕ) : ℝ) / (P_deg : ℝ)
    set Q_N : ℝ := ((N / 2 : ℕ) : ℝ) * Real.log ((N / 2 : ℕ) : ℝ) / (P_deg : ℝ)
    have hQ_le_Lbase : Q_N ≤ L_base := by
      apply div_le_div_of_nonneg_right _ hP_rpos.le
      exact le_trans (factorial_log_lower hN4)
        (Real.log_le_log (by exact_mod_cast Nat.factorial_pos N) (by exact_mod_cast Nat.factorial_le hN'_lo))
    have hQN_pos : 0 < Q_N := by
      have hN2_gt1 : (1 : ℝ) < ((N / 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ N / 2 by omega)
      have := Real.log_pos hN2_gt1
      positivity
    have hLbase_pos : 0 < L_base := lt_of_lt_of_le hQN_pos hQ_le_Lbase
    have hKlin_QN : (K_lin / (P_deg : ℝ)) * (N : ℝ) < Q_N := by
      dsimp only [Q_N]; rw [div_mul_eq_mul_div]; exact div_lt_div_of_pos_right hKlin hP_rpos
    set D : ℕ := Nat.ceil ((E : ℝ) * (1 + η) * L_base / ((B_den - η) * Real.log (N : ℝ))) + 10 * m + 1
    set O : ℕ := Nat.floor (((m : ℝ) + 1 - ε₀) * (D : ℝ))
    have hD_ge : 10 * m ≤ D := by omega
    have hD1 : 1 ≤ D := by omega
    have hO_gt : D < O := by
      have hD_r : (10 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (show 10 ≤ D by omega)
      have h1 : (D : ℝ) + 1 < ((m : ℝ) + 1 - ε₀) * (D : ℝ) := by nlinarith
      have h2 := Nat.lt_floor_add_one (((m : ℝ) + 1 - ε₀) * (D : ℝ))
      exact_mod_cast (show (D : ℝ) < (O : ℝ) by linarith)
    have hO_lt : O - D < m * (D + 1) := by
      have hO_le : (O : ℝ) ≤ ((m : ℝ) + 1 - ε₀) * (D : ℝ) := Nat.floor_le (by
        have : 0 < (m : ℝ) + 1 - ε₀ := by linarith; positivity)
      have h1 : (O : ℝ) < (D : ℝ) + (m : ℝ) * ((D : ℝ) + 1) := by nlinarith
      have h2 : O < D + m * (D + 1) := by exact_mod_cast h1
      omega
    -- Step 5 & 6: `lem_7_1_initial_pade_polynomials` + support extraction + `siegel_ode_wronskian_on_support`
    obtain ⟨P_coeff, hP_nz, hP_bd, hP_van⟩ :=
      lem_7_1_initial_pade_polynomials fam hP hM1 hm1 hD1 hO_gt hO_lt
    let S : Finset (Fin (m + 1)) :=
      insert 0 ((Finset.univ.filter (fun i : Fin m => ∃ j : Fin (D + 1), P_coeff i j ≠ 0)).image Fin.succ)
    have hS_eq : ∀ i : Fin m, i.succ ∈ S ↔ ∃ j : Fin (D + 1), P_coeff i j ≠ 0 := by
      intro i
      simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (h0 | ⟨i', hi', heq⟩)
        · exact absurd h0 (Fin.succ_ne_zero i)
        · exact (Fin.succ_injective _ heq) ▸ hi'
      · intro hi; exact Or.inr ⟨i, hi, rfl⟩
    have hS_ge1 : 1 ≤ S.card := Finset.one_le_card.mpr ⟨0, Finset.mem_insert_self 0 _⟩
    have hS_le : S.card ≤ m + 1 := by
      calc S.card ≤ (Finset.univ : Finset (Fin (m + 1))).card := Finset.card_le_univ S
        _ = m + 1 := Fintype.card_fin (m + 1)
    obtain ⟨W⟩ := siegel_ode_wronskian_on_support fam P_coeff S hP hM1 hm1 hD1 hO_gt
      hP_nz hP_bd hP_van hS_eq
    -- Step 7: `lem_7_3_support_reduced_wronskian` on T' and minimal-multiplicity n₀ ∈ T'
    have hT'_gtM : ∀ n ∈ T', M < n := fun n hn => by have := (hT'_int n hn).1; omega
    obtain ⟨_, hsum_mult, _⟩ := lem_7_3_support_reduced_wronskian W T' hT'_gtM
    obtain ⟨n₀, hn₀_mem, hn₀_min⟩ := Finset.exists_min_image T' W.multAt (Finset.card_pos.mp hT'_pos)
    set a : ℕ := W.multAt n₀
    have ha_mul : T'.card * a ≤ S.card * D + Nat.choose S.card 2 * M := by
      have h1 : T'.card * a ≤ ∑ n ∈ T', W.multAt n := by
        calc T'.card * a = ∑ _n ∈ T', a := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ n ∈ T', W.multAt n := Finset.sum_le_sum (fun n hn => hn₀_min n hn)
      exact le_trans h1 (le_trans hsum_mult (Nat.sub_le _ _))
    -- Key bound: (m + 1) * M ≤ (η / 256) * D and ((a + S.card) * M + a + S.card) ≤ (η / 32) * D
    have hD_lo_main : (E : ℝ) * (1 + η) * L_base ≤ (D : ℝ) * ((B_den - η) * Real.log (N : ℝ)) := by
      have h1 : (E : ℝ) * (1 + η) * L_base / ((B_den - η) * Real.log (N : ℝ)) ≤ (D : ℝ) := by
        have := Nat.le_ceil ((E : ℝ) * (1 + η) * L_base / ((B_den - η) * Real.log (N : ℝ)))
        have hD_cast : (Nat.ceil ((E : ℝ) * (1 + η) * L_base / ((B_den - η) * Real.log (N : ℝ))) : ℝ) ≤ (D : ℝ) := by
          exact_mod_cast (show Nat.ceil _ ≤ D by omega)
        linarith
      exact (div_le_iff₀ (by positivity)).mp h1
    have hQN_le_Dlog : Q_N / (B_den + 1) ≤ (D : ℝ) * Real.log (N : ℝ) := by
      have hE1 : (1 : ℝ) ≤ (E : ℝ) := by exact_mod_cast hE
      have h1 : Q_N ≤ (D : ℝ) * Real.log (N : ℝ) * (B_den - η) := by nlinarith
      have h2 : Q_N / (B_den - η) ≤ (D : ℝ) * Real.log (N : ℝ) := (div_le_iff₀ hBη_pos).mpr h1
      exact le_trans (div_le_div_of_nonneg_left hQN_pos.le hBη_pos (by linarith)) h2
    have hM_le_D : ((m + 1 : ℕ) : ℝ) * (M : ℝ) ≤ (η / 256) * (D : ℝ) := by
      have hN2_ge : (N : ℝ) / 4 ≤ ((N / 2 : ℕ) : ℝ) := by
        have : N ≤ 4 * (N / 2) := by omega
        have h1 : (N : ℝ) ≤ 4 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast this; linarith
      have hlog_comp : Real.log (N : ℝ) ≤ 2 * Real.log ((N / 2 : ℕ) : ℝ) := by
        have h1 := Real.log_le_log hN_pos (by linarith : (N : ℝ) ≤ 4 * ((N / 2 : ℕ) : ℝ))
        rw [Real.log_mul (by norm_num) (by linarith : ((N / 2 : ℕ) : ℝ) ≠ 0)] at h1
        linarith [log_four_lt_two]
      have hQN_ge_Nlog : (N : ℝ) * Real.log (N : ℝ) / (8 * (P_deg : ℝ)) ≤ Q_N := by
        dsimp only [Q_N]
        rw [div_le_div_iff₀ (by positivity) hP_rpos]; nlinarith
      have h1 : (2048 * ((m + 1 : ℕ) : ℝ) * (P_deg : ℝ) * (B_den - η) / (η * (E : ℝ))) * Real.log (N : ℝ) <
          (N : ℝ) ^ (1 - θ) := by nlinarith
      have h2 : ((m + 1 : ℕ) : ℝ) * (M : ℝ) * ((B_den - η) * Real.log (N : ℝ)) ≤
          (η / 256) * (E : ℝ) * ((N : ℝ) / (8 * (P_deg : ℝ))) := by
        have hmul : (N : ℝ) ^ θ * (N : ℝ) ^ (1 - θ) = (N : ℝ) := by rw [← Real.rpow_add hN_pos]; simp
        have h3 := mul_lt_mul_of_pos_left h1 (show 0 < η * (E : ℝ) / (2048 * (P_deg : ℝ)) by positivity)
        have hsimp : η * (E : ℝ) / (2048 * (P_deg : ℝ)) *
            ((2048 * ((m + 1 : ℕ) : ℝ) * (P_deg : ℝ) * (B_den - η) / (η * (E : ℝ))) * Real.log (N : ℝ)) =
            ((m + 1 : ℕ) : ℝ) * ((B_den - η) * Real.log (N : ℝ)) := by
          field_simp [hη_pos.ne', hE_pos.ne', hP_rpos.ne']
        rw [hsimp] at h3
        have h4 := mul_le_mul_of_nonneg_left h3.le (show (0 : ℝ) ≤ (M : ℝ) by positivity)
        have h5 : (M : ℝ) * (N : ℝ) ^ (1 - θ) ≤ (N : ℝ) := by nlinarith [Real.rpow_pos_of_pos hN_pos (1 - θ)]
        have h6 : (M : ℝ) * (η * (E : ℝ) / (2048 * (P_deg : ℝ)) * (N : ℝ) ^ (1 - θ)) ≤
            (η / 256) * (E : ℝ) * ((N : ℝ) / (8 * (P_deg : ℝ))) := by
          have : (M : ℝ) * (η * (E : ℝ) / (2048 * (P_deg : ℝ)) * (N : ℝ) ^ (1 - θ)) =
              (η / 256) * (E : ℝ) * (((M : ℝ) * (N : ℝ) ^ (1 - θ)) / (8 * (P_deg : ℝ))) := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h5 (by positivity)) (by positivity)
        linarith
      have h3 : ((m + 1 : ℕ) : ℝ) * (M : ℝ) * ((B_den - η) * Real.log (N : ℝ)) ≤
          (η / 256) * ((D : ℝ) * ((B_den - η) * Real.log (N : ℝ))) := by
        have hQ_N : (N : ℝ) / (8 * (P_deg : ℝ)) ≤ Q_N := by
          have : (1 : ℝ) ≤ Real.log (N : ℝ) := by linarith
          have : (N : ℝ) / (8 * (P_deg : ℝ)) ≤ (N : ℝ) * Real.log (N : ℝ) / (8 * (P_deg : ℝ)) := by
            apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
          exact le_trans this hQN_ge_Nlog
        nlinarith [hD_lo_main, hQ_le_Lbase]
      exact le_of_mul_le_mul_right (by linarith : ((m + 1 : ℕ) : ℝ) * (M : ℝ) * ((B_den - η) * Real.log (N : ℝ)) ≤
        ((η / 256) * (D : ℝ)) * ((B_den - η) * Real.log (N : ℝ))) (by positivity)
    have haM_small : (((a + S.card) * M + a + S.card : ℕ) : ℝ) ≤ (η / 32) * (D : ℝ) := by
      have hch_le : Nat.choose S.card 2 ≤ (m + 1) * (m + 1) := by
        rw [Nat.choose_two_right]
        exact le_trans (Nat.div_le_self _ 2) (Nat.mul_le_mul hS_le hS_le)
      have ha_r : (a : ℝ) ≤ (((m + 1 : ℕ) : ℝ) * (D : ℝ) + ((m + 1 : ℕ) : ℝ) ^ 2 * (M : ℝ)) / (T'.card : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast (show 0 < T'.card by omega))]
        have h1 : ((T'.card * a : ℕ) : ℝ) ≤ ((S.card * D + Nat.choose S.card 2 * M : ℕ) : ℝ) := by
          exact_mod_cast ha_mul
        push_cast at h1
        have hS_r : (S.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hS_le
        have hch_r : (Nat.choose S.card 2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by rw [sq]; exact_mod_cast hch_le
        nlinarith
      have hS_r : (S.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hS_le
      have haM_1 : (a : ℝ) * (M : ℝ) ≤ (η / 128) * (D : ℝ) := by
        calc (a : ℝ) * (M : ℝ)
            ≤ ((((m + 1 : ℕ) : ℝ) * (D : ℝ) + ((m + 1 : ℕ) : ℝ) ^ 2 * (M : ℝ)) / (T'.card : ℝ)) * (M : ℝ) :=
              mul_le_mul_of_nonneg_right ha_r (by positivity)
          _ = (((m + 1 : ℕ) : ℝ) * (M : ℝ) / (T'.card : ℝ)) * (D : ℝ) +
              (((m + 1 : ℕ) : ℝ) * (M : ℝ) / (T'.card : ℝ)) * (((m + 1 : ℕ) : ℝ) * (M : ℝ)) := by ring
          _ ≤ (η / 256) * (D : ℝ) + (η / 256) * (((m + 1 : ℕ) : ℝ) * (M : ℝ)) := by
              have h1 := mul_le_mul_of_nonneg_right hT'_M_small (show (0 : ℝ) ≤ (D : ℝ) by positivity)
              have h2 := mul_le_mul_of_nonneg_right hT'_M_small (show (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (M : ℝ) by positivity)
              linarith
          _ ≤ (η / 128) * (D : ℝ) := by nlinarith [hM_le_D, hη_le_16]
      have hSM_1 : (S.card : ℝ) * (M : ℝ) ≤ (η / 256) * (D : ℝ) := by nlinarith
      have hM_ge1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
      push_cast; nlinarith
    -- Step 8: Call `bpz_cauchy_leibniz_pade_eval` at n₀ ∈ T'
    have hn₀_T : n₀ ∈ T := hT'_sub hn₀_mem
    have hn₀_S : n₀ ∈ S_sol := hT_sub hn₀_T
    have hn₀_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn₀_S).1
    have hn₀_sol : IsPolyFactSol s_mult P n₀ := (Finset.mem_filter.mp hn₀_S).2
    have hn₀_clust : ∀ i : Fin d, IsPolyFactSol s_mult P (n₀ - β i) :=
      fun i => (Finset.mem_filter.mp (hT_sol n₀ hn₀_T i).2).2
    obtain ⟨x₀, E_dat, hx₀_gt1, hx₀_log, hCP_le, hU_le, hW_ge, hu_le, hw_le⟩ :=
      h_bpz_eval N M D β S _ W n₀ hM1 h8M hD_ge hβ_prop hβ_mono hn₀_Icc.1 hn₀_Icc.2 hn₀_sol hn₀_clust
    have hx₀_pos : 0 < x₀ := by linarith
    -- Helper: any c_part * N ≤ (η / (32 * (B_den + 1))) * Q_N from hKlin_QN
    have hlogC_nn : 0 ≤ Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m + 1 by omega)
      nlinarith
    have hlogD_const_nn : 0 ≤ Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m + 1 by omega)
      have : (1 : ℝ) ≤ 16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ) := by
        push_cast; linarith [show (0 : ℝ) < 16 * (E : ℝ) / (B_den - η) by positivity]
      nlinarith
    have hKlin_simp : (32 * (B_den + 1) / η) *
        (((m : ℝ) / ε₀) * Real.log 10 + (E : ℝ) + Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) +
          (10 * (m : ℝ) + 2) + C_0 + 10 +
          Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1) * (N : ℝ) < Q_N := by
      have h1 : K_lin / (P_deg : ℝ) = (32 * (B_den + 1) / η) *
          (((m : ℝ) / ε₀) * Real.log 10 + (E : ℝ) + Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) +
            (10 * (m : ℝ) + 2) + C_0 + 10 +
            Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1) := by
        dsimp only [K_lin]; field_simp [hP_rpos.ne']
      rwa [← h1]
    have hKlin_scaled : (((m : ℝ) / ε₀) * Real.log 10 + (E : ℝ) + Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) +
        (10 * (m : ℝ) + 2) + C_0 + 10 +
        Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1) * (N : ℝ) ≤
        (η / (32 * (B_den + 1))) * Q_N := by
      have hmul := mul_lt_mul_of_pos_left hKlin_simp (show 0 < η / (32 * (B_den + 1)) by positivity)
      have hsimp : η / (32 * (B_den + 1)) * ((32 * (B_den + 1) / η) *
          (((m : ℝ) / ε₀) * Real.log 10 + (E : ℝ) + Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) +
            (10 * (m : ℝ) + 2) + C_0 + 10 +
            Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1) * (N : ℝ)) =
          (((m : ℝ) / ε₀) * Real.log 10 + (E : ℝ) + Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) +
            (10 * (m : ℝ) + 2) + C_0 + 10 +
            Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1) * (N : ℝ) := by
        field_simp [hη_pos.ne', (by linarith : B_den + 1 ≠ 0)]
      rw [hsimp] at hmul; linarith
    have hKlin_Dlog : (((m : ℝ) / ε₀) * Real.log 10 + (E : ℝ) + Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) +
        (10 * (m : ℝ) + 2) + C_0 + 10 +
        Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1) * (N : ℝ) ≤
        (η / 32) * (D : ℝ) * Real.log (N : ℝ) := by
      have h1 : (η / (32 * (B_den + 1))) * Q_N = (η / 32) * (Q_N / (B_den + 1)) := by ring
      have h2 := mul_le_mul_of_nonneg_left hQN_le_Dlog (show 0 ≤ η / 32 by positivity)
      linarith
    have hlog10_pos : 0 < Real.log 10 := Real.log_pos (by norm_num)
    have hB1_ge1 : (1 : ℝ) ≤ B_den + 1 := by linarith
    -- Step 9: Pin log x₀ to [(1 - η) * L_base, (1 + η) * L_base]
    have hx₀_lo : (1 - η) * L_base ≤ Real.log x₀ := by
      have h1 := (abs_le.mp hx₀_log).1
      have hfac_le : Real.log ((Nat.factorial N' : ℕ) : ℝ) ≤ Real.log ((Nat.factorial n₀ : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast Nat.factorial_pos N') (by exact_mod_cast Nat.factorial_le (hT'_int n₀ hn₀_mem).1)
      have h2 : L_base ≤ Real.log ((Nat.factorial n₀ : ℕ) : ℝ) / (P_deg : ℝ) :=
        div_le_div_of_nonneg_right hfac_le hP_rpos.le
      have hC0_le : C_0 ≤ η * L_base := by
        have hC0_N : C_0 ≤ C_0 * (N : ℝ) := by nlinarith [show (1 : ℝ) ≤ (N : ℝ) by linarith]
        have h1 : C_0 * (N : ℝ) ≤ (η / (32 * (B_den + 1))) * Q_N := by
          have : 0 ≤ (((m : ℝ) / ε₀) * Real.log 10 + (E : ℝ) + Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) +
              (10 * (m : ℝ) + 2) + 10 +
              Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1) := by positivity
          nlinarith
        have h2 : (η / (32 * (B_den + 1))) * Q_N ≤ η * L_base := by
          have : η / (32 * (B_den + 1)) ≤ η := by rw [div_le_iff₀ (by positivity)]; nlinarith
          nlinarith
        linarith
      linarith
    have hx₀_hi : Real.log x₀ ≤ (1 + η) * L_base := by
      have h1 := (abs_le.mp hx₀_log).2
      have hfac_hi := factorial_log_diff_upper (by omega : 1 ≤ N') (hT'_int n₀ hn₀_mem).1 (hT'_int n₀ hn₀_mem).2
      have harg_le : ((N' + (N / L + 1) : ℕ) : ℝ) ≤ 4 * (N : ℝ) := by
        push_cast; have : N / L ≤ N := Nat.div_le_self N L; have : (N / L : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
        have : (N' : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hN'_hi
        have : (1 : ℝ) ≤ (N : ℝ) := by linarith
        linarith
      have hlog_arg : Real.log ((N' + (N / L + 1) : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
        have h2 := Real.log_le_log (by positivity) harg_le
        rw [Real.log_mul (by norm_num) hN_pos.ne'] at h2
        linarith [log_four_lt_two]
      have hstep_le : ((N / L + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) / Real.log (N : ℝ) := by
        push_cast
        have hdiv : ((N / L : ℕ) : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) :=
          le_trans Nat.cast_div_le (div_le_div_of_nonneg_left hN_pos.le (by linarith) hL_ge_log)
        have h1_le : (1 : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) := (le_div_iff₀ (by linarith)).mpr (by linarith)
        linarith
      have hprod_le : ((N / L + 1 : ℕ) : ℝ) * Real.log ((N' + (N / L + 1) : ℕ) : ℝ) ≤ 4 * (N : ℝ) := by
        calc ((N / L + 1 : ℕ) : ℝ) * Real.log ((N' + (N / L + 1) : ℕ) : ℝ)
            ≤ (2 * (N : ℝ) / Real.log (N : ℝ)) * (2 * Real.log (N : ℝ)) :=
              mul_le_mul hstep_le hlog_arg (Real.log_nonneg (by norm_cast; omega)) (by positivity)
          _ = 4 * (N : ℝ) := by field_simp [(by linarith : Real.log (N : ℝ) ≠ 0)]; ring
      have hdiff_le : Real.log ((Nat.factorial n₀ : ℕ) : ℝ) / (P_deg : ℝ) ≤ L_base + 4 * (N : ℝ) := by
        have hP1 : (1 : ℝ) ≤ (P_deg : ℝ) := by exact_mod_cast (show 1 ≤ P_deg by omega)
        have h2 := div_le_div_of_nonneg_right (le_trans hfac_hi (add_le_add_left hprod_le _)) hP_rpos.le
        rw [add_div] at h2
        have h3 : 4 * (N : ℝ) / (P_deg : ℝ) ≤ 4 * (N : ℝ) := div_le_self (by positivity) hP1
        linarith
      have herr_le : 4 * (N : ℝ) + C_0 ≤ η * L_base := by
        have hC0_N : C_0 ≤ C_0 * (N : ℝ) := by nlinarith [show (1 : ℝ) ≤ (N : ℝ) by linarith]
        have h1 : (4 + C_0) * (N : ℝ) ≤ (η / (32 * (B_den + 1))) * Q_N := by
          have : 0 ≤ (((m : ℝ) / ε₀) * Real.log 10 + (E : ℝ) + Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) +
              (10 * (m : ℝ) + 2) + 6 +
              Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1) := by positivity
          nlinarith
        have h2 : (η / (32 * (B_den + 1))) * Q_N ≤ η * L_base := by
          have : η / (32 * (B_den + 1)) ≤ η := by rw [div_le_iff₀ (by positivity)]; nlinarith
          nlinarith
        linarith
      linarith
    -- Step 10: Bound log Z, log U, log W, log(2w), log(2*s*C_P*M^E*u)
    have hconst1 : α₂ * Real.log C_2 + Real.log 2 + (η / 16) * Real.log (C_3 * (N : ℝ)) ≤
        (η / 4) * Real.log (N : ℝ) := by
      rw [Real.log_mul (by linarith) hN_pos.ne']
      have h6a : (α₂ * Real.log C_2 + Real.log 2 + (η / 16) * Real.log C_3 + 1) * (8 / η) ≤
          Real.log (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlogN_big
      have hmul := mul_le_mul_of_nonneg_right h6a (show 0 ≤ η / 8 by positivity)
      have hsimp : (α₂ * Real.log C_2 + Real.log 2 + (η / 16) * Real.log C_3 + 1) * (8 / η) * (η / 8) =
          α₂ * Real.log C_2 + Real.log 2 + (η / 16) * Real.log C_3 + 1 := by field_simp [hη_pos.ne']
      rw [hsimp] at hmul; linarith
    have hconst2 : α₁ * Real.log C_1 + Real.log 2 + Real.log (P_deg : ℝ) ≤ (η / 8) * Real.log (N : ℝ) := by
      have h6b : (α₁ * Real.log C_1 + Real.log 2 + Real.log (P_deg : ℝ) + 1) * (8 / η) ≤
          Real.log (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlogN_big
      have hmul := mul_le_mul_of_nonneg_right h6b (show 0 ≤ η / 8 by positivity)
      have hsimp : (α₁ * Real.log C_1 + Real.log 2 + Real.log (P_deg : ℝ) + 1) * (8 / η) * (η / 8) =
          α₁ * Real.log C_1 + Real.log 2 + Real.log (P_deg : ℝ) + 1 := by field_simp [hη_pos.ne']
      rw [hsimp] at hmul; linarith
    have hlogC3_le : Real.log (C_3 * (N : ℝ)) ≤ 4 * Real.log (N : ℝ) := by
      have h3 : (η / 16) * Real.log (C_3 * (N : ℝ)) ≤ (η / 4) * Real.log (N : ℝ) := by
        have : 0 ≤ α₂ * Real.log C_2 := mul_nonneg hα₂_pos.le (Real.log_nonneg hC2)
        have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num); linarith
      have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 16 / η by positivity)
      have hsimp1 : 16 / η * ((η / 16) * Real.log (C_3 * (N : ℝ))) = Real.log (C_3 * (N : ℝ)) := by field_simp [hη_pos.ne']
      have hsimp2 : 16 / η * ((η / 4) * Real.log (N : ℝ)) = 4 * Real.log (N : ℝ) := by field_simp [hη_pos.ne']; ring
      rw [hsimp1, hsimp2] at h4; exact h4
    have hZ_pos_nat : 0 < P_deg ^ (a + S.card) * n₀ ^ (D + (a + S.card) * M) :=
      Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _)
    have hZ_pos : (0 : ℝ) < (E_dat.Z : ℝ) := by rw [E_dat.Z_eq]; exact_mod_cast hZ_pos_nat
    have hlogZ_clean : Real.log (E_dat.Z : ℝ) ≤ (1 + η / 4) * (D : ℝ) * Real.log (N : ℝ) := by
      have hZ_le : (E_dat.Z : ℝ) ≤ (P_deg : ℝ) ^ (a + S.card) * (2 * (N : ℝ)) ^ (D + (a + S.card) * M) := by
        rw [E_dat.Z_eq]; push_cast
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hn₀_Icc.2) _) (by positivity)
      have h1 := Real.log_le_log hZ_pos hZ_le
      rw [Real.log_mul (pow_ne_zero _ hP_rpos.ne') (pow_ne_zero _ (by positivity)),
        Real.log_pow, Real.log_pow, Real.log_mul (by norm_num) hN_pos.ne'] at h1
      have hlogP : Real.log (P_deg : ℝ) ≤ (η / 8) * Real.log (N : ℝ) := by
        have : 0 ≤ α₁ * Real.log C_1 := mul_nonneg hα₁_pos.le (Real.log_nonneg hC1)
        have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num); linarith
      have hlog2 : Real.log 2 ≤ (η / 8) * Real.log (N : ℝ) := by
        have : 0 ≤ α₁ * Real.log C_1 := mul_nonneg hα₁_pos.le (Real.log_nonneg hC1)
        have : 0 ≤ Real.log (P_deg : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ P_deg by omega)); linarith
      have ha_le_D : ((a + S.card : ℕ) : ℝ) ≤ (η / 32) * (D : ℝ) := by
        have : ((a + S.card : ℕ) : ℝ) ≤ (((a + S.card) * M + a + S.card : ℕ) : ℝ) := by
          exact_mod_cast (show a + S.card ≤ (a + S.card) * M + a + S.card by omega)
        linarith
      have haM_le_D : (((a + S.card) * M : ℕ) : ℝ) ≤ (η / 32) * (D : ℝ) := by
        have : (((a + S.card) * M : ℕ) : ℝ) ≤ (((a + S.card) * M + a + S.card : ℕ) : ℝ) := by
          exact_mod_cast (show (a + S.card) * M ≤ (a + S.card) * M + a + S.card by omega)
        linarith
      push_cast at h1 ha_le_D haM_le_D
      nlinarith [hη_le_16, hlogN_ge4]
    have hlogU_le : Real.log E_dat.U ≤ (α₁ * θ + η / 4) * Real.log (N : ℝ) := by
      have h1 := Real.log_le_log E_dat.U_pos hU_le
      rw [Real.log_rpow (by positivity), Real.log_mul (by linarith) (by positivity)] at h1
      have hlogM : Real.log (M : ℝ) ≤ θ * Real.log (N : ℝ) := by
        have := Real.log_le_log (by positivity) hM_le_rpow; rwa [Real.log_rpow hN_pos] at this
      have hlogC1 : α₁ * Real.log C_1 ≤ (η / 8) * Real.log (N : ℝ) := by
        have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have : 0 ≤ Real.log (P_deg : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ P_deg by omega)); linarith
      nlinarith
    have hlogW_ge : (B_den + 1 - η / 4) * Real.log (N : ℝ) ≤ Real.log E_dat.W := by
      have h1 := Real.log_le_log (by positivity) hW_ge
      rw [Real.log_mul (Real.rpow_pos_of_pos hN_pos _).ne' (Real.rpow_pos_of_pos (by positivity) _).ne',
        Real.log_rpow hN_pos, Real.log_rpow (by positivity),
        Real.log_mul (by linarith) (by positivity)] at h1
      have hlogM : Real.log (M : ℝ) ≤ θ * Real.log (N : ℝ) := by
        have := Real.log_le_log (by positivity) hM_le_rpow; rwa [Real.log_rpow hN_pos] at this
      have hlogC2 : α₂ * Real.log C_2 ≤ (η / 4) * Real.log (N : ℝ) := by
        have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have : 0 ≤ (η / 16) * Real.log (C_3 * (N : ℝ)) := mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith))
        linarith
      dsimp only [B_den, α₂] at h1 ⊢; nlinarith
    have hlog2w_le : Real.log (2 * E_dat.w) ≤ (η / 2) * (D : ℝ) * Real.log (N : ℝ) := by
      have h1 := Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hw_le (by norm_num : (0 : ℝ) ≤ 2))
      have hlog_expand : Real.log (2 * (((m + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) *
          (C_3 * (N : ℝ)) ^ (2 * ((a + S.card) * M + a + S.card)) *
          (4 : ℝ) ^ (((m : ℝ) / ε₀) * (M : ℝ)))) =
          Real.log 2 + Real.log (((m + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ)) +
          ((2 * ((a + S.card) * M + a + S.card) : ℕ) : ℝ) * Real.log (C_3 * (N : ℝ)) +
          (((m : ℝ) / ε₀) * (M : ℝ)) * Real.log 4 := by
        rw [show 2 * (((m + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) *
            (C_3 * (N : ℝ)) ^ (2 * ((a + S.card) * M + a + S.card)) *
            (4 : ℝ) ^ (((m : ℝ) / ε₀) * (M : ℝ))) =
            (2 * (((m + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ))) *
            ((C_3 * (N : ℝ)) ^ (2 * ((a + S.card) * M + a + S.card)) *
            (4 : ℝ) ^ (((m : ℝ) / ε₀) * (M : ℝ))) by ring]
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) (by positivity),
          Real.log_mul (pow_ne_zero _ (by positivity)) (Real.rpow_pos_of_pos (by norm_num) _).ne',
          Real.log_pow, Real.log_rpow (by norm_num)]
        push_cast; ring
      rw [hlog_expand] at h1
      have hD_up : ((m + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) ≤
          (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) * (N : ℝ) := by
        have hfac : Nat.factorial N' ≤ (2 * N) ^ (2 * N) :=
          le_trans (Nat.factorial_le hN'_hi) (Nat.factorial_le_pow (2 * N))
        have hLbase_up : L_base ≤ 4 * (N : ℝ) * Real.log (N : ℝ) := by
          have hlogf := Real.log_le_log (by exact_mod_cast Nat.factorial_pos N')
            (by exact_mod_cast hfac : ((Nat.factorial N' : ℕ) : ℝ) ≤ (((2 * N) ^ (2 * N) : ℕ) : ℝ))
          rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hN_pos.ne'] at hlogf
          have hP1 : (1 : ℝ) ≤ (P_deg : ℝ) := by exact_mod_cast (show 1 ≤ P_deg by omega)
          have h2 : L_base ≤ Real.log ((Nat.factorial N' : ℕ) : ℝ) := div_le_self (by positivity) hP1
          have := log_two_lt_one
          nlinarith
        have hceil := Nat.ceil_lt_add_one (show 0 ≤ (E : ℝ) * (1 + η) * L_base / ((B_den - η) * Real.log (N : ℝ)) by positivity)
        have hfrac : (E : ℝ) * (1 + η) * L_base / ((B_den - η) * Real.log (N : ℝ)) ≤
            (8 * (E : ℝ) / (B_den - η)) * (N : ℝ) := by
          rw [div_le_iff₀ (by positivity)]
          have : (8 * (E : ℝ) / (B_den - η)) * (N : ℝ) * ((B_den - η) * Real.log (N : ℝ)) =
              8 * (E : ℝ) * (N : ℝ) * Real.log (N : ℝ) := by field_simp [hBη_pos.ne']
          rw [this]; nlinarith [hη_le_16]
        have hD_cast : ((D + 1 : ℕ) : ℝ) = (Nat.ceil ((E : ℝ) * (1 + η) * L_base / ((B_den - η) * Real.log (N : ℝ))) : ℝ) +
            ((10 * m + 2 : ℕ) : ℝ) := by dsimp [D]; push_cast; ring
        have hD_le : ((D + 1 : ℕ) : ℝ) ≤ (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ)) * (N : ℝ) := by
          push_cast at hD_cast ⊢; nlinarith [show (1 : ℝ) ≤ (N : ℝ) by linarith]
        have hmul := mul_le_mul_of_nonneg_left hD_le (show (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) by positivity)
        linarith
      have hterm_D1 : Real.log (((m + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ)) ≤ (η / 32) * (D : ℝ) * Real.log (N : ℝ) := by
        have h2 := Real.log_le_log (by positivity) hD_up
        rw [Real.log_mul (by positivity) hN_pos.ne'] at h2
        have h3 : Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + Real.log (N : ℝ) ≤
            (Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1) * (N : ℝ) := by
          nlinarith [show (1 : ℝ) ≤ (N : ℝ) by linarith]
        have h4 : (Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1) * (N : ℝ) ≤
            (η / 32) * (D : ℝ) * Real.log (N : ℝ) := by
          have : 0 ≤ (((m : ℝ) / ε₀) * Real.log 10 + (E : ℝ) + Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) +
              (10 * (m : ℝ) + 2) + C_0 + 10) := by positivity
          nlinarith [hKlin_Dlog]
        linarith
      have hterm_M4 : (((m : ℝ) / ε₀) * (M : ℝ)) * Real.log 4 ≤ (η / 32) * (D : ℝ) * Real.log (N : ℝ) := by
        have hlog_4_le_10 : Real.log 4 ≤ Real.log 10 := Real.log_le_log (by norm_num) (by norm_num)
        have hMN : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show M ≤ N by omega)
        have h2 : (((m : ℝ) / ε₀) * (M : ℝ)) * Real.log 4 ≤ (((m : ℝ) / ε₀) * Real.log 10) * (N : ℝ) := by
          have : 0 ≤ ((m : ℝ) / ε₀) := by positivity
          nlinarith
        have h3 : (((m : ℝ) / ε₀) * Real.log 10) * (N : ℝ) ≤ (η / 32) * (D : ℝ) * Real.log (N : ℝ) := by
          have : 0 ≤ ((E : ℝ) + Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) + (10 * (m : ℝ) + 2) + C_0 + 10 +
              Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1) := by positivity
          nlinarith [hKlin_Dlog]
        linarith
      have hterm_log2 : Real.log 2 ≤ (η / 8) * (D : ℝ) * Real.log (N : ℝ) := by
        have hlog2 : Real.log 2 ≤ (η / 8) * Real.log (N : ℝ) := by
          have : 0 ≤ α₁ * Real.log C_1 := mul_nonneg hα₁_pos.le (Real.log_nonneg hC1)
          have : 0 ≤ Real.log (P_deg : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ P_deg by omega)); linarith
        nlinarith [show (1 : ℝ) ≤ (D : ℝ) by exact_mod_cast hD1]
      have hterm_C3 : ((2 * ((a + S.card) * M + a + S.card) : ℕ) : ℝ) * Real.log (C_3 * (N : ℝ)) ≤
          (η / 4) * (D : ℝ) * Real.log (N : ℝ) := by
        have hlogC3_nn : 0 ≤ Real.log (C_3 * (N : ℝ)) := Real.log_nonneg (by nlinarith)
        have h2a : ((2 * ((a + S.card) * M + a + S.card) : ℕ) : ℝ) ≤ (η / 16) * (D : ℝ) := by
          push_cast at haM_small ⊢; linarith
        nlinarith
      linarith
    -- Step 11: Verify `hD_choice` and invoke `lem_7_4_denominator_clearing`!
    have hD_choice : x₀ ^ E * E_dat.w * E_dat.W ^ (-(D : ℝ)) ≤ (1 : ℝ) / (2 * (E_dat.Z : ℝ)) := by
      rw [← Real.log_le_log_iff (by positivity) (by positivity)]
      rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos E_dat.W_pos _).ne',
        Real.log_mul (pow_pos hx₀_pos E).ne' E_dat.w_pos.ne',
        Real.log_pow, Real.log_rpow E_dat.W_pos,
        Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub,
        Real.log_mul (by norm_num) hZ_pos.ne']
      have hlog2w_split : Real.log 2 + Real.log E_dat.w = Real.log (2 * E_dat.w) :=
        (Real.log_mul (by norm_num) E_dat.w_pos.ne').symm
      nlinarith [hx₀_hi, hD_lo_main, hlogW_ge, hlogZ_clean, hlog2w_le]
    have h74 := (lem_7_4_denominator_clearing hx₀_pos hS_ge1 hZ_pos_nat E_dat hD_choice).2
    -- Step 12: Take log of h74 and derive strict contradiction with `γ > 0`!
    have hlog74 := Real.log_le_log (by positivity) h74
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub,
      Real.log_mul (by norm_num) hZ_pos.ne'] at hlog74
    have hRHS_pos1 : 0 < (S.card : ℝ) * E_dat.C_P * (M : ℝ) ^ E * E_dat.u * E_dat.U ^ D := by
      have := E_dat.C_P_pos; have := E_dat.u_pos; have := E_dat.U_pos; positivity
    rw [Real.log_mul hRHS_pos1.ne' (Real.rpow_pos_of_pos hx₀_pos _).ne',
      Real.log_rpow hx₀_pos,
      Real.log_mul (by have := E_dat.C_P_pos; have := E_dat.u_pos; positivity) (pow_ne_zero D E_dat.U_pos.ne'),
      Real.log_pow] at hlog74
    have hlog_pre : Real.log 2 + Real.log ((S.card : ℝ) * E_dat.C_P * (M : ℝ) ^ E * E_dat.u) ≤
        (η / 4) * (D : ℝ) * Real.log (N : ℝ) := by
      have h1 : 2 * ((S.card : ℝ) * E_dat.C_P * (M : ℝ) ^ E * E_dat.u) ≤
          (2 * ((m + 1 : ℕ) : ℝ) * C_1) * (N : ℝ) ^ E *
          (C_3 * (N : ℝ)) ^ ((a + S.card) * M + a + S.card) *
          (10 : ℝ) ^ (((m : ℝ) / ε₀) * (M : ℝ)) := by
        have hS_r : (S.card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hS_le
        have hME : (M : ℝ) ^ E ≤ (N : ℝ) ^ E :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show M ≤ N by omega)) E
        have hpart1 : 2 * (S.card : ℝ) * E_dat.C_P * (M : ℝ) ^ E ≤
            (2 * ((m + 1 : ℕ) : ℝ) * C_1) * (N : ℝ) ^ E := by
          have ha : 2 * (S.card : ℝ) * E_dat.C_P ≤ 2 * ((m + 1 : ℕ) : ℝ) * C_1 := by
            have := E_dat.C_P_pos; nlinarith
          exact mul_le_mul ha hME (by positivity) (by positivity)
        have h2 := mul_le_mul hpart1 hu_le E_dat.u_pos.le (by positivity)
        linarith
      have hlog1 := Real.log_le_log (by have := E_dat.C_P_pos; have := E_dat.u_pos; positivity) h1
      rw [Real.log_mul (by norm_num) (by have := E_dat.C_P_pos; have := E_dat.u_pos; positivity)] at hlog1
      rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos (by norm_num) _).ne',
        Real.log_mul (by positivity) (pow_ne_zero _ (by positivity)),
        Real.log_mul (by positivity) (pow_ne_zero _ hN_pos.ne'),
        Real.log_pow, Real.log_pow, Real.log_rpow (by norm_num)] at hlog1
      have hpartA : Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) + (E : ℝ) * Real.log (N : ℝ) +
          ((m : ℝ) / ε₀) * (M : ℝ) * Real.log 10 ≤ (η / 32) * (D : ℝ) * Real.log (N : ℝ) := by
        have hMN : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show M ≤ N by omega)
        have h2 : Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) + (E : ℝ) * Real.log (N : ℝ) +
            ((m : ℝ) / ε₀) * (M : ℝ) * Real.log 10 ≤
            (Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) + (E : ℝ) + ((m : ℝ) / ε₀) * Real.log 10) * (N : ℝ) := by
          have : 0 ≤ ((m : ℝ) / ε₀) * Real.log 10 := by positivity
          nlinarith [show (1 : ℝ) ≤ (N : ℝ) by linarith]
        have h3 : (Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) + (E : ℝ) + ((m : ℝ) / ε₀) * Real.log 10) * (N : ℝ) ≤
            (η / 32) * (D : ℝ) * Real.log (N : ℝ) := by
          have : 0 ≤ ((10 * (m : ℝ) + 2) + C_0 + 10 +
              Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1) := by positivity
          nlinarith [hKlin_Dlog]
        linarith
      have hpartB : (((a + S.card) * M + a + S.card : ℕ) : ℝ) * Real.log (C_3 * (N : ℝ)) ≤
          (η / 8) * (D : ℝ) * Real.log (N : ℝ) := by
        have hlogC3_nn : 0 ≤ Real.log (C_3 * (N : ℝ)) := Real.log_nonneg (by nlinarith)
        nlinarith [haM_small, hlogC3_le]
      linarith
    have hD_up_log : (D : ℝ) * Real.log (N : ℝ) ≤ ((E : ℝ) * (1 + η) / (B_den - η) + η) * L_base := by
      have hceil := Nat.ceil_lt_add_one (show 0 ≤ (E : ℝ) * (1 + η) * L_base / ((B_den - η) * Real.log (N : ℝ)) by positivity)
      have hD_cast : (D : ℝ) = (Nat.ceil ((E : ℝ) * (1 + η) * L_base / ((B_den - η) * Real.log (N : ℝ))) : ℝ) +
          ((10 * m + 1 : ℕ) : ℝ) := by dsimp [D]; push_cast; ring
      have hD_lt : (D : ℝ) ≤ (E : ℝ) * (1 + η) * L_base / ((B_den - η) * Real.log (N : ℝ)) + ((10 * m + 2 : ℕ) : ℝ) := by
        push_cast at hD_cast ⊢; linarith
      have hmul := mul_le_mul_of_nonneg_right hD_lt (show 0 ≤ Real.log (N : ℝ) by linarith)
      rw [add_mul] at hmul
      have hsimp : (E : ℝ) * (1 + η) * L_base / ((B_den - η) * Real.log (N : ℝ)) * Real.log (N : ℝ) =
          (E : ℝ) * (1 + η) / (B_den - η) * L_base := by field_simp [(by linarith : Real.log (N : ℝ) ≠ 0)]
      rw [hsimp] at hmul
      have htail : ((10 * m + 2 : ℕ) : ℝ) * Real.log (N : ℝ) ≤ η * L_base := by
        have h1 : ((10 * m + 2 : ℕ) : ℝ) * Real.log (N : ℝ) ≤ (10 * (m : ℝ) + 2) * (N : ℝ) := by
          push_cast; nlinarith
        have h2 : (10 * (m : ℝ) + 2) * (N : ℝ) ≤ (η / (32 * (B_den + 1))) * Q_N := by
          have : 0 ≤ (((m : ℝ) / ε₀) * Real.log 10 + (E : ℝ) + Real.log (2 * ((m + 1 : ℕ) : ℝ) * C_1) +
              C_0 + 10 + Real.log (((m + 1 : ℕ) : ℝ) * (16 * (E : ℝ) / (B_den - η) + 2 * (10 * m + 3 : ℕ))) + 1) := by positivity
          nlinarith [hKlin_scaled]
        have h3 : (η / (32 * (B_den + 1))) * Q_N ≤ η * L_base := by
          have : η / (32 * (B_den + 1)) ≤ η := by rw [div_le_iff₀ (by positivity)]; nlinarith
          nlinarith
        linarith
      linarith
    have hfinal : ((ν : ℝ) - (E : ℝ)) * (1 - η) * L_base ≤
        (A_num + η) * (((E : ℝ) * (1 + η) / (B_den - η) + η) * L_base) := by
      have h1 : ((ν : ℝ) - (E : ℝ)) * Real.log x₀ ≤
          (Real.log 2 + Real.log ((S.card : ℝ) * E_dat.C_P * (M : ℝ) ^ E * E_dat.u)) +
          Real.log (E_dat.Z : ℝ) + (D : ℝ) * Real.log E_dat.U := by linarith
      have h2 : (Real.log 2 + Real.log ((S.card : ℝ) * E_dat.C_P * (M : ℝ) ^ E * E_dat.u)) +
          Real.log (E_dat.Z : ℝ) + (D : ℝ) * Real.log E_dat.U ≤
          (A_num + η) * ((D : ℝ) * Real.log (N : ℝ)) := by
        dsimp only [A_num]; nlinarith [hlog_pre, hlogZ_clean, hlogU_le]
      have h3 : ((ν : ℝ) - (E : ℝ)) * (1 - η) * L_base ≤ ((ν : ℝ) - (E : ℝ)) * Real.log x₀ := by nlinarith [hx₀_lo]
      exact le_trans h3 (le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left hD_up_log (by positivity))))
    have hcancel : ((ν : ℝ) - (E : ℝ)) * (1 - η) ≤ (A_num + η) * ((E : ℝ) * (1 + η) / (B_den - η) + η) :=
      le_of_mul_le_mul_right hfinal hLbase_pos
    have hmul_B := mul_le_mul_of_nonneg_right hcancel hBη_pos.le
    have hsimp_B : (A_num + η) * ((E : ℝ) * (1 + η) / (B_den - η) + η) * (B_den - η) =
        (A_num + η) * ((E : ℝ) * (1 + η) + η * (B_den - η)) := by field_simp [hBη_pos.ne']
    rw [hsimp_B] at hmul_B
    have hcontra : (A_num + η) * ((E : ℝ) * (1 + η) + η * (B_den - η)) <
        ((ν : ℝ) - (E : ℝ)) * (1 - η) * (B_den - η) := by
      have hγ_bd : η * (16 * ((ν : ℝ) + 1) * (B_den + A_num + 1)) ≤ γ :=
        (le_div_iff₀ (by positivity)).mp hη_le_γ
      have hE_lt_ν : (E : ℝ) < (ν : ℝ) := by exact_mod_cast hEν
      nlinarith [hη_le_16, hη_le_B, hA_pos, hB_pos, hE_pos, hνE_pos]
    linarith

/-- **Theorem 1.3(ii) (Global $O_{P, s, \varepsilon}(N^{6/7 + \varepsilon})$ Bound, eq. 1.10)**:
For any polynomial-factorial equation $s \cdot n! = P(x)$ with $\deg P \ge 2$ and depressed
degree gap $\nu \ge 2$ (and in particular Brocard–Ramanujan $n! + 1 = m^2$), the number of
solutions $n \le N$ is $O_{P, s, \varepsilon}(N^{6/7 + \varepsilon})$ for every $\varepsilon > 0$. -/
theorem thm_1_3_part2_global_6_7 (P_deg : ℕ) (hP : 2 ≤ P_deg)
    (s_mult : ℕ) (hs_mult : 1 ≤ s_mult) (P : ℤ[X])
    (hP_deg : P.natDegree = P_deg) (hP_gap : HasDepressedDegreeGap P 2)
    [DecidablePred (IsPolyFactSol s_mult P)] :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter (IsPolyFactSol s_mult P)).card : ℝ) ≤
        C * (N : ℝ) ^ ((6 / 7 : ℝ) + ε) := by
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
  obtain ⟨C, hC, hdyad⟩ := dyadic_cluster_elimination_proved P_deg 2 5 1 (5 - Real.sqrt 5) ((1 / 7 : ℝ) - δ)
    hP (by norm_num) (by norm_num) (by norm_num) (by omega)
    (by linarith) (by rw [hch5]; push_cast; linarith)
    (by linarith [min_le_right (ε / 2) (1 / 14)])
    (by norm_num; linarith)
    (by simpa [theta_monomial] using hθ_lt)
    s_mult hs_mult P hP_deg hP_gap δ hδ_pos
  have hα_pos : 0 < 1 - ((1 / 7 : ℝ) - δ) + δ := by linarith
  obtain ⟨C', hC', hsum⟩ := dyadic_sum_counting hα_pos hC (IsPolyFactSol s_mult P) hdyad
  refine ⟨C', hC', fun N hN => ?_⟩
  refine le_trans (hsum N hN) ?_
  have hexp : 1 - ((1 / 7 : ℝ) - δ) + δ ≤ (6 / 7 : ℝ) + ε := by
    have := min_le_left (ε / 2) (1 / 14); linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hexp) hC'.le

/-- The Brocard polynomial $P(x) = x^2 - 1 \in \mathbb{Z}[x]$ has degree $2$ and depressed
degree gap $\nu = 2$ (with depressed polynomial $P_{\mathrm{dep}}(y) = y^2 - 4$). -/
lemma brocard_poly_depressed_gap :
    (Polynomial.X ^ 2 - Polynomial.C (1 : ℤ)).natDegree = 2 ∧
    HasDepressedDegreeGap (Polynomial.X ^ 2 - Polynomial.C (1 : ℤ)) 2 := by
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C (1 : ℤ)).natDegree = 2 :=
    Polynomial.natDegree_X_pow_sub_C
  have hmon : (Polynomial.X ^ 2 - Polynomial.C (1 : ℤ)).Monic :=
    Polynomial.monic_X_pow_sub_C 1 (by norm_num)
  have hlead : (Polynomial.X ^ 2 - Polynomial.C (1 : ℤ)).leadingCoeff = 1 := hmon.leadingCoeff
  refine ⟨hdeg, by omega, by omega, by omega, by rw [hlead]; norm_num,
    Polynomial.X ^ 2 - Polynomial.C (4 : ℤ),
    Polynomial.monic_X_pow_sub_C 4 (by norm_num),
    by rw [Polynomial.natDegree_X_pow_sub_C, hdeg], ?_, ?_⟩
  · intro j hj1 hj2
    have hj : j = 1 := by omega
    subst hj
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]
  · intro x
    rw [hdeg, hlead]
    have hc1 : (Polynomial.X ^ 2 - Polynomial.C (1 : ℤ)).coeff 1 = 0 := by
      simp [Polynomial.coeff_X_pow, Polynomial.coeff_one]
    rw [show (2 - 1 : ℕ) = 1 from rfl, hc1]
    simp [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    ring

open Classical in
/-- **Theorem 1.3(ii) (Brocard–Ramanujan Specialization)**:
$\mathcal{N}_{\mathrm{Brocard}}(N) \ll_\varepsilon N^{6/7 + \varepsilon}$. -/
theorem thm_1_3_part2_brocard_6_7 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter (fun n => ∃ m : ℕ, Nat.factorial n + 1 = m ^ 2)).card : ℝ) ≤
        C * (N : ℝ) ^ ((6 / 7 : ℝ) + ε) := by
  intro ε hε
  obtain ⟨hdeg, hgap⟩ := brocard_poly_depressed_gap
  obtain ⟨C, hC, hbd⟩ := thm_1_3_part2_global_6_7 2 (by norm_num) 1 (by norm_num)
    (Polynomial.X ^ 2 - Polynomial.C (1 : ℤ)) hdeg hgap ε hε
  refine ⟨C, hC, fun N hN => ?_⟩
  have heq : (Finset.Icc 1 N).filter (fun n => ∃ m : ℕ, Nat.factorial n + 1 = m ^ 2) =
      (Finset.Icc 1 N).filter (IsPolyFactSol 1 (Polynomial.X ^ 2 - Polynomial.C (1 : ℤ))) := by
    apply Finset.filter_congr
    intro n _
    unfold IsPolyFactSol
    simp only [Nat.cast_one, one_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨(m : ℤ), ?_⟩
      have hmZ : (Nat.factorial n : ℤ) + 1 = (m : ℤ) ^ 2 := by exact_mod_cast hm
      linarith
    · rintro ⟨x, hx⟩
      refine ⟨x.natAbs, ?_⟩
      have hsq : (x.natAbs : ℤ) ^ 2 = x ^ 2 := Int.natAbs_sq x
      have hmZ : ((Nat.factorial n + 1 : ℕ) : ℤ) = ((x.natAbs ^ 2 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, hsq]; linarith
      exact_mod_cast hmZ
  rw [heq]
  exact hbd N hN

/-- **Theorem 1.3(ii) (Decoupled Monomial-Product Degree-Gap Counting Bounds, Table 2)**:
For depressed polynomial-factorial equations $s \cdot n! = P(x)$ with degree gap $\nu$:
- $\nu = 3$: $O_\varepsilon(N^{5/6 + \varepsilon})$,
- $\nu = 4$: $O_\varepsilon(N^{4/5 + \varepsilon})$,
- $\nu = 5$: $O(N^{0.78939})$,
- $\nu \ge 6$ ($\deg P \ge 3$): $O_\varepsilon(N^{3/4 + \varepsilon})$,
- $\nu \ge 25$ ($\deg P \ge 7$): $O_\varepsilon(N^{2/3 + \varepsilon})$. -/
theorem thm_1_3_part2_degree_gap_bounds (P_deg ν : ℕ)
    (s_mult : ℕ) (hs_mult : 1 ≤ s_mult) (P : ℤ[X])
    (hP_deg : P.natDegree = P_deg) (hP_gap : HasDepressedDegreeGap P ν)
    [DecidablePred (IsPolyFactSol s_mult P)] :
    ((3 ≤ P_deg ∧ ν = 3) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter (IsPolyFactSol s_mult P)).card : ℝ) ≤
        C * (N : ℝ) ^ ((5 / 6 : ℝ) + ε)) ∧
    ((4 ≤ P_deg ∧ ν = 4) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter (IsPolyFactSol s_mult P)).card : ℝ) ≤
        C * (N : ℝ) ^ ((4 / 5 : ℝ) + ε)) ∧
    ((5 ≤ P_deg ∧ ν = 5) → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter (IsPolyFactSol s_mult P)).card : ℝ) ≤
        C * (N : ℝ) ^ (0.78939 : ℝ)) ∧
    ((3 ≤ P_deg ∧ 6 ≤ ν) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter (IsPolyFactSol s_mult P)).card : ℝ) ≤
        C * (N : ℝ) ^ ((3 / 4 : ℝ) + ε)) ∧
    ((7 ≤ P_deg ∧ 25 ≤ ν) → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter (IsPolyFactSol s_mult P)).card : ℝ) ≤
        C * (N : ℝ) ^ ((2 / 3 : ℝ) + ε)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hP, rfl⟩ ε hε
    let δ := min (ε / 2) (1 / 12)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hch : Nat.choose (4 + 1) 4 - 1 = 4 := by decide
    obtain ⟨C, hC, hdyad⟩ := dyadic_cluster_elimination_proved P_deg 3 4 1 2 ((1 / 6 : ℝ) - δ)
      (by omega) (by norm_num) (by norm_num) (by norm_num) (by omega)
      (by norm_num) (by rw [hch]; norm_num)
      (by linarith [min_le_right (ε / 2) (1 / 12)])
      (by norm_num; linarith)
      (by have := table2_nu3; unfold theta_monomial at this; linarith)
      s_mult hs_mult P hP_deg hP_gap δ hδ
    obtain ⟨C', hC', hsum⟩ := dyadic_sum_counting (by linarith) hC (IsPolyFactSol s_mult P) hdyad
    refine ⟨C', hC', fun N hN => le_trans (hsum N hN) ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith [min_le_left (ε / 2) (1 / 12)])) hC'.le
  · rintro ⟨hP, rfl⟩ ε hε
    let δ := min (ε / 2) (1 / 10)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hch : Nat.choose (3 + 1) 3 - 1 = 3 := by decide
    obtain ⟨C, hC, hdyad⟩ := dyadic_cluster_elimination_proved P_deg 4 3 1 (7 / 4) ((1 / 5 : ℝ) - δ)
      (by omega) (by norm_num) (by norm_num) (by norm_num) (by omega)
      (by norm_num) (by rw [hch]; norm_num)
      (by linarith [min_le_right (ε / 2) (1 / 10)])
      (by norm_num; linarith)
      (by have := table2_nu4; unfold theta_monomial at this; linarith)
      s_mult hs_mult P hP_deg hP_gap δ hδ
    obtain ⟨C', hC', hsum⟩ := dyadic_sum_counting (by linarith) hC (IsPolyFactSol s_mult P) hdyad
    refine ⟨C', hC', fun N hN => le_trans (hsum N hN) ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith [min_le_left (ε / 2) (1 / 10)])) hC'.le
  · rintro ⟨hP, rfl⟩
    have hθ5 : (0.210615 : ℝ) < theta_monomial 2 2 5 (76 / 25) := by
      unfold theta_monomial
      have hch : Nat.choose (2 + 2) 2 - 1 = 5 := by decide
      rw [hch]; norm_num
    have hch : Nat.choose (2 + 2) 2 - 1 = 5 := by decide
    obtain ⟨C, hC, hdyad⟩ := dyadic_cluster_elimination_proved P_deg 5 2 2 (76 / 25) 0.210615
      (by omega) (by norm_num) (by norm_num) (by norm_num) (by omega)
      (by norm_num) (by rw [hch]; norm_num) (by norm_num) (by norm_num)
      (by unfold theta_monomial at hθ5; exact hθ5)
      s_mult hs_mult P hP_deg hP_gap 0.000005 (by norm_num)
    obtain ⟨C', hC', hsum⟩ := dyadic_sum_counting (by norm_num) hC (IsPolyFactSol s_mult P) hdyad
    refine ⟨C', hC', fun N hN => le_trans (hsum N hN) ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)) hC'.le
  · rintro ⟨hP, hν⟩ ε hε
    let δ := min (ε / 2) (1 / 8)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hch : Nat.choose (2 + 2) 2 - 1 = 5 := by decide
    obtain ⟨C, hC, hdyad⟩ := dyadic_cluster_elimination_proved P_deg ν 2 2 (16 / 5) ((1 / 4 : ℝ) - δ)
      (by omega) (by omega) (by norm_num) (by norm_num) (by omega)
      (by norm_num) (by rw [hch]; norm_num)
      (by linarith [min_le_right (ε / 2) (1 / 8)])
      (by norm_num; linarith)
      (by have := table2_nu6_ge hν; unfold theta_monomial at this; linarith)
      s_mult hs_mult P hP_deg hP_gap δ hδ
    obtain ⟨C', hC', hsum⟩ := dyadic_sum_counting (by linarith) hC (IsPolyFactSol s_mult P) hdyad
    refine ⟨C', hC', fun N hN => le_trans (hsum N hN) ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith [min_le_left (ε / 2) (1 / 8)])) hC'.le
  · rintro ⟨hP, hν⟩ ε hε
    let δ := min (ε / 2) (1 / 6)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hch : Nat.choose (1 + 6) 1 - 1 = 6 := by decide
    obtain ⟨C, hC, hdyad⟩ := dyadic_cluster_elimination_proved P_deg ν 1 6 4 ((1 / 3 : ℝ) - δ)
      (by omega) (by omega) (by norm_num) (by norm_num) (by omega)
      (by norm_num) (by rw [hch]; norm_num)
      (by linarith [min_le_right (ε / 2) (1 / 6)])
      (by norm_num; linarith)
      (by have := table2_nu_large hν; unfold theta_monomial at this; linarith)
      s_mult hs_mult P hP_deg hP_gap δ hδ
    obtain ⟨C', hC', hsum⟩ := dyadic_sum_counting (by linarith) hC (IsPolyFactSol s_mult P) hdyad
    refine ⟨C', hC', fun N hN => le_trans (hsum N hN) ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith [min_le_left (ε / 2) (1 / 6)])) hC'.le

end GrasGreenbergBrocard
