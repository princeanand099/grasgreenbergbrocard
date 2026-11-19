import GrasGreenbergBrocard.ExternalAxiomsSec8
import GrasGreenbergBrocard.Thm1_1Collapse
import GrasGreenbergBrocard.ExpSumBounds

/-!
# Section 8.2: Effective Tatuzawa Class Number Explosion and Narrow $2^J$-Rank Dichotomy

This file formalizes **Theorem 8.2** of the manuscript:
1. Effective Tatuzawa non-genus class number lower bound (eq. 8.4):
   with at most one exceptional index $n_* \in \mathbb{N}$, every Brocard solution $n \ge 8$ satisfies
   $$h_{\mathrm{non\text{-}gen}}(q_n) := \frac{h(q_n)}{2^{\omega(D_n)-2}} > \frac{0.655\,\varepsilon\,k\,q_n^{1/2-\varepsilon}}{n\log n \cdot 2^{\pi(n)}} = q_n^{1/2-\varepsilon-o(1)}.$$
2. Narrow class group $\mathrm{Cl}^+(q_n) \simeq \mathcal{A}_2(q_n) \oplus \mathrm{Cl}_{\mathrm{odd}}^+(q_n)$ dichotomy:
   either $|\mathrm{Cl}_{\mathrm{odd}}^+(q_n)| \ge q_n^{1/4-\varepsilon}$, or
   $|\mathcal{A}_2(q_n)| \ge 2^{(\frac{\log 2}{4} - \varepsilon) n}$,
   $\log_2 \exp(\mathcal{A}_2(q_n)) \ge (\frac{1}{4\log 2} - \varepsilon)\log n$, and
   $\exp(\mathcal{A}_2(q_n)) \ge n^{\frac{1}{4} - \varepsilon}$.
-/

open Real Filter Finset

namespace GrasGreenbergBrocard

set_option maxHeartbeats 800000

/-- Non-genus class number $h_{\mathrm{non\text{-}gen}}(q_n) := h(q_n) / 2^{\omega(D_n) - 2}$. -/
noncomputable def hNonGen (n X₁ Y₁ : ℕ) (G : RealQuadClassGroupData n X₁ Y₁) : ℝ :=
  (G.h : ℝ) / (2 : ℝ) ^ (omegaNat (fundDisc n) - 2)

private lemma fundDisc_eq_iff_q_n_eq {n₁ n₂ : ℕ} (hn₁ : 4 ≤ n₁) (hn₂ : 4 ≤ n₂) :
    fundDisc n₁ = fundDisc n₂ ↔ q_n n₁ = q_n n₂ := by
  constructor
  · intro heq
    unfold fundDisc at heq
    have hsq1 := q_n_squarefree n₁
    have hsq2 := q_n_squarefree n₂
    split_ifs at heq with h1 h2 h2
    · exact heq
    · have h4 : 4 ∣ q_n n₁ := heq ▸ dvd_mul_right 4 _
      have h2sq : 2 * 2 ∣ q_n n₁ := by simpa using h4
      exact absurd (hsq1 2 h2sq) (by decide)
    · have h4 : 4 ∣ q_n n₂ := heq.symm ▸ dvd_mul_right 4 _
      have h2sq : 2 * 2 ∣ q_n n₂ := by simpa using h4
      exact absurd (hsq2 2 h2sq) (by decide)
    · omega
  · intro hq; unfold fundDisc; rw [hq]

private lemma omegaNat_fundDisc_le_piPrime {n : ℕ} (hn : 8 ≤ n) :
    (omegaNat (fundDisc n) : ℝ) ≤ piPrime (n : ℝ) := by
  have hq_dvd_fac : q_n n ∣ Nat.factorial n := ⟨s_n n ^ 2, (factorial_eq_q_n_mul_s_n_sq n).symm⟩
  have hsub : (fundDisc n).primeFactors ⊆ (Finset.Icc 2 (Nat.floor (n : ℝ))).filter Nat.Prime := by
    intro p hp
    have hp_pr := Nat.prime_of_mem_primeFactors hp
    have hp_dvd := Nat.dvd_of_mem_primeFactors hp
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.floor_natCast]
    refine ⟨⟨hp_pr.two_le, ?_⟩, hp_pr⟩
    unfold fundDisc at hp_dvd
    split_ifs at hp_dvd
    · exact hp_pr.dvd_factorial.mp (dvd_trans hp_dvd hq_dvd_fac)
    · rcases hp_pr.dvd_mul.mp hp_dvd with h4 | hq
      · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_two).mp (hp_pr.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h4))
        omega
      · exact hp_pr.dvd_factorial.mp (dvd_trans hq hq_dvd_fac)
  unfold omegaNat piPrime
  exact_mod_cast Finset.card_le_card hsub

private lemma pellUnit_log_le_half_n_log_n {n m k X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hm : Nat.factorial n + 1 = m ^ 2) (hk : 1 ≤ k)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hpow : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ k) :
    Real.log (pellUnit (q_n n) X₁ Y₁) ≤ (n : ℝ) * Real.log (n : ℝ) / (2 * (k : ℝ)) := by
  have heps_gt1 : 1 < pellUnit (q_n n) X₁ Y₁ := by
    unfold pellUnit
    have hq_pos : 0 < q_n n := by unfold q_n; exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.1.pos)
    have h1 : 1 ≤ X₁ := hfund.1
    have h2 : 0 < (Y₁ : ℝ) * Real.sqrt (q_n n : ℝ) := mul_pos (by exact_mod_cast hfund.2.1) (Real.sqrt_pos.mpr (by exact_mod_cast hq_pos))
    linarith [show (1 : ℝ) ≤ (X₁ : ℝ) by exact_mod_cast h1]
  have h2m_lt : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) < 2 * (m : ℝ) := by
    have hfac : (q_n n : ℝ) * (s_n n : ℝ) ^ 2 = (Nat.factorial n : ℝ) := by
      exact_mod_cast (factorial_eq_q_n_mul_s_n_sq n).symm
    have hsq : ((s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2 < (m : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      have hm_r : (Nat.factorial n : ℝ) + 1 = (m : ℝ) ^ 2 := by exact_mod_cast hm
      linarith
    have hlt : (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) < (m : ℝ) :=
      lt_of_pow_lt_pow_left₀ 2 (Nat.cast_nonneg m) hsq
    linarith
  have h4fac : 4 * (Nat.factorial n + 1) ≤ n ^ n := by
    have hfac_le : Nat.factorial n ≤ n ^ (n - 2) * 2 := by
      have hgen : ∀ j : ℕ, 2 ≤ j → Nat.factorial j ≤ j ^ (j - 2) * 2 := by
        intro j hj
        induction j, hj using Nat.le_induction with
        | base => decide
        | succ t ht ih =>
          rw [Nat.factorial_succ]
          have h1 : t ^ (t - 2) ≤ (t + 1) ^ (t - 2) := Nat.pow_le_pow_left (by omega) _
          have h2 : (t + 1) * (t ^ (t - 2) * 2) ≤ (t + 1) * ((t + 1) ^ (t - 2) * 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right 2 h1)
          have h3 : (t + 1) * ((t + 1) ^ (t - 2) * 2) = (t + 1) ^ (t + 1 - 2) * 2 := by
            have : t + 1 - 2 = (t - 2) + 1 := by omega
            rw [this, pow_succ]; ring
          exact le_trans (Nat.mul_le_mul_left _ ih) (h3 ▸ h2)
      exact hgen n (by omega)
    have hpow_eq : n ^ n = n ^ (n - 2) * n ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have hn2 : 12 ≤ n ^ 2 := by nlinarith
    have hpow_pos : 1 ≤ n ^ (n - 2) := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have h2m_le : 2 * (m : ℝ) ≤ (n : ℝ) ^ ((n : ℝ) / 2) := by
    have hsq : (2 * (m : ℝ)) ^ 2 ≤ ((n : ℝ) ^ ((n : ℝ) / 2)) ^ 2 := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ ((n : ℝ) / 2)) 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
      have hdiv : (n : ℝ) / 2 * (2 : ℕ) = (n : ℝ) := by push_cast; ring
      rw [hdiv, Real.rpow_natCast]
      have : (2 * (m : ℝ)) ^ 2 = 4 * ((Nat.factorial n : ℝ) + 1) := by
        have hm_r : (Nat.factorial n : ℝ) + 1 = (m : ℝ) ^ 2 := by exact_mod_cast hm
        linarith
      rw [this]; exact_mod_cast h4fac
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsq
  have hlog_le := Real.log_le_log (by positivity : (0 : ℝ) < (pellUnit (q_n n) X₁ Y₁) ^ k)
    (le_trans (hpow ▸ h2m_lt.le) h2m_le)
  rw [Real.log_pow, Real.log_rpow (by exact_mod_cast (by omega : 0 < n))] at hlog_le
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **Theorem 8.2 (Effective Tatuzawa Class Number Explosion and Narrow $2^J$-Rank Dichotomy)**:
For any $\varepsilon \in (0, 1/8)$, there exists at most one exceptional integer $n_* \in \mathbb{N}$
such that:
1. For every solution $n \ge 8$ ($n \neq n_*$) to $n! + 1 = m^2$, eq. (8.4) holds:
   $$h_{\mathrm{non\text{-}gen}}(q_n) > \frac{0.655\,\varepsilon\,k\,q_n^{1/2-\varepsilon}}{n\log n \cdot 2^{\pi(n)}}.$$
2. For all sufficiently large solutions $n \neq n_*$, $h_{\mathrm{non\text{-}gen}}(q_n) \ge q_n^{1/2 - 2\varepsilon}$,
   and in $\mathrm{Cl}^+(q_n) \simeq \mathcal{A}_2(q_n) \oplus \mathrm{Cl}_{\mathrm{odd}}^+(q_n)$, either
   $|\mathrm{Cl}_{\mathrm{odd}}^+(q_n)| \ge q_n^{1/4 - \varepsilon}$, OR
   $|\mathcal{A}_2(q_n)| \ge 2^{(\frac{\log 2}{4} - \varepsilon) n}$,
   $\log_2 \exp(\mathcal{A}_2(q_n)) \ge (\frac{1}{4\log 2} - \varepsilon)\log n$, and
   $\exp(\mathcal{A}_2(q_n)) \ge n^{\frac{1}{4} - \varepsilon}$. -/
theorem thm_8_2_tatuzawa_and_narrow_2J_rank (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 8) :
    ∃ n_star : ℕ, ∃ N₀ : ℕ, 8 ≤ N₀ ∧
      (∀ (n m k X₁ Y₁ : ℕ) (G : RealQuadClassGroupData n X₁ Y₁),
        8 ≤ n → n ≠ n_star →
        Nat.factorial n + 1 = m ^ 2 → 1 ≤ k →
        IsFundamentalPell (q_n n) X₁ Y₁ →
        (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ k →
        (0.655 : ℝ) * ε * (k : ℝ) * (q_n n : ℝ) ^ (1 / 2 - ε) /
          ((n : ℝ) * Real.log (n : ℝ) * (2 : ℝ) ^ (piPrime (n : ℝ))) < hNonGen n X₁ Y₁ G) ∧
      (∀ (n m k X₁ Y₁ : ℕ) (G : RealQuadClassGroupData n X₁ Y₁),
        N₀ ≤ n → n ≠ n_star →
        Nat.factorial n + 1 = m ^ 2 → 1 ≤ k →
        IsFundamentalPell (q_n n) X₁ Y₁ →
        (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ k →
        (q_n n : ℝ) ^ (1 / 2 - 2 * ε) ≤ hNonGen n X₁ Y₁ G ∧
        ((q_n n : ℝ) ^ (1 / 4 - ε) ≤ (G.card_Cl_odd : ℝ) ∨
          ((2 : ℝ) ^ ((Real.log 2 / 4 - ε) * (n : ℝ)) ≤ (G.card_A2 : ℝ) ∧
           (1 / (4 * Real.log 2) - ε) * Real.log (n : ℝ) ≤ Real.log (G.exp_A2 : ℝ) / Real.log 2 ∧
           (n : ℝ) ^ (1 / 4 - ε) ≤ (G.exp_A2 : ℝ)))) := by
  classical
  obtain ⟨D_star, hTat⟩ := tatuzawa_effective_siegel ε hε0 hε1
  let n_star : ℕ :=
    if h : ∃ n : ℕ, 8 ≤ n ∧ (∃ m : ℕ, Nat.factorial n + 1 = m ^ 2) ∧ fundDisc n = D_star
    then Classical.choose h else 0
  have hn_star_uniq : ∀ n m : ℕ, 8 ≤ n → n ≠ n_star → Nat.factorial n + 1 = m ^ 2 →
      fundDisc n ≠ D_star := by
    intro n m hn hne hm hD
    have hex : ∃ n' : ℕ, 8 ≤ n' ∧ (∃ m' : ℕ, Nat.factorial n' + 1 = m' ^ 2) ∧ fundDisc n' = D_star :=
      ⟨n, hn, ⟨m, hm⟩, hD⟩
    have hspec := Classical.choose_spec hex
    have hns_eq : n_star = Classical.choose hex := dif_pos hex
    obtain ⟨m', hm'⟩ := hspec.2.1
    have hq_eq : q_n n = q_n n_star := (fundDisc_eq_iff_q_n_eq (by omega) (by omega)).mp (by rw [hD, hns_eq, hspec.2.2])
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact q_n_ne_of_solutions (by omega) hlt hm (hns_eq ▸ hm') hq_eq
    · exact q_n_ne_of_solutions (by omega) hgt (hns_eq ▸ hm') hm hq_eq.symm
  have h84 : ∀ (n m k X₁ Y₁ : ℕ) (G : RealQuadClassGroupData n X₁ Y₁),
      8 ≤ n → n ≠ n_star →
      Nat.factorial n + 1 = m ^ 2 → 1 ≤ k →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ k →
      (0.655 : ℝ) * ε * (k : ℝ) * (q_n n : ℝ) ^ (1 / 2 - ε) /
        ((n : ℝ) * Real.log (n : ℝ) * (2 : ℝ) ^ (piPrime (n : ℝ))) < hNonGen n X₁ Y₁ G := by
    intro n m k X₁ Y₁ G hn hne hm hk hfund hpow
    have hD_ne := hn_star_uniq n m hn hne hm
    have hL1 := hTat n X₁ Y₁ G hn hD_ne
    have hq_pos : (0 : ℝ) < (q_n n : ℝ) := by
      exact_mod_cast (show 0 < q_n n by unfold q_n; exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.1.pos))
    have hD_pos : (0 : ℝ) < (fundDisc n : ℝ) := by
      unfold fundDisc; split_ifs
      · exact hq_pos
      · push_cast; linarith
    have hD_ge_q : (q_n n : ℝ) ^ (1 / 2 - ε) ≤ Real.sqrt (fundDisc n : ℝ) * (fundDisc n : ℝ) ^ (-ε) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hD_pos]
      have hle : (q_n n : ℝ) ≤ (fundDisc n : ℝ) := by
        unfold fundDisc; split_ifs
        · exact le_rfl
        · push_cast; linarith
      exact Real.rpow_le_rpow hq_pos.le hle (by linarith)
    have hR_ub : G.R ≤ (n : ℝ) * Real.log (n : ℝ) / (2 * (k : ℝ)) :=
      le_trans G.R_le_log_eps (pellUnit_log_le_half_n_log_n hn hm hk hfund hpow)
    have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hh_lb : (0.655 : ℝ) * ε * (k : ℝ) * (q_n n : ℝ) ^ (1 / 2 - ε) / ((n : ℝ) * Real.log (n : ℝ)) < (G.h : ℝ) := by
      have hcnf := G.dirichlet_cnf
      have h1 : (1 / 2 : ℝ) * (0.655 : ℝ) * ε * (q_n n : ℝ) ^ (1 / 2 - ε) < (G.h : ℝ) * G.R := by
        rw [hcnf]
        have hsqrt_pos : 0 < Real.sqrt (fundDisc n : ℝ) := Real.sqrt_pos.mpr hD_pos
        have h2 : (1 / 2 : ℝ) * Real.sqrt (fundDisc n : ℝ) * ((0.655 : ℝ) * ε * (fundDisc n : ℝ) ^ (-ε)) <
            (1 / 2 : ℝ) * Real.sqrt (fundDisc n : ℝ) * G.L1_val := by gcongr
        have h3 : (1 / 2 : ℝ) * (0.655 : ℝ) * ε * (q_n n : ℝ) ^ (1 / 2 - ε) ≤
            (1 / 2 : ℝ) * Real.sqrt (fundDisc n : ℝ) * ((0.655 : ℝ) * ε * (fundDisc n : ℝ) ^ (-ε)) := by
          have : (1 / 2 : ℝ) * Real.sqrt (fundDisc n : ℝ) * ((0.655 : ℝ) * ε * (fundDisc n : ℝ) ^ (-ε)) =
              (1 / 2 : ℝ) * (0.655 : ℝ) * ε * (Real.sqrt (fundDisc n : ℝ) * (fundDisc n : ℝ) ^ (-ε)) := by ring
          rw [this]; exact mul_le_mul_of_nonneg_left hD_ge_q (by positivity)
        linarith
      have h2 : (G.h : ℝ) * G.R ≤ (G.h : ℝ) * ((n : ℝ) * Real.log (n : ℝ) / (2 * (k : ℝ))) :=
        mul_le_mul_of_nonneg_left hR_ub (Nat.cast_nonneg _)
      have h3 : (1 / 2 : ℝ) * (0.655 : ℝ) * ε * (q_n n : ℝ) ^ (1 / 2 - ε) <
          (G.h : ℝ) * ((n : ℝ) * Real.log (n : ℝ) / (2 * (k : ℝ))) := lt_of_lt_of_le h1 h2
      rw [div_lt_iff₀ (mul_pos (by exact_mod_cast (by omega : 0 < n)) hlogn_pos)]
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have h4 := mul_lt_mul_of_pos_right h3 (show (0 : ℝ) < 2 * (k : ℝ) by positivity)
      have h5 : (G.h : ℝ) * ((n : ℝ) * Real.log (n : ℝ) / (2 * (k : ℝ))) * (2 * (k : ℝ)) =
          (G.h : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by field_simp [hk_pos.ne']
      linarith
    have hpow_le : (2 : ℝ) ^ (omegaNat (fundDisc n) - 2) ≤ (2 : ℝ) ^ (piPrime (n : ℝ)) := by
      rw [← Real.rpow_natCast]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      exact le_trans (by exact_mod_cast Nat.sub_le _ _) (omegaNat_fundDisc_le_piPrime hn)
    unfold hNonGen
    calc (0.655 : ℝ) * ε * (k : ℝ) * (q_n n : ℝ) ^ (1 / 2 - ε) /
          ((n : ℝ) * Real.log (n : ℝ) * (2 : ℝ) ^ (piPrime (n : ℝ)))
        = ((0.655 : ℝ) * ε * (k : ℝ) * (q_n n : ℝ) ^ (1 / 2 - ε) / ((n : ℝ) * Real.log (n : ℝ))) /
          (2 : ℝ) ^ (piPrime (n : ℝ)) := by rw [div_div]
      _ < (G.h : ℝ) / (2 : ℝ) ^ (piPrime (n : ℝ)) := by gcongr
      _ ≤ (G.h : ℝ) / (2 : ℝ) ^ (omegaNat (fundDisc n) - 2) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hpow_le
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by
    have := Real.exp_one_gt_d9
    exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr (by linarith)
  have hlog2_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
    have : Real.exp (1 / 2 : ℝ) < 2 := by
      have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by rw [sq, ← Real.exp_add]; norm_num
      have hlt : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr this
  obtain ⟨c₀, hc₀, hlogq_O⟩ := log_q_n_asymptotic
  have hlogq_o : (fun n : ℕ => Real.log (q_n n : ℝ) - Real.log 2 * (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    rw [Asymptotics.isLittleO_iff]; intro δ hδ
    obtain ⟨C₀, hC₀⟩ := hlogq_O.bound
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hC₀
    have htend : Filter.Tendsto (fun n : ℕ => C₀ * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ)))) atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      have h2 : Filter.Tendsto (fun n : ℕ => -c₀ * Real.sqrt (Real.log (n : ℝ))) atTop atBot :=
        Filter.Tendsto.const_mul_atTop_of_neg (r := -c₀) (by linarith) h1
      simpa using (Real.tendsto_exp_atBot.comp h2).const_mul C₀
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (htend.eventually (Metric.ball_mem_nhds 0 hδ))
    refine Filter.eventually_atTop.mpr ⟨max (max N₁ N₂) 16, fun n hn => ?_⟩
    have h1 := hN₁ n (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn))
    have h2 := hN₂ n (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn))
    have hC0_nn : 0 ≤ C₀ := by
      have h16 := hN₁ (max N₁ 16) (le_max_left _ _)
      have hpos : 0 < ((max N₁ 16 : ℕ) : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log ((max N₁ 16 : ℕ) : ℝ))) := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos] at h16
      exact nonneg_of_mul_nonneg_left (le_trans (abs_nonneg _) h16) hpos
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hC0_nn (Real.exp_pos _).le)] at h2
    have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (Real.exp_pos _).le)] at h1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
    calc |Real.log (q_n n : ℝ) - Real.log 2 * (n : ℝ)|
        ≤ C₀ * ((n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ)))) := h1
      _ = (C₀ * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ)))) * (n : ℝ) := by ring
      _ ≤ δ * (n : ℝ) := mul_le_mul_of_nonneg_right h2.le hnn
  obtain ⟨N_q, hN_q⟩ := Filter.eventually_atTop.mp (Asymptotics.IsLittleO.bound hlogq_o (show (0 : ℝ) < ε / 100 by positivity))
  obtain ⟨N_pi, hN_pi⟩ := Filter.eventually_atTop.mp (Asymptotics.IsLittleO.bound pnt_pi_asymptotic (show (0 : ℝ) < ε / 100 by positivity))
  obtain ⟨N_podd, hN_podd⟩ := Filter.eventually_atTop.mp (Asymptotics.IsLittleO.bound card_Podd_asymptotic (show (0 : ℝ) < ε / 100 by positivity))
  have h_inv_log : Filter.Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N_lg, hN_lg⟩ := Filter.eventually_atTop.mp (h_inv_log.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / 100 by positivity)))
  have h_log_div_n : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) * Real.log (n : ℝ) / ((0.655 : ℝ) * ε)) / (n : ℝ)) atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (2 * Real.log (n : ℝ) + |Real.log ((0.655 : ℝ) * ε)|) / (n : ℝ)) atTop (nhds 0) := by
      have ha0 : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
        have hlp := log_pow_div_rpow_tendsto_zero 1 (by norm_num : (0 : ℝ) < 1)
        exact hlp.congr' (by filter_upwards [Filter.eventually_ge_atTop 1] with n _; simp)
      have ha : Filter.Tendsto (fun n : ℕ => 2 * (Real.log (n : ℝ) / (n : ℝ))) atTop (nhds 0) := by
        simpa using ha0.const_mul 2
      have hb : Filter.Tendsto (fun n : ℕ => |Real.log ((0.655 : ℝ) * ε)| / (n : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa [add_div, mul_div_assoc] using ha.add hb
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [Filter.eventually_ge_atTop 100] with n hn
    have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hlogn_le : Real.log (n : ℝ) ≤ (n : ℝ) := le_trans (Real.log_le_sub_one_of_pos (by positivity)) (by linarith)
    have harg_ge1 : 1 ≤ (n : ℝ) * Real.log (n : ℝ) / ((0.655 : ℝ) * ε) := by
      rw [one_le_div (by positivity)]
      have : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have : (1 : ℝ) ≤ Real.log (n : ℝ) := (Real.le_log_iff_exp_le (by positivity)).mpr (by linarith [Real.exp_one_lt_d9])
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.log_nonneg harg_ge1) (Nat.cast_nonneg _))]
    gcongr
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hlogn_pos.ne']
    have hloglog : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := Real.log_le_log hlogn_pos hlogn_le
    linarith [neg_le_abs (Real.log ((0.655 : ℝ) * ε))]
  obtain ⟨N_ld, hN_ld⟩ := Filter.eventually_atTop.mp (h_log_div_n.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / 100 by positivity)))
  let N₀ := max (max (max N_q (Nat.ceil N_pi)) (max N_podd N_lg)) (max N_ld 1000)
  refine ⟨n_star, N₀, by omega, h84, ?_⟩
  intro n m k X₁ Y₁ G hn hne hm hk hfund hpow
  have h84_n := h84 n m k X₁ Y₁ G (by omega) hne hm hk hfund hpow
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hq_pos : (0 : ℝ) < (q_n n : ℝ) := by
    exact_mod_cast (show 0 < q_n n by unfold q_n; exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.1.pos))
  have hlogq_bd := hN_q n (by omega)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hn_pos.le] at hlogq_bd
  have hlogq_lb : (Real.log 2 - ε / 100) * (n : ℝ) ≤ Real.log (q_n n : ℝ) := by linarith [(abs_le.mp hlogq_bd).1]
  have hlogq_ub : Real.log (q_n n : ℝ) ≤ (Real.log 2 + ε / 100) * (n : ℝ) := by linarith [(abs_le.mp hlogq_bd).2]
  have hpi_bd := hN_pi (n : ℝ) (le_trans (Nat.le_ceil N_pi) (by exact_mod_cast (by omega : Nat.ceil N_pi ≤ n)))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn_pos.le hlogn_pos.le)] at hpi_bd
  have hpi_ub : piPrime (n : ℝ) ≤ (1 + ε / 100) * ((n : ℝ) / Real.log (n : ℝ)) := by linarith [(abs_le.mp hpi_bd).2]
  have hil := hN_lg n (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg zero_le_one hlogn_pos.le)] at hil
  have hld := hN_ld n (by omega)
  rw [Real.dist_eq, sub_zero] at hld
  have hld_ub : Real.log ((n : ℝ) * Real.log (n : ℝ) / ((0.655 : ℝ) * ε)) ≤ (ε / 100) * (n : ℝ) := by
    have := (abs_le.mp hld.le).2
    rwa [div_le_iff₀ hn_pos] at this
  have hpi_small : piPrime (n : ℝ) * Real.log 2 ≤ (ε / 50) * (n : ℝ) := by
    have h1 : (n : ℝ) / Real.log (n : ℝ) ≤ (ε / 100) * (n : ℝ) := by
      have := mul_le_mul_of_nonneg_right hil.le hn_pos.le; simpa [div_eq_mul_inv, mul_comm] using this
    have h2 : piPrime (n : ℝ) ≤ (1 + ε / 100) * ((ε / 100) * (n : ℝ)) :=
      le_trans hpi_ub (mul_le_mul_of_nonneg_left h1 (by positivity))
    have h3 : (1 + ε / 100) * (ε / 100) ≤ ε / 50 := by nlinarith only [hε0, hε1]
    have hpi_le : piPrime (n : ℝ) ≤ (ε / 50) * (n : ℝ) := by nlinarith only [h2, h3, hn_pos]
    have hpi_nn : 0 ≤ piPrime (n : ℝ) := Nat.cast_nonneg _
    nlinarith only [hpi_le, hlog2_lt1, hlog2_pos, hpi_nn, hn_pos, hε0]
  have h_ng_lb : (q_n n : ℝ) ^ (1 / 2 - 2 * ε) ≤ hNonGen n X₁ Y₁ G := by
    have h1 : (q_n n : ℝ) ^ (1 / 2 - 2 * ε) ≤
        (0.655 : ℝ) * ε * (k : ℝ) * (q_n n : ℝ) ^ (1 / 2 - ε) /
          ((n : ℝ) * Real.log (n : ℝ) * (2 : ℝ) ^ (piPrime (n : ℝ))) := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : (n : ℝ) * Real.log (n : ℝ) / ((0.655 : ℝ) * ε) * (2 : ℝ) ^ (piPrime (n : ℝ)) ≤ (q_n n : ℝ) ^ ε := by
        rw [← Real.log_le_log_iff (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num), Real.log_rpow hq_pos]
        nlinarith only [hld_ub, hpi_small, hlogq_lb, hlog2_gt_half, hn_pos, hε0, hε1]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hqp : 0 < (q_n n : ℝ) ^ (1 / 2 - ε) := Real.rpow_pos_of_pos hq_pos (1 / 2 - ε)
      calc (q_n n : ℝ) ^ (1 / 2 - 2 * ε) * ((n : ℝ) * Real.log (n : ℝ) * (2 : ℝ) ^ (piPrime (n : ℝ)))
          = (0.655 : ℝ) * ε * (q_n n : ℝ) ^ (1 / 2 - 2 * ε) *
            ((n : ℝ) * Real.log (n : ℝ) / ((0.655 : ℝ) * ε) * (2 : ℝ) ^ (piPrime (n : ℝ))) := by field_simp [(by positivity : ε ≠ 0)]
        _ ≤ (0.655 : ℝ) * ε * (q_n n : ℝ) ^ (1 / 2 - 2 * ε) * (q_n n : ℝ) ^ ε := by gcongr
        _ = (0.655 : ℝ) * ε * (q_n n : ℝ) ^ (1 / 2 - ε) := by rw [mul_assoc, ← Real.rpow_add hq_pos]; ring_nf
        _ ≤ (0.655 : ℝ) * ε * (k : ℝ) * (q_n n : ℝ) ^ (1 / 2 - ε) := by
            have : (0.655 : ℝ) * ε * (q_n n : ℝ) ^ (1 / 2 - ε) * 1 ≤
                (0.655 : ℝ) * ε * (q_n n : ℝ) ^ (1 / 2 - ε) * (k : ℝ) :=
              mul_le_mul_of_nonneg_left hk1 (by positivity)
            linarith only [this]
    exact le_trans h1 h84_n.le
  refine ⟨h_ng_lb, ?_⟩
  by_cases hodd : (q_n n : ℝ) ^ (1 / 4 - ε) ≤ (G.card_Cl_odd : ℝ)
  · exact Or.inl hodd
  · right
    push Not at hodd
    have h2h_ge : (q_n n : ℝ) ^ (1 / 2 - 2 * ε) ≤ (2 * G.h : ℝ) := by
      have hpow_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (omegaNat (fundDisc n) - 2) := one_le_pow₀ (by norm_num)
      have h1 : hNonGen n X₁ Y₁ G ≤ (G.h : ℝ) := div_le_self (Nat.cast_nonneg _) hpow_ge1
      have : (G.h : ℝ) ≤ (2 * G.h : ℝ) := by linarith [show (0 : ℝ) ≤ G.h by positivity]
      linarith only [h_ng_lb, h1, this]
    have hA2_gt_q : (q_n n : ℝ) ^ (1 / 4 - ε) < (G.card_A2 : ℝ) := by
      have hdecomp : (G.card_A2 : ℝ) * (G.card_Cl_odd : ℝ) = (2 * G.h : ℝ) := by
        exact_mod_cast G.narrow_class_decomp
      have h1 : (q_n n : ℝ) ^ (1 / 4 - ε) * (G.card_Cl_odd : ℝ) < (q_n n : ℝ) ^ (1 / 4 - ε) * (q_n n : ℝ) ^ (1 / 4 - ε) :=
        mul_lt_mul_of_pos_left hodd (Real.rpow_pos_of_pos hq_pos _)
      have h2 : (q_n n : ℝ) ^ (1 / 4 - ε) * (q_n n : ℝ) ^ (1 / 4 - ε) = (q_n n : ℝ) ^ (1 / 2 - 2 * ε) := by
        rw [← Real.rpow_add hq_pos]; ring_nf
      have h3 : (q_n n : ℝ) ^ (1 / 4 - ε) * (G.card_Cl_odd : ℝ) < (G.card_A2 : ℝ) * (G.card_Cl_odd : ℝ) := by linarith only [h1, h2, h2h_ge, hdecomp]
      exact lt_of_mul_lt_mul_right h3 (Nat.cast_nonneg _)
    have hlogA2_lb : (1 / 4 - ε) * (Real.log 2 - ε / 100) * (n : ℝ) ≤ Real.log (G.card_A2 : ℝ) := by
      have h1 := Real.log_le_log (Real.rpow_pos_of_pos hq_pos _) hA2_gt_q.le
      rw [Real.log_rpow hq_pos] at h1
      nlinarith only [h1, hlogq_lb, hε1]
    have hA2_pow2 : (2 : ℝ) ^ ((Real.log 2 / 4 - ε) * (n : ℝ)) ≤ (G.card_A2 : ℝ) := by
      rw [← Real.log_le_log_iff (by positivity) (by exact_mod_cast G.card_A2_pos), Real.log_rpow (by norm_num)]
      nlinarith only [hlogA2_lb, hlog2_pos, hlog2_lt1, hn_pos, hε0, hε1]
    have hrank_ub : (G.rank2_A2 : ℝ) ≤ (Real.log 2 + ε / 20) * ((n : ℝ) / Real.log (n : ℝ)) := by
      have hsub_podd : (fundDisc n).primeFactors ⊆ insert 2 (Podd n) := by
        intro p hp
        have hp_pr := Nat.prime_of_mem_primeFactors hp
        have hp_dvd := Nat.dvd_of_mem_primeFactors hp
        by_cases hp2 : p = 2
        · exact Finset.mem_insert.mpr (Or.inl hp2)
        · refine Finset.mem_insert.mpr (Or.inr ?_)
          have hp_q : p ∣ q_n n := by
            unfold fundDisc at hp_dvd; split_ifs at hp_dvd
            · exact hp_dvd
            · exact (hp_pr.dvd_mul.mp hp_dvd).resolve_left (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_two).mp (hp_pr.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h))))
          unfold q_n at hp_q
          rw [hp_pr.prime.dvd_finset_prod_iff] at hp_q
          obtain ⟨q, hq, hqd⟩ := hp_q
          have hq_pr := (Finset.mem_filter.mp hq).2.1
          have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp hqd
          exact hpq ▸ hq
      have hcard_le : omegaNat (fundDisc n) ≤ (Podd n).card + 1 := by
        unfold omegaNat
        exact le_trans (Finset.card_le_card hsub_podd) (Finset.card_insert_le _ _)
      have hrank_le : (G.rank2_A2 : ℝ) ≤ ((Podd n).card : ℝ) := by
        rw [G.gauss_genus_rank2]; exact_mod_cast (by omega : omegaNat (fundDisc n) - 1 ≤ (Podd n).card)
      have hpodd_bd := hN_podd n (by omega)
      have hpi_nn : 0 ≤ piPrime (n : ℝ) := Nat.cast_nonneg _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpi_nn] at hpodd_bd
      have hpodd_ub : ((Podd n).card : ℝ) ≤ (Real.log 2 + ε / 100) * piPrime (n : ℝ) := by linarith [(abs_le.mp hpodd_bd).2]
      calc (G.rank2_A2 : ℝ) ≤ ((Podd n).card : ℝ) := hrank_le
        _ ≤ (Real.log 2 + ε / 100) * piPrime (n : ℝ) := hpodd_ub
        _ ≤ (Real.log 2 + ε / 100) * ((1 + ε / 100) * ((n : ℝ) / Real.log (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hpi_ub (by positivity)
        _ ≤ (Real.log 2 + ε / 20) * ((n : ℝ) / Real.log (n : ℝ)) := by
            have h1 : (Real.log 2 + ε / 100) * (1 + ε / 100) ≤ Real.log 2 + ε / 20 := by nlinarith only [hlog2_lt1, hε0, hε1]
            have h2 : 0 ≤ (n : ℝ) / Real.log (n : ℝ) := div_nonneg hn_pos.le hlogn_pos.le
            nlinarith only [h1, h2]
    have hrank_pos : (0 : ℝ) < (G.rank2_A2 : ℝ) := by
      have hcard_gt1 : 1 < G.card_A2 := by
        have hq_gt1 : 1 < (q_n n : ℝ) := by
          have : 0 < Real.log (q_n n : ℝ) := by nlinarith only [hlogq_lb, hlog2_gt_half, hn_pos, hε1]
          exact (Real.log_pos_iff hq_pos.le).mp this
        have : (1 : ℝ) < (q_n n : ℝ) ^ (1 / 4 - ε) := Real.one_lt_rpow hq_gt1 (by linarith only [hε1])
        exact_mod_cast (by linarith only [this, hA2_gt_q] : (1 : ℝ) < (G.card_A2 : ℝ))
      have hpos : 0 < G.rank2_A2 := by
        by_contra h0; push Not at h0
        have h0' : G.rank2_A2 = 0 := by omega
        have := G.card_A2_le_exp_pow_rank
        rw [h0', pow_zero] at this; omega
      exact_mod_cast hpos
    have h_ng_tight : (q_n n : ℝ) ^ (1 / 2 - (11 / 10 : ℝ) * ε) ≤ hNonGen n X₁ Y₁ G := by
      have h1' : (q_n n : ℝ) ^ (1 / 2 - (11 / 10 : ℝ) * ε) ≤
          (0.655 : ℝ) * ε * (k : ℝ) * (q_n n : ℝ) ^ (1 / 2 - ε) /
            ((n : ℝ) * Real.log (n : ℝ) * (2 : ℝ) ^ (piPrime (n : ℝ))) := by
        rw [le_div_iff₀ (by positivity)]
        have h2' : (n : ℝ) * Real.log (n : ℝ) / ((0.655 : ℝ) * ε) * (2 : ℝ) ^ (piPrime (n : ℝ)) ≤ (q_n n : ℝ) ^ ((1 / 10 : ℝ) * ε) := by
          rw [← Real.log_le_log_iff (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num), Real.log_rpow hq_pos]
          nlinarith only [hld_ub, hpi_small, hlogq_lb, hlog2_gt_half, hn_pos, hε0, hε1]
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        have hqp : 0 < (q_n n : ℝ) ^ (1 / 2 - ε) := Real.rpow_pos_of_pos hq_pos (1 / 2 - ε)
        calc (q_n n : ℝ) ^ (1 / 2 - (11 / 10 : ℝ) * ε) * ((n : ℝ) * Real.log (n : ℝ) * (2 : ℝ) ^ (piPrime (n : ℝ)))
            = (0.655 : ℝ) * ε * (q_n n : ℝ) ^ (1 / 2 - (11 / 10 : ℝ) * ε) *
              ((n : ℝ) * Real.log (n : ℝ) / ((0.655 : ℝ) * ε) * (2 : ℝ) ^ (piPrime (n : ℝ))) := by field_simp [(by positivity : ε ≠ 0)]
          _ ≤ (0.655 : ℝ) * ε * (q_n n : ℝ) ^ (1 / 2 - (11 / 10 : ℝ) * ε) * (q_n n : ℝ) ^ ((1 / 10 : ℝ) * ε) := by gcongr
          _ = (0.655 : ℝ) * ε * (q_n n : ℝ) ^ (1 / 2 - ε) := by rw [mul_assoc, ← Real.rpow_add hq_pos]; ring_nf
          _ ≤ (0.655 : ℝ) * ε * (k : ℝ) * (q_n n : ℝ) ^ (1 / 2 - ε) := by
              have : (0.655 : ℝ) * ε * (q_n n : ℝ) ^ (1 / 2 - ε) * 1 ≤
                  (0.655 : ℝ) * ε * (q_n n : ℝ) ^ (1 / 2 - ε) * (k : ℝ) :=
                mul_le_mul_of_nonneg_left hk1 (by positivity)
              linarith only [this]
      exact le_trans h1' h84_n.le
    have hA2_tight : (q_n n : ℝ) ^ (1 / 4 - (1 / 10 : ℝ) * ε) < (G.card_A2 : ℝ) := by
      have hdecomp : (G.card_A2 : ℝ) * (G.card_Cl_odd : ℝ) = (2 * G.h : ℝ) := by exact_mod_cast G.narrow_class_decomp
      have hpow_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (omegaNat (fundDisc n) - 2) := one_le_pow₀ (by norm_num)
      have h2h_t : (q_n n : ℝ) ^ (1 / 2 - (11 / 10 : ℝ) * ε) ≤ (2 * G.h : ℝ) := by
        have h1 := div_le_self (Nat.cast_nonneg G.h) hpow_ge1
        have h2 : (G.h : ℝ) ≤ (2 * G.h : ℝ) := by linarith [show (0 : ℝ) ≤ G.h by positivity]
        unfold hNonGen at h_ng_tight; linarith only [h_ng_tight, h1, h2]
      have h1' : (q_n n : ℝ) ^ (1 / 4 - (1 / 10 : ℝ) * ε) * (G.card_Cl_odd : ℝ) <
          (q_n n : ℝ) ^ (1 / 4 - (1 / 10 : ℝ) * ε) * (q_n n : ℝ) ^ (1 / 4 - ε) :=
        mul_lt_mul_of_pos_left hodd (Real.rpow_pos_of_pos hq_pos _)
      have h2' : (q_n n : ℝ) ^ (1 / 4 - (1 / 10 : ℝ) * ε) * (q_n n : ℝ) ^ (1 / 4 - ε) =
          (q_n n : ℝ) ^ (1 / 2 - (11 / 10 : ℝ) * ε) := by rw [← Real.rpow_add hq_pos]; ring_nf
      exact lt_of_mul_lt_mul_right (by linarith only [h1', h2', h2h_t, hdecomp] : (q_n n : ℝ) ^ (1 / 4 - (1 / 10 : ℝ) * ε) * (G.card_Cl_odd : ℝ) < (G.card_A2 : ℝ) * (G.card_Cl_odd : ℝ)) (Nat.cast_nonneg _)
    have hlogA2_tight : (1 / 4 - (1 / 10 : ℝ) * ε) * (Real.log 2 - ε / 100) * (n : ℝ) ≤ Real.log (G.card_A2 : ℝ) := by
      have h' := Real.log_le_log (Real.rpow_pos_of_pos hq_pos _) hA2_tight.le
      rw [Real.log_rpow hq_pos] at h'
      nlinarith only [h', hlogq_lb, hε1]
    have h1_rank : Real.log (G.card_A2 : ℝ) ≤ (G.rank2_A2 : ℝ) * Real.log (G.exp_A2 : ℝ) := by
      have hle := Real.log_le_log (by exact_mod_cast G.card_A2_pos) (by exact_mod_cast G.card_A2_le_exp_pow_rank)
      rwa [Nat.cast_pow, Real.log_pow] at hle
    have hlog_exp_tight : (1 / 4 - ε * Real.log 2) * Real.log (n : ℝ) ≤ Real.log (G.exp_A2 : ℝ) := by
      have hmul_le : (G.rank2_A2 : ℝ) * ((1 / 4 - ε * Real.log 2) * Real.log (n : ℝ)) ≤ Real.log (G.card_A2 : ℝ) := by
        calc (G.rank2_A2 : ℝ) * ((1 / 4 - ε * Real.log 2) * Real.log (n : ℝ))
            ≤ ((Real.log 2 + ε / 20) * ((n : ℝ) / Real.log (n : ℝ))) * ((1 / 4 - ε * Real.log 2) * Real.log (n : ℝ)) :=
              mul_le_mul_of_nonneg_right hrank_ub (mul_nonneg (by nlinarith only [hlog2_lt1, hε0, hε1]) hlogn_pos.le)
          _ = (Real.log 2 + ε / 20) * (1 / 4 - ε * Real.log 2) * (n : ℝ) := by field_simp [hlogn_pos.ne']
          _ ≤ (1 / 4 - (1 / 10 : ℝ) * ε) * (Real.log 2 - ε / 100) * (n : ℝ) := by
              nlinarith only [hlog2_gt_half, hlog2_lt1, hn_pos, hε0, hε1]
          _ ≤ Real.log (G.card_A2 : ℝ) := hlogA2_tight
      exact le_of_mul_le_mul_left (le_trans hmul_le h1_rank) hrank_pos
    have hlog2_exp_lb : (1 / (4 * Real.log 2) - ε) * Real.log (n : ℝ) ≤ Real.log (G.exp_A2 : ℝ) / Real.log 2 := by
      rw [le_div_iff₀ hlog2_pos]
      have h1 : (1 / (4 * Real.log 2) - ε) * Real.log 2 = 1 / 4 - ε * Real.log 2 := by
        field_simp [hlog2_pos.ne']
      calc (1 / (4 * Real.log 2) - ε) * Real.log (n : ℝ) * Real.log 2
          = ((1 / (4 * Real.log 2) - ε) * Real.log 2) * Real.log (n : ℝ) := by ring
        _ = (1 / 4 - ε * Real.log 2) * Real.log (n : ℝ) := by rw [h1]
        _ ≤ Real.log (G.exp_A2 : ℝ) := hlog_exp_tight
    have hexp_lb : (n : ℝ) ^ (1 / 4 - ε) ≤ (G.exp_A2 : ℝ) := by
      rw [← Real.log_le_log_iff (by positivity) (by exact_mod_cast G.exp_A2_pos), Real.log_rpow hn_pos]
      have : (1 / 4 - ε) * Real.log (n : ℝ) ≤ (1 / 4 - ε * Real.log 2) * Real.log (n : ℝ) := by
        nlinarith only [hlog2_lt1, hlogn_pos, hε0]
      exact le_trans this hlog_exp_tight
    exact ⟨hA2_pow2, hlog2_exp_lb, hexp_lb⟩

end GrasGreenbergBrocard
