import GrasGreenbergBrocard.Prop6_1FourGCD
import GrasGreenbergBrocard.ValuationParityThmHelpers

/-!
# Section 6.3: Odd-Harmonic Vaaler Diagonal Non-Vanishing for Parity-Flip Primes

This file formalizes **Lemma 6.3 (eq. 6.7)** of the manuscript:
for `4 ≤ n₁ < n₂` with `h := n₂ - n₁`, the logarithmic factorial weight of the parity-flip primes
`{3 ≤ p ≤ n₁ : 2 ∤ v_p(n₂! / n₁!)}` satisfies
`∑_{3 ≤ p ≤ n₁, 2 ∤ v_p(P)} v_p(n₁!) log p = (1/2) n₁ log h + o(n₁ log n₁)` (for `h ≥ n₁^δ`)
and `≤ (δ + o(1)) n₁ log n₁` (for `h ≤ n₁^δ`).
In particular, when `h = n₁^α` (`α ∈ [0, 1)`), the sum is `(α/2 + o(1)) n₁ log n₁`.
-/

open scoped BigOperators
open Real Finset Filter

namespace GrasGreenbergBrocard

set_option maxHeartbeats 800000

/-- The logarithmic factorial weight of parity-flip primes `3 ≤ p ≤ n₁` with `2 ∤ v_p(n₂!/n₁!)`. -/
noncomputable def parityFlipWeight (n₁ n₂ : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 3 n₁).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (P_ratio n₁ n₂)),
    (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)

private lemma padicValNat_P_ratio_eq_sub {n₁ n₂ p : ℕ} (hlt : n₁ < n₂) (hp : p.Prime) :
    padicValNat p (P_ratio n₁ n₂) =
      padicValNat p (Nat.factorial n₂) - padicValNat p (Nat.factorial n₁) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmul := P_ratio_mul_factorial hlt
  have hP_pos : 0 < P_ratio n₁ n₂ := by
    by_contra h0
    have h0' : P_ratio n₁ n₂ = 0 := by omega
    rw [h0', zero_mul] at hmul
    exact (Nat.factorial_pos n₂).ne' hmul.symm
  have hv := congrArg (padicValNat p) hmul
  rw [padicValNat.mul hP_pos.ne' (Nat.factorial_pos n₁).ne'] at hv
  omega

private lemma neg_one_pow_val_sum_eq {n₁ n₂ p : ℕ} (hlt : n₁ < n₂) (hp : p.Prime) :
    (if ¬ 2 ∣ padicValNat p (P_ratio n₁ n₂) then (1 : ℝ) else 0) =
      (1 / 2 : ℝ) - (1 / 2 : ℝ) *
        ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) := by
  have hv := padicValNat_P_ratio_eq_sub hlt hp
  have hle : padicValNat p (Nat.factorial n₁) ≤ padicValNat p (Nat.factorial n₂) := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hmul := P_ratio_mul_factorial hlt
    have hP_pos : 0 < P_ratio n₁ n₂ := by
      by_contra h0; have : P_ratio n₁ n₂ = 0 := by omega
      rw [this, zero_mul] at hmul; exact (Nat.factorial_pos n₂).ne' hmul.symm
    have h := congrArg (padicValNat p) hmul
    rw [padicValNat.mul hP_pos.ne' (Nat.factorial_pos n₁).ne'] at h
    omega
  rw [hv]
  have hmod : (padicValNat p (Nat.factorial n₂) - padicValNat p (Nat.factorial n₁)) % 2 =
      (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂)) % 2 := by omega
  by_cases hdvd : 2 ∣ (padicValNat p (Nat.factorial n₂) - padicValNat p (Nat.factorial n₁))
  · have hev : Even (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂)) := by
      rw [Nat.even_iff]; omega
    rw [if_neg (not_not.mpr hdvd), hev.neg_one_pow]
    ring
  · have hodd : Odd (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂)) := by
      rw [Nat.odd_iff]; omega
    rw [if_pos hdvd, hodd.neg_one_pow]
    ring

private lemma val_factorial_le_two_div {n p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    (padicValNat p (Nat.factorial n) : ℝ) ≤ 2 * (n : ℝ) / (p : ℝ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : padicValNat p (Nat.factorial n) * (p - 1) ≤ n := by
    have := sub_one_mul_padicValNat_factorial n; linarith
  have h1r : (padicValNat p (Nat.factorial n) : ℝ) * ((p : ℝ) - 1) ≤ (n : ℝ) := by exact_mod_cast h1
  have hv : (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) :=
    (le_div_iff₀ (by exact_mod_cast (by omega : 0 < p - 1))).mpr h1r
  have hp_half : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3; linarith
  calc (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := hv
    _ ≤ (n : ℝ) / ((p : ℝ) / 2) := by gcongr
    _ = 2 * (n : ℝ) / (p : ℝ) := by ring

private lemma vaaler_btilde_dyadic_sum_bound
    (H : ℕ) (hH : 1 ≤ H) (b_tilde : ℤ → ℂ)
    (h_btilde0 : b_tilde 0 = (2 / ((H : ℝ) + 1) : ℂ))
    (h_btilde_b : ∀ h : ℤ, ‖b_tilde h‖ < 3 / ((H : ℝ) + 1))
    (n : ℕ) (hn : 3 ≤ n) (P : ℝ) (hP_pos : 0 < P) (I : Finset ℕ)
    (hI : ∀ p ∈ I, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P)
    (hExp : ∀ (h : ℤ), h ≠ 0 → |h| ≤ 2 * (H : ℤ) + 1 →
      ‖∑ p ∈ I, (Real.log (p : ℝ) : ℂ) * eExp ((h : ℝ) * (n : ℝ) / (2 * (p : ℝ)))‖ ≤
        C_exp * P * (Real.log (n : ℝ)) ^ (-((R_exp : ℝ) + 2)))
    (C_exp : ℝ) (hC_exp : 0 ≤ C_exp) (R_exp : ℕ) :
    ∑ p ∈ I, (Real.log (p : ℝ)) *
      (b_tilde 0 + ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
        b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re ≤
      (4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) +
        12 * C_exp * P * (Real.log (n : ℝ)) ^ (-((R_exp : ℝ) + 2)) := by
  have hI_card : (I.card : ℝ) ≤ 2 * P := by
    have hsub : I ⊆ Finset.Icc 1 (Nat.floor (2 * P)) := by
      intro p hp
      have hp_mem := hI p hp
      exact Finset.mem_Icc.mpr ⟨hp_mem.1.pos, Nat.le_floor hp_mem.2.2⟩
    have hcard : I.card ≤ Nat.floor (2 * P) := by
      calc I.card ≤ (Finset.Icc 1 (Nat.floor (2 * P))).card := Finset.card_le_card hsub
        _ = Nat.floor (2 * P) := by simp
    exact le_trans (by exact_mod_cast hcard) (Nat.floor_le (by positivity))
  have hsum_main : ∑ p ∈ I, Real.log (p : ℝ) * (b_tilde 0).re ≤
      (4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) := by
    rw [h_btilde0]
    simp only [Complex.ofReal_re]
    have hterm : ∀ p ∈ I, Real.log (p : ℝ) * (2 / ((H : ℝ) + 1)) ≤
        Real.log (2 * P) * (2 / ((H : ℝ) + 1)) := by
      intro p hp
      have hp_mem := hI p hp
      gcongr
      exact_mod_cast hp_mem.1.pos
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hlog2P : 0 ≤ Real.log (2 * P) := by
      by_cases h1 : 1 ≤ 2 * P
      · exact Real.log_nonneg h1
      · have hI_empty : I = ∅ := by
          ext p; simp only [Finset.not_mem_empty, iff_false]
          intro hp; have := (hI p hp).2.2; have : 2 ≤ p := (hI p hp).1.two_le
          linarith [show (2 : ℝ) ≤ p from by exact_mod_cast this]
        subst hI_empty; simp at hterm ⊢; linarith
    calc (I.card : ℝ) * (Real.log (2 * P) * (2 / ((H : ℝ) + 1)))
        ≤ (2 * P) * (Real.log (2 * P) * (2 / ((H : ℝ) + 1))) := by gcongr
      _ = (4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) := by ring
  let S_h := (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0)
  have hsum_err : ∑ p ∈ I, Real.log (p : ℝ) *
      (∑ h ∈ S_h, b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re ≤
      12 * C_exp * P * (Real.log (n : ℝ)) ^ (-((R_exp : ℝ) + 2)) := by
    have hre_eq : ∑ p ∈ I, Real.log (p : ℝ) *
        (∑ h ∈ S_h, b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re =
        (∑ h ∈ S_h, b_tilde h *
          ∑ p ∈ I, (Real.log (p : ℝ) : ℂ) * eExp ((h : ℝ) * (n : ℝ) / (2 * (p : ℝ)))).re := by
      rw [Complex.re_sum, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro p hp
      rw [Finset.mul_sum, Complex.re_sum]
      apply Finset.sum_congr rfl; intro h hh
      rw [← Complex.ofReal_re (Real.log (p : ℝ)), ← Complex.re_ofReal_mul]
      congr 1
      have hdiv : (h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2 = (h : ℝ) * (n : ℝ) / (2 * (p : ℝ)) := by ring
      rw [hdiv]; ring
    rw [hre_eq]
    calc (∑ h ∈ S_h, b_tilde h * _).re
        ≤ ‖∑ h ∈ S_h, b_tilde h * _‖ := Complex.abs_re_le_norm _ |>.trans' (le_abs_self _)
      _ ≤ ∑ h ∈ S_h, ‖b_tilde h * _‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ S_h, (3 / ((H : ℝ) + 1)) * (C_exp * P * (Real.log (n : ℝ)) ^ (-((R_exp : ℝ) + 2))) := by
          apply Finset.sum_le_sum; intro h hh
          rw [norm_mul]
          have hmem := Finset.mem_filter.mp hh
          have habs : |h| ≤ 2 * (H : ℤ) + 1 := by
            have := Finset.mem_Icc.mp hmem.1
            exact abs_le.mpr ⟨this.1, this.2⟩
          exact mul_le_mul (h_btilde_b h).le (hExp h hmem.2 habs) (norm_nonneg _) (by positivity)
      _ = (S_h.card : ℝ) * ((3 / ((H : ℝ) + 1)) * (C_exp * P * (Real.log (n : ℝ)) ^ (-((R_exp : ℝ) + 2)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 * ((H : ℝ) + 1)) * ((3 / ((H : ℝ) + 1)) * (C_exp * P * (Real.log (n : ℝ)) ^ (-((R_exp : ℝ) + 2)))) := by
          have hcard_le : (S_h.card : ℝ) ≤ 4 * ((H : ℝ) + 1) := by
            have h1 : S_h.card ≤ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).card :=
              Finset.card_filter_le _ _
            have h2 : (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).card = 4 * H + 3 := by
              rw [Int.card_Icc]; omega
            have h1r : (S_h.card : ℝ) ≤ 4 * (H : ℝ) + 3 := by exact_mod_cast le_trans h1 h2.le
            linarith
          gcongr
      _ = 12 * C_exp * P * (Real.log (n : ℝ)) ^ (-((R_exp : ℝ) + 2)) := by
          have hH0 : (H : ℝ) + 1 ≠ 0 := by positivity
          field_simp [hH0]; ring
  have hsplit : ∑ p ∈ I, Real.log (p : ℝ) *
      (b_tilde 0 + ∑ h ∈ S_h, b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re =
      (∑ p ∈ I, Real.log (p : ℝ) * (b_tilde 0).re) +
      (∑ p ∈ I, Real.log (p : ℝ) * (∑ h ∈ S_h, b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro p _
    rw [Complex.add_re]; ring
  rw [hsplit]
  exact add_le_add hsum_main hsum_err

/-- **Lemma 6.3 (Uniform Parity-Flip Weight Asymptotic, eq. 6.7)**:
For any `δ ∈ (0, 1/4]` and any `ε > 0`, there exists `N₀` such that for all `n₁ ≥ N₀` and
`n₂ > n₁` with `h := n₂ - n₁ < n₁`:
- if `(h : ℝ) ≤ (n₁ : ℝ) ^ δ`, then `parityFlipWeight n₁ n₂ ≤ (δ + ε) * n₁ * log n₁`;
- if `(n₁ : ℝ) ^ δ < (h : ℝ)`, then `|parityFlipWeight n₁ n₂ - (1/2) * n₁ * log h| ≤ (δ + ε) * n₁ * log n₁`. -/
theorem lem_6_3_parity_flip_uniform (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1000 ≤ N₀ ∧ ∀ n₁ n₂ : ℕ, N₀ ≤ n₁ → n₁ < n₂ → n₂ - n₁ < n₁ →
      let h := n₂ - n₁
      ((h : ℝ) ≤ (n₁ : ℝ) ^ δ →
        parityFlipWeight n₁ n₂ ≤ (δ + ε) * (n₁ : ℝ) * Real.log (n₁ : ℝ)) ∧
      ((n₁ : ℝ) ^ δ < (h : ℝ) →
        |parityFlipWeight n₁ n₂ - (1 / 2 : ℝ) * (n₁ : ℝ) * Real.log (h : ℝ)| ≤
          (δ + ε) * (n₁ : ℝ) * Real.log (n₁ : ℝ)) := by
  obtain ⟨_, _, _, _, C₁, C₂, _, _, hC₂, _, hExpBound⟩ := prime_exp_sum_bounds δ hδ0 (by linarith)
  obtain ⟨N_exp, hN_exp⟩ := Filter.eventually_atTop.mp hExpBound
  obtain ⟨C_mert, hC_mert_pos, hMert⟩ := Mertens_div_p_band_le
  let R := Nat.floor (1 / δ)
  let A_R := 6 * R + 30
  have hR_ge4 : 4 ≤ R := Nat.le_floor (by rw [Nat.cast_ofNat, le_div_iff₀ hδ0]; linarith)
  have hR1_gt : 1 < ((R : ℝ) + 1) * δ := by
    have hlt := Nat.lt_floor_add_one (1 / δ)
    change 1 / δ < (R : ℝ) + 1 at hlt
    exact (div_lt_iff₀ hδ0).mp hlt
  have hloglog_div : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => Real.log t / t) Filter.atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 1 0 (by norm_num)
    exact h1.comp Real.tendsto_log_atTop
  have hinv_log : Filter.Tendsto (fun x : ℝ => 1 / Real.log x) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h_err1 : Filter.Tendsto
      (fun n : ℕ => ((A_R : ℝ) + 4) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      Filter.atTop (nhds 0) := by
    have := (hloglog_div.const_mul ((A_R : ℝ) + 4)).comp tendsto_natCast_atTop_atTop
    simpa [mul_div_assoc] using this
  have h_err2 : Filter.Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) Filter.atTop (nhds 0) :=
    hinv_log.comp tendsto_natCast_atTop_atTop
  have h_err3 : Filter.Tendsto
      (fun n : ℕ => (Real.log (Real.log (n : ℝ))) ^ 2 / Real.log (n : ℝ))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => (Real.log t) ^ 2 / t) Filter.atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 2 0 (by norm_num)
    exact (h1.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (h_err1.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / 100 by positivity)))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    (h_err2.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / (100 * (C_mert + C₂ + 10)) by positivity)))
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp
    (h_err3.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / (1000 * (C₂ + 1) * (δ ^ (-(R : ℤ) - 2) + 1)) by positivity)))
  have hpow_gt : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (((R : ℝ) + 1) * δ - 1)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by linarith) |>.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₄, hN₄⟩ := Filter.eventually_atTop.mp (hpow_gt.eventually (Filter.eventually_gt_atTop 4))
  obtain ⟨N₅, hN₅⟩ := Filter.eventually_atTop.mp
    (h_err2.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < δ / 20 by positivity)))
  obtain ⟨N₆, hN₆⟩ := Filter.eventually_atTop.mp
    ((log_pow_div_rpow_tendsto_zero 2 hδ0).eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨C_mert1, hC_mert1_pos, hMert1⟩ := mertens_first_theorem
  obtain ⟨N₇, hN₇⟩ := Filter.eventually_atTop.mp
    (h_err2.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / (100 * (C_mert1 + C_mert + C₂ + 10)) by positivity)))
  obtain ⟨N_exp_d, hN_exp_d⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hδ0 |>.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (max (N_exp : ℝ) 100)))
  let C_osc_const : ℝ := 1000 * (((R : ℝ) + 4) ^ 2 + 1) * (C₂ + 1) * ((δ / 2) ^ (-(R : ℤ) - 2) + 1)
  have h_err_osc : Filter.Tendsto
      (fun n : ℕ => C_osc_const * (Real.log (Real.log (n : ℝ)) + 1) ^ 2 / (Real.log (n : ℝ)) ^ 2)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => (Real.log t + 1) ^ 2 / t ^ 2) Filter.atTop (nhds 0) := by
      have ht : Filter.Tendsto (fun t : ℝ => (Real.log t + 1) / t) Filter.atTop (nhds 0) := by
        have ha : Filter.Tendsto (fun t : ℝ => Real.log t / t) Filter.atTop (nhds 0) := by
          simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 1 0 (by norm_num)
        have hb : Filter.Tendsto (fun t : ℝ => 1 / t) Filter.atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop Filter.tendsto_id
        simpa [add_div] using ha.add hb
      simpa [div_pow] using ht.pow 2
    have h2 := (h1.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
    simpa [mul_div_assoc] using h2.const_mul C_osc_const
  obtain ⟨N_osc_fin, hN_osc_fin⟩ := Filter.eventually_atTop.mp
    (h_err_osc.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / 100 by positivity)))
  let N₀ := max (max (max N_exp N₁) (max N₂ N₃)) (max (max N₄ N₅) (max N₆ (max N₇ (max N_exp_d (max N_osc_fin 1000)))))
  refine ⟨N₀, by omega, ?_⟩
  intro n₁ n₂ hn₁ hlt h_lt_n₁
  set h := n₂ - n₁
  have hn₁_pos : (0 : ℝ) < n₁ := by positivity
  have hlog_n₁_pos : 0 < Real.log (n₁ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n₁))
  let y₂ : ℝ := (h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2 + 2
  have hy₂_ge2 : 2 ≤ y₂ := by dsimp [y₂]; positivity
  have h_upper_bound : ∀ (S : Finset ℕ),
      (∀ p ∈ S, p.Prime ∧ 3 ≤ p ∧ p ≤ n₁ ∧ y₂ ≤ (p : ℝ) ∧ ¬ 2 ∣ padicValNat p (P_ratio n₁ n₂)) →
      ∑ p ∈ S, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
        2 * (n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2 := by
    intro S hS
    have hterm : ∀ p ∈ S, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
        (2 * (n₁ : ℝ) / ((h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2)) * Real.log (p : ℝ) := by
      intro p hp
      have hpS := hS p hp
      have hv := val_factorial_le_two_div (n := n₁) hpS.1 hpS.2.1
      have hpy : (h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2 ≤ (p : ℝ) := by linarith [hpS.2.2.2.1]
      have hh_pos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
      have hv2 : (padicValNat p (Nat.factorial n₁) : ℝ) ≤
          2 * (n₁ : ℝ) / ((h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2) :=
        le_trans hv (div_le_div_of_nonneg_left (by positivity) (by positivity) hpy)
      gcongr
      exact Real.log_nonneg (by exact_mod_cast hpS.1.pos)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hdvd_P : ∏ p ∈ S, p ∣ P_ratio n₁ n₂ := by
      apply Finset.prod_primes_dvd
      · intro p hp
        have hpS := hS p hp
        have hv_pos : 0 < padicValNat p (P_ratio n₁ n₂) := by
          by_contra h0; have : padicValNat p (P_ratio n₁ n₂) = 0 := by omega
          apply hpS.2.2.2.2; rw [this]; exact dvd_zero 2
        haveI : Fact p.Prime := ⟨hpS.1⟩
        have hP_pos : 0 < P_ratio n₁ n₂ := by
          have hmul := P_ratio_mul_factorial hlt
          by_contra h0; have : P_ratio n₁ n₂ = 0 := by omega
          rw [this, zero_mul] at hmul; exact (Nat.factorial_pos n₂).ne' hmul.symm
        exact dvd_of_padicValNat_pos hP_pos.ne' hv_pos
      · intro p hp q hq hpq
        exact (Nat.coprime_primes (hS p hp).1 (hS q hq).1).mpr hpq
    have hP_le : (P_ratio n₁ n₂ : ℝ) ≤ (2 * (n₁ : ℝ)) ^ h := by
      have hprod_eq : P_ratio n₁ n₂ = ∏ j ∈ Finset.Ioc n₁ n₂, j := by
        have hfac := P_ratio_mul_factorial hlt
        have hprod : Nat.factorial n₂ = Nat.factorial n₁ * ∏ j ∈ Finset.Ioc n₁ n₂, j := by
          have hle : n₁ ≤ n₂ := le_of_lt hlt
          induction n₂, hle using Nat.le_induction with
          | base => simp
          | succ k hk ih => rw [Nat.factorial_succ, Finset.prod_Ioc_succ_top hk, ih]; ring
        have : P_ratio n₁ n₂ * Nat.factorial n₁ = (∏ j ∈ Finset.Ioc n₁ n₂, j) * Nat.factorial n₁ := by
          rw [hfac, hprod]; ring
        exact mul_right_cancel₀ (Nat.factorial_pos n₁).ne' this
      rw [hprod_eq]
      have hle_nat : ∏ j ∈ Finset.Ioc n₁ n₂, j ≤ (2 * n₁) ^ h := by
        calc ∏ j ∈ Finset.Ioc n₁ n₂, j
            ≤ ∏ _j ∈ Finset.Ioc n₁ n₂, (2 * n₁) := Finset.prod_le_prod' (fun j hj => by
              have := (Finset.mem_Ioc.mp hj).2; omega)
          _ = (2 * n₁) ^ (Finset.Ioc n₁ n₂).card := Finset.prod_const _
          _ = (2 * n₁) ^ h := by rw [Nat.card_Ioc]; rfl
      exact_mod_cast hle_nat
    have hpos_prod : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hS p hp).1.pos)
    have hP_pos : 0 < P_ratio n₁ n₂ := by
      have hmul := P_ratio_mul_factorial hlt
      by_contra h0; have : P_ratio n₁ n₂ = 0 := by omega
      rw [this, zero_mul] at hmul; exact (Nat.factorial_pos n₂).ne' hmul.symm
    have hlog_sum_le : ∑ p ∈ S, Real.log (p : ℝ) ≤ (h : ℝ) * Real.log (2 * (n₁ : ℝ)) := by
      have h1 : (∏ p ∈ S, p : ℝ) ≤ (P_ratio n₁ n₂ : ℝ) := by
        exact_mod_cast Nat.le_of_dvd hP_pos hdvd_P
      have h2 := Real.log_le_log (by exact_mod_cast hpos_prod) (le_trans h1 hP_le)
      rw [Nat.cast_prod, Real.log_prod _ _ (fun p hp => by exact_mod_cast (hS p hp).1.ne_zero),
        Real.log_pow] at h2
      exact h2
    calc (2 * (n₁ : ℝ) / ((h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2)) * ∑ p ∈ S, Real.log (p : ℝ)
        ≤ (2 * (n₁ : ℝ) / ((h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2)) * ((h : ℝ) * Real.log (2 * (n₁ : ℝ))) := by
          gcongr
      _ = 2 * (n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2 := by
          have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
          field_simp [hh0]
  have h_tiny_bound : ∀ (B : ℝ), 3 ≤ B →
      ∑ p ∈ (Finset.Icc 3 (Nat.floor B)).filter Nat.Prime,
        (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
      2 * (n₁ : ℝ) * (Real.log B + C_mert + 1) := by
    intro B hB
    have hterm : ∀ p ∈ (Finset.Icc 3 (Nat.floor B)).filter Nat.Prime,
        (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
        2 * (n₁ : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by
      intro p hp
      have hp_mem := Finset.mem_filter.mp hp
      have hp3 : 3 ≤ p := (Finset.mem_Icc.mp hp_mem.1).1
      have hv := val_factorial_le_two_div (n := n₁) hp_mem.2 hp3
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
      calc (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)
          ≤ (2 * (n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ) := by gcongr
        _ = 2 * (n₁ : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    gcongr
    have hsub : (Finset.Icc 3 (Nat.floor B)).filter Nat.Prime ⊆
        {3} ∪ ((Finset.Icc 3 (Nat.floor B)).filter Nat.Prime).filter (fun p : ℕ => (3 : ℝ) < (p : ℝ)) := by
      intro p hp
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      by_cases hp3 : p = 3
      · exact Or.inl hp3
      · exact Or.inr ⟨hp, by exact_mod_cast (by omega : 3 < p)⟩
    have hmert := hMert 3 B (le_refl 3) hB
    have h3_val : Real.log (3 : ℝ) / (3 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
    calc ∑ p ∈ (Finset.Icc 3 (Nat.floor B)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
        ≤ ∑ p ∈ ({3} ∪ ((Finset.Icc 3 (Nat.floor B)).filter Nat.Prime).filter
            (fun p : ℕ => (3 : ℝ) < (p : ℝ))), Real.log (p : ℝ) / (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ (Real.log (3 : ℝ) / (3 : ℝ)) + (Real.log (B / 3) + C_mert) := by
          rw [Finset.sum_union]; · simp only [Finset.sum_singleton]; linarith
          · rw [Finset.disjoint_singleton_left]; simp
      _ ≤ 1 + (Real.log B + C_mert) := by
          have : Real.log (B / 3) ≤ Real.log B := Real.log_le_log (by positivity) (by linarith)
          linarith
      _ = Real.log B + C_mert + 1 := by ring
  have h_band_exact : ∀ (A B : ℝ), (Real.log (n₁ : ℝ)) ^ 2 ≤ A → A ≤ B →
      ∑ p ∈ ((Finset.Icc 3 (Nat.floor B)).filter Nat.Prime).filter (fun p : ℕ => A < (p : ℝ)),
        (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
      (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) * (Real.log (B / A) + C_mert) := by
    intro A B hA_lb hAB
    have hlog2_ge : 3 ≤ (Real.log (n₁ : ℝ)) ^ 2 := by
      have : (1000 : ℝ) ≤ n₁ := by exact_mod_cast (by omega : 1000 ≤ n₁)
      have he2 : Real.exp 2 < 1000 := by
        have := Real.exp_one_lt_d9
        calc Real.exp 2 = Real.exp (1 + 1) := by norm_num
          _ = Real.exp 1 * Real.exp 1 := by rw [Real.exp_add]
          _ < 2.72 * 2.72 := by gcongr <;> linarith
          _ < 1000 := by norm_num
      have h2_le : 2 ≤ Real.log (n₁ : ℝ) := (Real.le_log_iff_exp_le (by positivity)).mpr (le_trans he2.le this)
      nlinarith
    have hterm : ∀ p ∈ ((Finset.Icc 3 (Nat.floor B)).filter Nat.Prime).filter (fun p : ℕ => A < (p : ℝ)),
        (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
        (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by
      intro p hp
      have hp_mem := Finset.mem_filter.mp hp
      have hp_mem1 := Finset.mem_filter.mp hp_mem.1
      have hp_pr := hp_mem1.2
      have hp_A : A < (p : ℝ) := hp_mem.2
      have hp_log2 : (Real.log (n₁ : ℝ)) ^ 2 < (p : ℝ) := lt_of_le_of_lt hA_lb hp_A
      haveI : Fact p.Prime := ⟨hp_pr⟩
      have h1 : (padicValNat p (Nat.factorial n₁) : ℝ) * ((p : ℝ) - 1) ≤ (n₁ : ℝ) := by
        have := sub_one_mul_padicValNat_factorial n₁
        exact_mod_cast (show padicValNat p (Nat.factorial n₁) * (p - 1) ≤ n₁ by linarith)
      have hp1_pos : 0 < (p : ℝ) - 1 := by linarith
      have hv : (padicValNat p (Nat.factorial n₁) : ℝ) ≤ (n₁ : ℝ) / ((p : ℝ) - 1) :=
        (le_div_iff₀ hp1_pos).mpr h1
      have hinv : 1 / ((p : ℝ) - 1) ≤ (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) / (p : ℝ) := by
        rw [div_le_div_iff₀ hp1_pos (by linarith)]
        have hp_pos : 0 < (p : ℝ) := by linarith
        have hsq_pos : 0 < (Real.log (n₁ : ℝ)) ^ 2 := by linarith
        rw [one_mul, add_mul, one_mul, div_mul_eq_mul_div, mul_sub, mul_one]
        have h1_le : 1 ≤ (2 * (p : ℝ) - 2) / (Real.log (n₁ : ℝ)) ^ 2 :=
          (le_div_iff₀ hsq_pos).mpr (by linarith)
        linarith
      have hv2 : (padicValNat p (Nat.factorial n₁) : ℝ) ≤
          (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) / (p : ℝ) := by
        calc (padicValNat p (Nat.factorial n₁) : ℝ)
            ≤ (n₁ : ℝ) * (1 / ((p : ℝ) - 1)) := by rw [mul_one_div]; exact hv
          _ ≤ (n₁ : ℝ) * ((1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) / (p : ℝ)) := by gcongr
          _ = (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) / (p : ℝ) := by ring
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
      calc (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)
          ≤ ((1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ) := by gcongr
        _ = (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    gcongr
    exact hMert A B (le_trans hlog2_ge hA_lb) hAB
  have hlog_ge3 : 3 ≤ (Real.log (n₁ : ℝ)) ^ 2 := by
    have : (1000 : ℝ) ≤ n₁ := by exact_mod_cast (by omega : 1000 ≤ n₁)
    have he2 : Real.exp 2 < 1000 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 2 = Real.exp (1 + 1) := by norm_num
        _ = Real.exp 1 * Real.exp 1 := by rw [Real.exp_add]
        _ < 2.72 * 2.72 := by gcongr <;> linarith
        _ < 1000 := by norm_num
    have h2_le : 2 ≤ Real.log (n₁ : ℝ) := (Real.le_log_iff_exp_le (by positivity)).mpr (le_trans he2.le this)
    nlinarith
  have h_branch1 : (h : ℝ) ≤ (n₁ : ℝ) ^ δ →
      parityFlipWeight n₁ n₂ ≤ (δ + ε) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
    intro hh_le
    unfold parityFlipWeight
    let S_all := (Finset.Icc 3 n₁).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (P_ratio n₁ n₂))
    let S_le := S_all.filter (fun p : ℕ => (p : ℝ) ≤ y₂)
    let S_gt := S_all.filter (fun p : ℕ => y₂ < (p : ℝ))
    have hsplit : S_all = S_le ∪ S_gt := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter, S_le, S_gt]; constructor
      · intro hp; by_cases hle : (p : ℝ) ≤ y₂; exact Or.inl ⟨hp, hle⟩; exact Or.inr ⟨hp, lt_of_not_ge hle⟩
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    have hdisj : Disjoint S_le S_gt := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      simp only [Finset.mem_filter, S_le, S_gt] at hp1 hp2; linarith
    rw [hsplit, Finset.sum_union hdisj]
    have hS_gt_ub : ∑ p ∈ S_gt, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
        2 * (n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2 := by
      apply h_upper_bound S_gt
      intro p hp
      simp only [S_gt, S_all, Finset.mem_filter, Finset.mem_Icc] at hp
      exact ⟨hp.1.2.1, hp.1.1.1, hp.1.1.2, hp.2.le, hp.1.2.2⟩
    let S_le1 := S_le.filter (fun p : ℕ => (p : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ 2)
    let S_le2 := S_le.filter (fun p : ℕ => (Real.log (n₁ : ℝ)) ^ 2 < (p : ℝ))
    have hsplit2 : S_le = S_le1 ∪ S_le2 := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter, S_le1, S_le2]; constructor
      · intro hp; by_cases hle : (p : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ 2
        exact Or.inl ⟨hp, hle⟩; exact Or.inr ⟨hp, lt_of_not_ge hle⟩
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    have hdisj2 : Disjoint S_le1 S_le2 := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      simp only [Finset.mem_filter, S_le1, S_le2] at hp1 hp2; linarith
    have hS_le1_ub : ∑ p ∈ S_le1, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
        2 * (n₁ : ℝ) * (Real.log ((Real.log (n₁ : ℝ)) ^ 2) + C_mert + 1) := by
      have hsub : S_le1 ⊆ (Finset.Icc 3 (Nat.floor ((Real.log (n₁ : ℝ)) ^ 2))).filter Nat.Prime := by
        intro p hp
        simp only [S_le1, S_le, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        exact ⟨⟨hp.1.1.1.1, Nat.le_floor hp.2⟩, hp.1.1.2.1⟩
      exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
        (h_tiny_bound ((Real.log (n₁ : ℝ)) ^ 2) hlog_ge3)
    have hS_le2_ub : ∑ p ∈ S_le2, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
        (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) *
          (δ * Real.log (n₁ : ℝ) + Real.log (3 : ℝ) + C_mert) := by
      by_cases hy_le : (Real.log (n₁ : ℝ)) ^ 2 ≤ y₂
      · have hsub : S_le2 ⊆ ((Finset.Icc 3 (Nat.floor y₂)).filter Nat.Prime).filter
            (fun p : ℕ => (Real.log (n₁ : ℝ)) ^ 2 < (p : ℝ)) := by
          intro p hp
          simp only [S_le2, S_le, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨⟨⟨hp.1.1.1.1, Nat.le_floor hp.1.2⟩, hp.1.1.2.1⟩, hp.2⟩
        have h1 := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
          (h_band_exact ((Real.log (n₁ : ℝ)) ^ 2) y₂ (le_refl _) hy_le)
        have hy2_le : y₂ ≤ 3 * (n₁ : ℝ) ^ δ * (Real.log (n₁ : ℝ)) ^ 2 := by
          dsimp [y₂]
          have h1n : (1 : ℝ) ≤ (n₁ : ℝ) ^ δ := Real.one_le_rpow (by linarith) hδ0.le
          nlinarith
        have hlog_div : Real.log (y₂ / (Real.log (n₁ : ℝ)) ^ 2) ≤
            δ * Real.log (n₁ : ℝ) + Real.log (3 : ℝ) := by
          have hdiv_le : y₂ / (Real.log (n₁ : ℝ)) ^ 2 ≤ 3 * (n₁ : ℝ) ^ δ := by
            rw [div_le_iff₀ (by positivity)]; exact hy2_le
          have h2 := Real.log_le_log (by positivity) hdiv_le
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hn₁_pos] at h2
          linarith
        have hfac_nn : 0 ≤ (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) := by positivity
        exact le_trans h1 (mul_le_mul_of_nonneg_left (by linarith) hfac_nn)
      · have hS_le2_empty : S_le2 = ∅ := by
          ext p; simp only [Finset.not_mem_empty, iff_false]
          intro hp; simp only [S_le2, S_le, Finset.mem_filter] at hp; linarith
        rw [hS_le2_empty, Finset.sum_empty]
        have : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
        positivity
    have hS_le_eq : ∑ p ∈ S_le, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) =
        (∑ p ∈ S_le1, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) +
        (∑ p ∈ S_le2, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) := by
      rw [hsplit2, Finset.sum_union hdisj2]
    rw [hS_le_eq]
    have herr_ball1 : ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) < ε / 100 := by
      have := hN₁ n₁ (by omega)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
        have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith)
        positivity)] at this
      exact this
    have herr_ball2 : 1 / Real.log (n₁ : ℝ) < ε / (100 * (C_mert + C₂ + 10)) := by
      have := hN₂ n₁ (by omega)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
      exact this
    have hlog_n₁_pos' : 0 < Real.log (n₁ : ℝ) := hlog_n₁_pos
    have h_gt_small : 2 * (n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2 ≤
        (ε / 10) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      have hlog2n : Real.log (2 * (n₁ : ℝ)) ≤ 2 * Real.log (n₁ : ℝ) := by
        rw [Real.log_mul (by norm_num) hn₁_pos.ne']
        have : Real.log 2 ≤ Real.log (n₁ : ℝ) := Real.log_le_log (by norm_num) (by linarith)
        linarith
      have h1 : 1 / Real.log (n₁ : ℝ) ≤ ε / 40 := by
        have : ε / (100 * (C_mert + C₂ + 10)) ≤ ε / 40 := by
          gcongr; linarith
        linarith
      calc 2 * (n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2
          ≤ 2 * (n₁ : ℝ) * (2 * Real.log (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2 := by gcongr
        _ = 4 * (n₁ : ℝ) / Real.log (n₁ : ℝ) := by field_simp [hlog_n₁_pos'.ne']
        _ = 4 * (1 / Real.log (n₁ : ℝ)) * (n₁ : ℝ) := by ring
        _ ≤ 4 * (ε / 40) * (n₁ : ℝ) := by gcongr
        _ = (ε / 10) * (n₁ : ℝ) := by ring
        _ ≤ (ε / 10) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
            have : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
            nlinarith [show 0 ≤ (ε / 10) * (n₁ : ℝ) by positivity]
    have h_le1_small : 2 * (n₁ : ℝ) * (Real.log ((Real.log (n₁ : ℝ)) ^ 2) + C_mert + 1) ≤
        (ε / 10) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      rw [Real.log_pow, Nat.cast_ofNat]
      have hloglog_le : Real.log (Real.log (n₁ : ℝ)) ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
        have h1 : Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) ≤
            ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) := by
          gcongr
          have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith)
          positivity
          have : (4 : ℝ) ≤ A_R := by exact_mod_cast (by omega : 4 ≤ A_R)
          linarith
        have h2 := (div_lt_iff₀ hlog_n₁_pos').mp (lt_of_le_of_lt h1 herr_ball1)
        linarith
      have hCm_le : C_mert + 1 ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
        have h1 : (C_mert + 1) / Real.log (n₁ : ℝ) ≤ ε / 100 := by
          have := (mul_lt_mul_of_pos_left herr_ball2 (by positivity : 0 < C_mert + 1))
          calc (C_mert + 1) / Real.log (n₁ : ℝ)
              = (C_mert + 1) * (1 / Real.log (n₁ : ℝ)) := by ring
            _ ≤ (C_mert + 1) * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
            _ ≤ ε / 100 := by
                rw [div_eq_mul_inv, mul_comm (C_mert + 1), ← mul_assoc]
                have : (C_mert + 1) / (100 * (C_mert + C₂ + 10)) ≤ 1 / 100 := by
                  rw [div_le_div_iff₀ (by positivity) (by positivity)]
                  nlinarith
                calc ε * (100 * (C_mert + C₂ + 10))⁻¹ * (C_mert + 1)
                    = ε * ((C_mert + 1) / (100 * (C_mert + C₂ + 10))) := by ring
                  _ ≤ ε * (1 / 100) := by gcongr
                  _ = ε / 100 := by ring
        exact (div_le_iff₀ hlog_n₁_pos').mp h1
      nlinarith [show (0 : ℝ) ≤ n₁ by positivity]
    have h_le2_small : (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) *
        (δ * Real.log (n₁ : ℝ) + Real.log (3 : ℝ) + C_mert) ≤
        (δ + ε / 2) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      have h2_div : 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ ε / 20 := by
        have h1 : 1 / Real.log (n₁ : ℝ) ≤ ε / 1000 := by
          have : ε / (100 * (C_mert + C₂ + 10)) ≤ ε / 1000 := by gcongr; linarith
          linarith
        have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
        calc 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ 2 / Real.log (n₁ : ℝ) := by
              gcongr; nlinarith
          _ = 2 * (1 / Real.log (n₁ : ℝ)) := by ring
          _ ≤ 2 * (ε / 1000) := by gcongr
          _ ≤ ε / 20 := by linarith
      have hlog3_Cm : Real.log (3 : ℝ) + C_mert ≤ (ε / 10) * Real.log (n₁ : ℝ) := by
        have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
        have h1 : (C_mert + 2) / Real.log (n₁ : ℝ) ≤ ε / 10 := by
          calc (C_mert + 2) / Real.log (n₁ : ℝ)
              = (C_mert + 2) * (1 / Real.log (n₁ : ℝ)) := by ring
            _ ≤ (C_mert + 2) * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
            _ ≤ ε / 10 := by
                have : (C_mert + 2) / (100 * (C_mert + C₂ + 10)) ≤ 1 / 10 := by
                  rw [div_le_div_iff₀ (by positivity) (by positivity)]
                  nlinarith
                calc (C_mert + 2) * (ε / (100 * (C_mert + C₂ + 10)))
                    = ε * ((C_mert + 2) / (100 * (C_mert + C₂ + 10))) := by ring
                  _ ≤ ε * (1 / 10) := by gcongr
                  _ = ε / 10 := by ring
        have h2 := (div_le_iff₀ hlog_n₁_pos').mp h1
        linarith
      have ha_le1 : 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have h_lin : (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) *
          (δ * Real.log (n₁ : ℝ) + Real.log (3 : ℝ) + C_mert) ≤
          (δ + ε / 2) * Real.log (n₁ : ℝ) := by
        calc (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) *
              (δ * Real.log (n₁ : ℝ) + Real.log (3 : ℝ) + C_mert)
            ≤ (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * ((δ + ε / 10) * Real.log (n₁ : ℝ)) := by
              gcongr; linarith
          _ = (δ + (2 / (Real.log (n₁ : ℝ)) ^ 2) * δ +
                (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (ε / 10)) * Real.log (n₁ : ℝ) := by ring
          _ ≤ (δ + (ε / 20) * (1 / 4) + 2 * (ε / 10)) * Real.log (n₁ : ℝ) := by
              gcongr; nlinarith
          _ ≤ (δ + ε / 2) * Real.log (n₁ : ℝ) := by gcongr; linarith
      calc (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) *
            (δ * Real.log (n₁ : ℝ) + Real.log (3 : ℝ) + C_mert)
          = (n₁ : ℝ) * ((1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) *
              (δ * Real.log (n₁ : ℝ) + Real.log (3 : ℝ) + C_mert)) := by ring
        _ ≤ (n₁ : ℝ) * ((δ + ε / 2) * Real.log (n₁ : ℝ)) := by gcongr
        _ = (δ + ε / 2) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
    linarith
  have h_branch2 : (n₁ : ℝ) ^ δ < (h : ℝ) →
      |parityFlipWeight n₁ n₂ - (1 / 2 : ℝ) * (n₁ : ℝ) * Real.log (h : ℝ)| ≤
        (δ + ε) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
    intro hh_gt
    by_cases hh_small : (h : ℝ) ≤ (n₁ : ℝ) ^ δ * (Real.log (n₁ : ℝ)) ^ (A_R + 2)
    · have hy₂_le : y₂ ≤ 3 * (n₁ : ℝ) ^ δ * (Real.log (n₁ : ℝ)) ^ (A_R + 4) := by
        dsimp [y₂]
        have h1n : (1 : ℝ) ≤ (n₁ : ℝ) ^ δ := Real.one_le_rpow (by linarith) hδ0.le
        have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
        have hpow_le : (Real.log (n₁ : ℝ)) ^ (A_R + 2) * (Real.log (n₁ : ℝ)) ^ 2 =
            (Real.log (n₁ : ℝ)) ^ (A_R + 4) := by ring
        have h1pow : 1 ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 4) := one_le_pow₀ hlog1
        nlinarith
      have hpf_ub : parityFlipWeight n₁ n₂ ≤ (δ + ε / 2) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        unfold parityFlipWeight
        let S_all := (Finset.Icc 3 n₁).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (P_ratio n₁ n₂))
        let S_le := S_all.filter (fun p : ℕ => (p : ℝ) ≤ y₂)
        let S_gt := S_all.filter (fun p : ℕ => y₂ < (p : ℝ))
        have hsplit : S_all = S_le ∪ S_gt := by
          ext p; simp only [Finset.mem_union, Finset.mem_filter, S_le, S_gt]; constructor
          · intro hp; by_cases hle : (p : ℝ) ≤ y₂; exact Or.inl ⟨hp, hle⟩; exact Or.inr ⟨hp, lt_of_not_ge hle⟩
          · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
        have hdisj : Disjoint S_le S_gt := by
          rw [Finset.disjoint_left]; intro p hp1 hp2
          simp only [Finset.mem_filter, S_le, S_gt] at hp1 hp2; linarith
        rw [hsplit, Finset.sum_union hdisj]
        have hS_gt_ub : ∑ p ∈ S_gt, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
            2 * (n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2 := by
          apply h_upper_bound S_gt
          intro p hp; simp only [S_gt, S_all, Finset.mem_filter, Finset.mem_Icc] at hp
          exact ⟨hp.1.2.1, hp.1.1.1, hp.1.1.2, hp.2.le, hp.1.2.2⟩
        let S_le1 := S_le.filter (fun p : ℕ => (p : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ 2)
        let S_le2 := S_le.filter (fun p : ℕ => (Real.log (n₁ : ℝ)) ^ 2 < (p : ℝ))
        have hsplit2 : S_le = S_le1 ∪ S_le2 := by
          ext p; simp only [Finset.mem_union, Finset.mem_filter, S_le1, S_le2]; constructor
          · intro hp; by_cases hle : (p : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ 2
            exact Or.inl ⟨hp, hle⟩; exact Or.inr ⟨hp, lt_of_not_ge hle⟩
          · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
        have hdisj2 : Disjoint S_le1 S_le2 := by
          rw [Finset.disjoint_left]; intro p hp1 hp2
          simp only [Finset.mem_filter, S_le1, S_le2] at hp1 hp2; linarith
        have hS_le1_ub : ∑ p ∈ S_le1, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
            2 * (n₁ : ℝ) * (Real.log ((Real.log (n₁ : ℝ)) ^ 2) + C_mert + 1) := by
          have hsub : S_le1 ⊆ (Finset.Icc 3 (Nat.floor ((Real.log (n₁ : ℝ)) ^ 2))).filter Nat.Prime := by
            intro p hp; simp only [S_le1, S_le, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
            exact ⟨⟨hp.1.1.1.1, Nat.le_floor hp.2⟩, hp.1.1.2.1⟩
          exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
            (h_tiny_bound ((Real.log (n₁ : ℝ)) ^ 2) hlog_ge3)
        have hS_le2_ub : ∑ p ∈ S_le2, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
            (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) *
              (δ * Real.log (n₁ : ℝ) + ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) + Real.log 3 + C_mert) := by
          by_cases hy_le : (Real.log (n₁ : ℝ)) ^ 2 ≤ y₂
          · have hsub : S_le2 ⊆ ((Finset.Icc 3 (Nat.floor y₂)).filter Nat.Prime).filter
                (fun p : ℕ => (Real.log (n₁ : ℝ)) ^ 2 < (p : ℝ)) := by
              intro p hp; simp only [S_le2, S_le, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
              exact ⟨⟨⟨hp.1.1.1.1, Nat.le_floor hp.1.2⟩, hp.1.1.2.1⟩, hp.2⟩
            have h1 := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
              (h_band_exact ((Real.log (n₁ : ℝ)) ^ 2) y₂ (le_refl _) hy_le)
            have hlog_div : Real.log (y₂ / (Real.log (n₁ : ℝ)) ^ 2) ≤
                δ * Real.log (n₁ : ℝ) + ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) + Real.log 3 := by
              have hdiv_le : y₂ / (Real.log (n₁ : ℝ)) ^ 2 ≤
                  3 * (n₁ : ℝ) ^ δ * (Real.log (n₁ : ℝ)) ^ (A_R + 2) := by
                rw [div_le_iff₀ (by positivity)]
                calc y₂ ≤ 3 * (n₁ : ℝ) ^ δ * (Real.log (n₁ : ℝ)) ^ (A_R + 4) := hy₂_le
                  _ = 3 * (n₁ : ℝ) ^ δ * (Real.log (n₁ : ℝ)) ^ (A_R + 2) * (Real.log (n₁ : ℝ)) ^ 2 := by ring
              have h2 := Real.log_le_log (by positivity) hdiv_le
              rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
                Real.log_rpow hn₁_pos, Real.log_pow] at h2
              push_cast at h2
              have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith)
              linarith
            have hfac_nn : 0 ≤ (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) := by positivity
            exact le_trans h1 (mul_le_mul_of_nonneg_left (by linarith) hfac_nn)
          · have hS_le2_empty : S_le2 = ∅ := by
              ext p; simp only [Finset.not_mem_empty, iff_false]
              intro hp; simp only [S_le2, S_le, Finset.mem_filter] at hp; linarith
            rw [hS_le2_empty, Finset.sum_empty]
            have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
            have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith)
            positivity
        have hS_le_eq : ∑ p ∈ S_le, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) =
            (∑ p ∈ S_le1, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) +
            (∑ p ∈ S_le2, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) := by
          rw [hsplit2, Finset.sum_union hdisj2]
        rw [hS_le_eq]
        have herr_ball1 : ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) < ε / 100 := by
          have := hN₁ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
            have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith); positivity)] at this
          exact this
        have herr_ball2 : 1 / Real.log (n₁ : ℝ) < ε / (100 * (C_mert + C₂ + 10)) := by
          have := hN₂ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this; exact this
        have h_gt_small : 2 * (n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2 ≤
            (ε / 10) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          have hlog2n : Real.log (2 * (n₁ : ℝ)) ≤ 2 * Real.log (n₁ : ℝ) := by
            rw [Real.log_mul (by norm_num) hn₁_pos.ne']
            have : Real.log 2 ≤ Real.log (n₁ : ℝ) := Real.log_le_log (by norm_num) (by linarith)
            linarith
          have h1 : 1 / Real.log (n₁ : ℝ) ≤ ε / 40 := by
            have : ε / (100 * (C_mert + C₂ + 10)) ≤ ε / 40 := by gcongr; linarith
            linarith
          calc 2 * (n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2
              ≤ 2 * (n₁ : ℝ) * (2 * Real.log (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2 := by gcongr
            _ = 4 * (1 / Real.log (n₁ : ℝ)) * (n₁ : ℝ) := by field_simp [hlog_n₁_pos.ne']; ring
            _ ≤ 4 * (ε / 40) * (n₁ : ℝ) := by gcongr
            _ = (ε / 10) * (n₁ : ℝ) := by ring
            _ ≤ (ε / 10) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
                have : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
                nlinarith [show 0 ≤ (ε / 10) * (n₁ : ℝ) by positivity]
        have h_le1_small : 2 * (n₁ : ℝ) * (Real.log ((Real.log (n₁ : ℝ)) ^ 2) + C_mert + 1) ≤
            (ε / 10) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          rw [Real.log_pow, Nat.cast_ofNat]
          have hloglog_le : Real.log (Real.log (n₁ : ℝ)) ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
            have h1 : Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) ≤
                ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) := by
              gcongr
              · have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith); positivity
              · have : (4 : ℝ) ≤ A_R := by exact_mod_cast (by omega : 4 ≤ A_R); linarith
            have h2 := (div_lt_iff₀ hlog_n₁_pos).mp (lt_of_le_of_lt h1 herr_ball1)
            linarith
          have hCm_le : C_mert + 1 ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
            have h1 : (C_mert + 1) / Real.log (n₁ : ℝ) ≤ ε / 100 := by
              calc (C_mert + 1) / Real.log (n₁ : ℝ)
                  = (C_mert + 1) * (1 / Real.log (n₁ : ℝ)) := by ring
                _ ≤ (C_mert + 1) * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
                _ ≤ ε / 100 := by
                    have : (C_mert + 1) / (100 * (C_mert + C₂ + 10)) ≤ 1 / 100 := by
                      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
                    calc (C_mert + 1) * (ε / (100 * (C_mert + C₂ + 10)))
                        = ε * ((C_mert + 1) / (100 * (C_mert + C₂ + 10))) := by ring
                      _ ≤ ε * (1 / 100) := by gcongr
                      _ = ε / 100 := by ring
            exact (div_le_iff₀ hlog_n₁_pos).mp h1
          nlinarith [show (0 : ℝ) ≤ n₁ by positivity]
        have h_le2_small : (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) *
            (δ * Real.log (n₁ : ℝ) + ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) + Real.log 3 + C_mert) ≤
            (δ + ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          have ha_le1 : 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          have ha_eps : 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ ε / 20 := by
            have h1 : 1 / Real.log (n₁ : ℝ) ≤ ε / 1000 := by
              have : ε / (100 * (C_mert + C₂ + 10)) ≤ ε / 1000 := by gcongr; linarith
              linarith
            have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
            calc 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ 2 / Real.log (n₁ : ℝ) := by gcongr; nlinarith
              _ = 2 * (1 / Real.log (n₁ : ℝ)) := by ring
              _ ≤ 2 * (ε / 1000) := by gcongr
              _ ≤ ε / 20 := by linarith
          have hb_eps : ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) + Real.log 3 + C_mert ≤
              (ε / 10) * Real.log (n₁ : ℝ) := by
            have hA4 : ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
              have := (div_lt_iff₀ hlog_n₁_pos).mp herr_ball1; linarith
            have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
              have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
            have h1 : (C_mert + 2) / Real.log (n₁ : ℝ) ≤ ε / 20 := by
              calc (C_mert + 2) / Real.log (n₁ : ℝ) = (C_mert + 2) * (1 / Real.log (n₁ : ℝ)) := by ring
                _ ≤ (C_mert + 2) * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
                _ ≤ ε / 20 := by
                    have : (C_mert + 2) / (100 * (C_mert + C₂ + 10)) ≤ 1 / 20 := by
                      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
                    calc (C_mert + 2) * (ε / (100 * (C_mert + C₂ + 10)))
                        = ε * ((C_mert + 2) / (100 * (C_mert + C₂ + 10))) := by ring
                      _ ≤ ε * (1 / 20) := by gcongr
                      _ = ε / 20 := by ring
            have h2 := (div_le_iff₀ hlog_n₁_pos).mp h1
            linarith
          have h_lin : (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) *
              (δ * Real.log (n₁ : ℝ) + ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) + Real.log 3 + C_mert) ≤
              (δ + ε / 4) * Real.log (n₁ : ℝ) := by
            calc (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) *
                  (δ * Real.log (n₁ : ℝ) + ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) + Real.log 3 + C_mert)
                ≤ (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * ((δ + ε / 10) * Real.log (n₁ : ℝ)) := by
                  gcongr; linarith
              _ = (δ + (2 / (Real.log (n₁ : ℝ)) ^ 2) * δ +
                    (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (ε / 10)) * Real.log (n₁ : ℝ) := by ring
              _ ≤ (δ + (ε / 20) * (1 / 4) + 2 * (ε / 10)) * Real.log (n₁ : ℝ) := by
                  gcongr; nlinarith
              _ ≤ (δ + ε / 4) * Real.log (n₁ : ℝ) := by gcongr; linarith
          calc (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) *
                (δ * Real.log (n₁ : ℝ) + ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) + Real.log 3 + C_mert)
              = (n₁ : ℝ) * ((1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) *
                  (δ * Real.log (n₁ : ℝ) + ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) + Real.log 3 + C_mert)) := by ring
            _ ≤ (n₁ : ℝ) * ((δ + ε / 4) * Real.log (n₁ : ℝ)) := by gcongr
            _ = (δ + ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
        linarith
      have hpf_nn : 0 ≤ parityFlipWeight n₁ n₂ := Finset.sum_nonneg (fun _ _ => by positivity)
      have hlogh_lb : δ * Real.log (n₁ : ℝ) ≤ Real.log (h : ℝ) := by
        have := Real.log_le_log (by positivity) hh_gt.le
        rwa [Real.log_rpow hn₁_pos] at this
      have hlogh_ub : Real.log (h : ℝ) ≤ δ * Real.log (n₁ : ℝ) + (ε / 100) * Real.log (n₁ : ℝ) := by
        have h1 := Real.log_le_log (by positivity) hh_small
        rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hn₁_pos, Real.log_pow] at h1
        push_cast at h1
        have hA2 : ((A_R : ℝ) + 2) * Real.log (Real.log (n₁ : ℝ)) ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
          have := hN₁ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
            have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith); positivity)] at this
          have h2 := (div_lt_iff₀ hlog_n₁_pos).mp this
          have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith)
          nlinarith
        linarith
      rw [abs_le]; constructor <;> nlinarith [show 0 ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
    · push_neg at hh_small
      let y₁ : ℝ := (h : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2)
      have hy₁_gt : (n₁ : ℝ) ^ δ < y₁ := by
        dsimp [y₁]; rw [lt_div_iff₀ (by positivity)]; exact hh_small
      have hy₁_lt_y₂ : y₁ < y₂ := by
        dsimp [y₁, y₂]
        have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
        have hpow1 : 1 ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 2) := one_le_pow₀ hlog1
        have h1 : (h : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2) ≤ (h : ℝ) := div_le_self (by positivity) hpow1
        have h2 : (h : ℝ) ≤ (h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2 := le_mul_of_one_le_right (by positivity) (by nlinarith)
        linarith
      have hn₁_delta_ge3 : 3 ≤ (n₁ : ℝ) ^ δ := by
        have h5 := hN₅ n₁ (by omega)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h5
        have h20 : 20 ≤ δ * Real.log (n₁ : ℝ) := by
          have := (div_lt_iff₀ hlog_n₁_pos).mp h5; linarith
        have hexp : (3 : ℝ) ≤ Real.exp (δ * Real.log (n₁ : ℝ)) := by
          have h1 : Real.exp 1 ≤ Real.exp (δ * Real.log (n₁ : ℝ)) := Real.exp_le_exp.mpr (by linarith)
          linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
        rwa [Real.rpow_def_of_pos hn₁_pos, mul_comm]
      unfold parityFlipWeight
      let S_all := (Finset.Icc 3 n₁).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (P_ratio n₁ n₂))
      let S_tiny := S_all.filter (fun p : ℕ => (p : ℝ) ≤ (n₁ : ℝ) ^ δ)
      let S_osc := S_all.filter (fun p : ℕ => (n₁ : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ≤ y₁)
      let S_collar := S_all.filter (fun p : ℕ => y₁ < (p : ℝ) ∧ (p : ℝ) < y₂)
      let S_upper := S_all.filter (fun p : ℕ => y₂ ≤ (p : ℝ))
      have hpart4 : ∑ p ∈ S_all, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) =
          (∑ p ∈ S_tiny, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) +
          (∑ p ∈ S_osc, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) +
          (∑ p ∈ S_collar, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) +
          (∑ p ∈ S_upper, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) := by
        have h12 : Disjoint S_tiny S_osc := by
          rw [Finset.disjoint_left]; intro p h1 h2
          simp only [S_tiny, S_osc, Finset.mem_filter] at h1 h2; linarith
        have h123 : Disjoint (S_tiny ∪ S_osc) S_collar := by
          rw [Finset.disjoint_left]; intro p h1 h2
          simp only [Finset.mem_union, S_tiny, S_osc, S_collar, Finset.mem_filter] at h1 h2
          rcases h1 with h1 | h1 <;> linarith
        have h1234 : Disjoint (S_tiny ∪ S_osc ∪ S_collar) S_upper := by
          rw [Finset.disjoint_left]; intro p h1 h2
          simp only [Finset.mem_union, S_tiny, S_osc, S_collar, S_upper, Finset.mem_filter] at h1 h2
          rcases h1 with (h1 | h1) | h1 <;> linarith
        have hun : S_all = S_tiny ∪ S_osc ∪ S_collar ∪ S_upper := by
          ext p; simp only [Finset.mem_union, S_tiny, S_osc, S_collar, S_upper, Finset.mem_filter]
          constructor
          · intro hp
            by_cases h1 : (p : ℝ) ≤ (n₁ : ℝ) ^ δ
            · exact Or.inl (Or.inl (Or.inl ⟨hp, h1⟩))
            · by_cases h2 : (p : ℝ) ≤ y₁
              · exact Or.inl (Or.inl (Or.inr ⟨hp, lt_of_not_ge h1, h2⟩))
              · by_cases h3 : (p : ℝ) < y₂
                · exact Or.inl (Or.inr ⟨hp, lt_of_not_ge h2, h3⟩)
                · exact Or.inr ⟨hp, le_of_not_gt h3⟩
          · rintro (((⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩) | ⟨hp, _⟩) <;> exact hp
        rw [hun, Finset.sum_union h1234, Finset.sum_union h123, Finset.sum_union h12]
      rw [hpart4]
      have hS_tiny_ub : ∑ p ∈ S_tiny, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
          (δ + ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        let S_t1 := S_tiny.filter (fun p : ℕ => (p : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ 2)
        let S_t2 := S_tiny.filter (fun p : ℕ => (Real.log (n₁ : ℝ)) ^ 2 < (p : ℝ))
        have hsp : S_tiny = S_t1 ∪ S_t2 := by
          ext p; simp only [Finset.mem_union, Finset.mem_filter, S_t1, S_t2]; constructor
          · intro hp; by_cases hle : (p : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ 2
            exact Or.inl ⟨hp, hle⟩; exact Or.inr ⟨hp, lt_of_not_ge hle⟩
          · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
        have hdj : Disjoint S_t1 S_t2 := by
          rw [Finset.disjoint_left]; intro p h1 h2
          simp only [Finset.mem_filter, S_t1, S_t2] at h1 h2; linarith
        rw [hsp, Finset.sum_union hdj]
        have ht1 : ∑ p ∈ S_t1, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
            2 * (n₁ : ℝ) * (Real.log ((Real.log (n₁ : ℝ)) ^ 2) + C_mert + 1) := by
          have hsub : S_t1 ⊆ (Finset.Icc 3 (Nat.floor ((Real.log (n₁ : ℝ)) ^ 2))).filter Nat.Prime := by
            intro p hp; simp only [S_t1, S_tiny, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
            exact ⟨⟨hp.1.1.1.1, Nat.le_floor hp.2⟩, hp.1.1.2.1⟩
          exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
            (h_tiny_bound ((Real.log (n₁ : ℝ)) ^ 2) hlog_ge3)
        have ht2 : ∑ p ∈ S_t2, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
            (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) * (δ * Real.log (n₁ : ℝ) + C_mert) := by
          by_cases hle : (Real.log (n₁ : ℝ)) ^ 2 ≤ (n₁ : ℝ) ^ δ
          · have hsub : S_t2 ⊆ ((Finset.Icc 3 (Nat.floor ((n₁ : ℝ) ^ δ))).filter Nat.Prime).filter
                (fun p : ℕ => (Real.log (n₁ : ℝ)) ^ 2 < (p : ℝ)) := by
              intro p hp; simp only [S_t2, S_tiny, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
              exact ⟨⟨⟨hp.1.1.1.1, Nat.le_floor hp.1.2⟩, hp.1.1.2.1⟩, hp.2⟩
            have h1 := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
              (h_band_exact ((Real.log (n₁ : ℝ)) ^ 2) ((n₁ : ℝ) ^ δ) (le_refl _) hle)
            have hlog_div : Real.log ((n₁ : ℝ) ^ δ / (Real.log (n₁ : ℝ)) ^ 2) ≤ δ * Real.log (n₁ : ℝ) := by
              have hdiv_le : (n₁ : ℝ) ^ δ / (Real.log (n₁ : ℝ)) ^ 2 ≤ (n₁ : ℝ) ^ δ :=
                div_le_self (by positivity) (by linarith)
              have h2 := Real.log_le_log (by positivity) hdiv_le
              rwa [Real.log_rpow hn₁_pos] at h2
            have hfac_nn : 0 ≤ (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) := by positivity
            exact le_trans h1 (mul_le_mul_of_nonneg_left (by linarith) hfac_nn)
          · have h_empty : S_t2 = ∅ := by
              ext p; simp only [Finset.not_mem_empty, iff_false]
              intro hp; simp only [S_t2, S_tiny, Finset.mem_filter] at hp; linarith
            rw [h_empty, Finset.sum_empty]; positivity
        have herr1 : ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) < ε / 100 := by
          have := hN₁ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
            have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith); positivity)] at this; exact this
        have herr2 : 1 / Real.log (n₁ : ℝ) < ε / (100 * (C_mert + C₂ + 10)) := by
          have := hN₂ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this; exact this
        have ht1_sm : 2 * (n₁ : ℝ) * (Real.log ((Real.log (n₁ : ℝ)) ^ 2) + C_mert + 1) ≤
            (ε / 20) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          rw [Real.log_pow, Nat.cast_ofNat]
          have hll : Real.log (Real.log (n₁ : ℝ)) ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
            have h1 : Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) ≤
                ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) := by
              gcongr; · have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith); positivity
              · have : (4 : ℝ) ≤ A_R := by exact_mod_cast (by omega : 4 ≤ A_R); linarith
            linarith [(div_lt_iff₀ hlog_n₁_pos).mp (lt_of_le_of_lt h1 herr1)]
          have hCm : C_mert + 1 ≤ (ε / 200) * Real.log (n₁ : ℝ) := by
            have h1 : (C_mert + 1) / Real.log (n₁ : ℝ) ≤ ε / 200 := by
              calc (C_mert + 1) / Real.log (n₁ : ℝ) = (C_mert + 1) * (1 / Real.log (n₁ : ℝ)) := by ring
                _ ≤ (C_mert + 1) * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
                _ ≤ ε / 200 := by
                    have : (C_mert + 1) / (100 * (C_mert + C₂ + 10)) ≤ 1 / 200 := by
                      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
                    calc (C_mert + 1) * (ε / (100 * (C_mert + C₂ + 10)))
                        = ε * ((C_mert + 1) / (100 * (C_mert + C₂ + 10))) := by ring
                      _ ≤ ε * (1 / 200) := by gcongr
                      _ = ε / 200 := by ring
            exact (div_le_iff₀ hlog_n₁_pos).mp h1
          nlinarith [show (0 : ℝ) ≤ n₁ by positivity]
        have ht2_sm : (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) * (δ * Real.log (n₁ : ℝ) + C_mert) ≤
            (δ + ε / 20) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          have ha1 : 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          have ha_eps : 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ ε / 40 := by
            have h1 : 1 / Real.log (n₁ : ℝ) ≤ ε / 1000 := by
              have : ε / (100 * (C_mert + C₂ + 10)) ≤ ε / 1000 := by gcongr; linarith
              linarith
            have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
            calc 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ 2 / Real.log (n₁ : ℝ) := by gcongr; nlinarith
              _ = 2 * (1 / Real.log (n₁ : ℝ)) := by ring
              _ ≤ 2 * (ε / 1000) := by gcongr
              _ ≤ ε / 40 := by linarith
          have hCm : C_mert ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
            have h1 : C_mert / Real.log (n₁ : ℝ) ≤ ε / 100 := by
              calc C_mert / Real.log (n₁ : ℝ) = C_mert * (1 / Real.log (n₁ : ℝ)) := by ring
                _ ≤ C_mert * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
                _ ≤ ε / 100 := by
                    have : C_mert / (100 * (C_mert + C₂ + 10)) ≤ 1 / 100 := by
                      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
                    calc C_mert * (ε / (100 * (C_mert + C₂ + 10)))
                        = ε * (C_mert / (100 * (C_mert + C₂ + 10))) := by ring
                      _ ≤ ε * (1 / 100) := by gcongr
                      _ = ε / 100 := by ring
            exact (div_le_iff₀ hlog_n₁_pos).mp h1
          have h_lin : (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (δ * Real.log (n₁ : ℝ) + C_mert) ≤
              (δ + ε / 20) * Real.log (n₁ : ℝ) := by
            calc (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (δ * Real.log (n₁ : ℝ) + C_mert)
                ≤ (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * ((δ + ε / 100) * Real.log (n₁ : ℝ)) := by gcongr; linarith
              _ = (δ + (2 / (Real.log (n₁ : ℝ)) ^ 2) * δ +
                    (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (ε / 100)) * Real.log (n₁ : ℝ) := by ring
              _ ≤ (δ + (ε / 40) * (1 / 4) + 2 * (ε / 100)) * Real.log (n₁ : ℝ) := by gcongr; nlinarith
              _ ≤ (δ + ε / 20) * Real.log (n₁ : ℝ) := by gcongr; linarith
          calc (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) * (δ * Real.log (n₁ : ℝ) + C_mert)
              = (n₁ : ℝ) * ((1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (δ * Real.log (n₁ : ℝ) + C_mert)) := by ring
            _ ≤ (n₁ : ℝ) * ((δ + ε / 20) * Real.log (n₁ : ℝ)) := by gcongr
            _ = (δ + ε / 20) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
        linarith
      have hlog2_le_ndelta : (Real.log (n₁ : ℝ)) ^ 2 ≤ (n₁ : ℝ) ^ δ := by
        have h6 := hN₆ n₁ (by omega)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h6
        exact (div_lt_one (by positivity)).mp h6 |>.le
      have hS_collar_ub : ∑ p ∈ S_collar, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
          (ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have hsub : S_collar ⊆ ((Finset.Icc 3 (Nat.floor y₂)).filter Nat.Prime).filter (fun p : ℕ => y₁ < (p : ℝ)) := by
          intro p hp; simp only [S_collar, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨⟨⟨hp.1.1.1.1, Nat.le_floor hp.2.2.le⟩, hp.1.2.1⟩, hp.2.1⟩
        have h1 := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
          (h_band_exact y₁ y₂ (le_trans hlog2_le_ndelta hy₁_gt.le) hy₁_lt_y₂.le)
        have hy_ratio : y₂ / y₁ ≤ 3 * (Real.log (n₁ : ℝ)) ^ (A_R + 4) := by
          have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
          have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
          have hy2_le : y₂ ≤ 3 * (h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2 := by
            dsimp [y₂]; nlinarith [show 1 ≤ (Real.log (n₁ : ℝ)) ^ 2 by nlinarith]
          rw [div_le_iff₀ (by positivity)]
          calc y₂ ≤ 3 * (h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2 := hy2_le
            _ = 3 * (Real.log (n₁ : ℝ)) ^ (A_R + 4) * y₁ := by
                dsimp [y₁]; field_simp [(by positivity : (Real.log (n₁ : ℝ)) ^ (A_R + 2) ≠ 0)]; ring
        have hlog_ratio : Real.log (y₂ / y₁) ≤ ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) + Real.log 3 := by
          have h2 := Real.log_le_log (by positivity) hy_ratio
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
          push_cast at h2; linarith
        have herr1 : ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
          have := hN₁ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
            have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith); positivity)] at this
          exact (div_lt_iff₀ hlog_n₁_pos).mp this |>.le
        have herr2 : Real.log 3 + C_mert ≤ (ε / 50) * Real.log (n₁ : ℝ) := by
          have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
          have h2 := hN₂ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
          have h3 : (C_mert + 2) / Real.log (n₁ : ℝ) ≤ ε / 50 := by
            calc (C_mert + 2) / Real.log (n₁ : ℝ) = (C_mert + 2) * (1 / Real.log (n₁ : ℝ)) := by ring
              _ ≤ (C_mert + 2) * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
              _ ≤ ε / 50 := by
                  have : (C_mert + 2) / (100 * (C_mert + C₂ + 10)) ≤ 1 / 50 := by
                    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
                  calc (C_mert + 2) * (ε / (100 * (C_mert + C₂ + 10)))
                      = ε * ((C_mert + 2) / (100 * (C_mert + C₂ + 10))) := by ring
                    _ ≤ ε * (1 / 50) := by gcongr
                    _ = ε / 50 := by ring
          linarith [(div_le_iff₀ hlog_n₁_pos).mp h3]
        have ha1 : 1 + 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ 2 := by
          have : 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          linarith
        calc ∑ p ∈ S_collar, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)
            ≤ (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) * (Real.log (y₂ / y₁) + C_mert) := h1
          _ ≤ 2 * (n₁ : ℝ) * ((ε / 100 + ε / 50) * Real.log (n₁ : ℝ)) := by gcongr; linarith
          _ ≤ (ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
              have : 2 * (ε / 100 + ε / 50) ≤ ε / 8 := by linarith
              nlinarith [show 0 ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
      have hS_upper_ub : ∑ p ∈ S_upper, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
          (ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have h1 := h_upper_bound S_upper (fun p hp => by
          simp only [S_upper, S_all, Finset.mem_filter, Finset.mem_Icc] at hp
          exact ⟨hp.1.2.1, hp.1.1.1, hp.1.1.2, hp.2, hp.1.2.2⟩)
        have hlog2n : Real.log (2 * (n₁ : ℝ)) ≤ 2 * Real.log (n₁ : ℝ) := by
          rw [Real.log_mul (by norm_num) hn₁_pos.ne']
          have : Real.log 2 ≤ Real.log (n₁ : ℝ) := Real.log_le_log (by norm_num) (by linarith)
          linarith
        have herr2 : 1 / Real.log (n₁ : ℝ) < ε / (100 * (C_mert + C₂ + 10)) := by
          have := hN₂ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this; exact this
        have h1' : 1 / Real.log (n₁ : ℝ) ≤ ε / 40 := by
          have : ε / (100 * (C_mert + C₂ + 10)) ≤ ε / 40 := by gcongr; linarith
          linarith
        calc ∑ p ∈ S_upper, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)
            ≤ 2 * (n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2 := h1
          _ ≤ 2 * (n₁ : ℝ) * (2 * Real.log (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2 := by gcongr
          _ = 4 * (1 / Real.log (n₁ : ℝ)) * (n₁ : ℝ) := by field_simp [hlog_n₁_pos.ne']; ring
          _ ≤ 4 * (ε / 40) * (n₁ : ℝ) := by gcongr
          _ ≤ (ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
              have : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
              nlinarith [show 0 ≤ (n₁ : ℝ) by positivity]
      let I_osc := ((Finset.Icc 3 n₁).filter Nat.Prime).filter (fun p : ℕ => (n₁ : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ≤ y₁)
      have hS_osc_eq : ∑ p ∈ S_osc, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) =
          (1 / 2 : ℝ) * (∑ p ∈ I_osc, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) -
          (1 / 2 : ℝ) * (∑ p ∈ I_osc,
            ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
              ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ))) := by
        have hsub : S_osc = I_osc.filter (fun p => ¬ 2 ∣ padicValNat p (P_ratio n₁ n₂)) := by
          ext p; simp only [S_osc, S_all, I_osc, Finset.mem_filter]; tauto
        rw [hsub, Finset.sum_filter]
        have hterm : ∀ p ∈ I_osc,
            (if ¬ 2 ∣ padicValNat p (P_ratio n₁ n₂) then
              (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) else 0) =
            (1 / 2 : ℝ) * ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) -
            (1 / 2 : ℝ) * (((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
              ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ))) := by
          intro p hp
          have hp_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
          have hneg := neg_one_pow_val_sum_eq hlt hp_pr
          by_cases hd : ¬ 2 ∣ padicValNat p (P_ratio n₁ n₂)
          · rw [if_pos hd]; rw [if_pos hd] at hneg; linear_combination hneg * ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ))
          · rw [if_neg hd]; rw [if_neg hd] at hneg; linear_combination hneg * ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ))
        rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hy₁_le_n₁ : y₁ ≤ (n₁ : ℝ) := by
        dsimp [y₁]
        have hh_le : (h : ℝ) ≤ (n₁ : ℝ) := by exact_mod_cast le_of_lt h_lt_n₁
        have hpow1 : 1 ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 2) := one_le_pow₀ (by nlinarith)
        exact le_trans (div_le_self (by positivity) hpow1) hh_le
      have hI_main_ub : ∑ p ∈ I_osc, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
          (n₁ : ℝ) * Real.log (h : ℝ) - δ * (n₁ : ℝ) * Real.log (n₁ : ℝ) + (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have hsub : I_osc ⊆ ((Finset.Icc 3 (Nat.floor y₁)).filter Nat.Prime).filter (fun p : ℕ => (n₁ : ℝ) ^ δ < (p : ℝ)) := by
          intro p hp; simp only [I_osc, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨⟨⟨hp.1.1.1, Nat.le_floor hp.2.2⟩, hp.1.2⟩, hp.2.1⟩
        have h1 := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
          (h_band_exact ((n₁ : ℝ) ^ δ) y₁ hlog2_le_ndelta hy₁_gt.le)
        have hlog_div : Real.log (y₁ / (n₁ : ℝ) ^ δ) ≤ Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) := by
          have hy1_le_h : y₁ ≤ (h : ℝ) := by
            dsimp [y₁]; exact div_le_self (by positivity) (one_le_pow₀ (by nlinarith))
          have h2 := Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hy1_le_h (by positivity))
          rwa [Real.log_div (by positivity) (by positivity), Real.log_rpow hn₁_pos] at h2
        have hCm : C_mert ≤ (ε / 20) * Real.log (n₁ : ℝ) := by
          have h2 := hN₂ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
          have h3 : C_mert / Real.log (n₁ : ℝ) ≤ ε / 20 := by
            calc C_mert / Real.log (n₁ : ℝ) = C_mert * (1 / Real.log (n₁ : ℝ)) := by ring
              _ ≤ C_mert * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
              _ ≤ ε / 20 := by
                  have : C_mert / (100 * (C_mert + C₂ + 10)) ≤ 1 / 20 := by
                    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
                  calc C_mert * (ε / (100 * (C_mert + C₂ + 10)))
                      = ε * (C_mert / (100 * (C_mert + C₂ + 10))) := by ring
                    _ ≤ ε * (1 / 20) := by gcongr
                    _ = ε / 20 := by ring
          exact (div_le_iff₀ hlog_n₁_pos).mp h3
        have ha_eps : 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ ε / 20 := by
          have h2 := hN₂ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
          have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
          calc 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ 2 / Real.log (n₁ : ℝ) := by gcongr; nlinarith
            _ = 2 * (1 / Real.log (n₁ : ℝ)) := by ring
            _ ≤ 2 * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
            _ ≤ ε / 20 := by
                have : 2 / (100 * (C_mert + C₂ + 10)) ≤ 1 / 20 := by
                  rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
                calc 2 * (ε / (100 * (C_mert + C₂ + 10)))
                    = ε * (2 / (100 * (C_mert + C₂ + 10))) := by ring
                  _ ≤ ε * (1 / 20) := by gcongr
                  _ = ε / 20 := by ring
        have ha1 : 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        have hdiff_nn : 0 ≤ Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) := by
          have := Real.log_le_log (by positivity) hh_gt.le
          rw [Real.log_rpow hn₁_pos] at this; linarith
        have hdiff_le : Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) ≤ Real.log (n₁ : ℝ) := by
          have : Real.log (h : ℝ) ≤ Real.log (n₁ : ℝ) := Real.log_le_log (by positivity) (by exact_mod_cast le_of_lt h_lt_n₁)
          linarith [show 0 ≤ δ * Real.log (n₁ : ℝ) by positivity]
        calc ∑ p ∈ I_osc, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)
            ≤ (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) * (Real.log (y₁ / (n₁ : ℝ) ^ δ) + C_mert) := h1
          _ ≤ (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) + C_mert) := by gcongr
          _ = (n₁ : ℝ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ)) +
              (n₁ : ℝ) * ((2 / (Real.log (n₁ : ℝ)) ^ 2) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ)) +
                (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * C_mert) := by ring
          _ ≤ (n₁ : ℝ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ)) +
              (n₁ : ℝ) * ((ε / 20) * Real.log (n₁ : ℝ) + 2 * ((ε / 20) * Real.log (n₁ : ℝ))) := by gcongr; linarith
          _ ≤ (n₁ : ℝ) * Real.log (h : ℝ) - δ * (n₁ : ℝ) * Real.log (n₁ : ℝ) + (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
              nlinarith [show 0 ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
      have hI_main_lb : (n₁ : ℝ) * Real.log (h : ℝ) - δ * (n₁ : ℝ) * Real.log (n₁ : ℝ) - (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) ≤
          ∑ p ∈ I_osc, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) := by
        have hterm : ∀ p ∈ I_osc,
            (n₁ : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) - Real.log (p : ℝ) ≤
              (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) := by
          intro p hp
          have hp_mem := Finset.mem_filter.mp hp
          have hp_pr := (Finset.mem_filter.mp hp_mem.1).2
          have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
          have hv1 : n₁ / p ≤ padicValNat p (Nat.factorial n₁) := by
            haveI : Fact p.Prime := ⟨hp_pr⟩
            have hleg := padicValNat_factorial (p := p) (n := n₁) (b := Nat.log p n₁ + 1) (Nat.lt_succ_self _)
            rw [hleg]
            rcases Nat.eq_zero_or_pos (Nat.log p n₁) with h0 | hlog_pos
            · have hn1_lt_p : n₁ < p := by
                by_contra hge; push_neg at hge
                have : 1 ≤ Nat.log p n₁ := Nat.log_pos hp_pr.one_lt hge
                omega
              rw [Nat.div_eq_of_lt hn1_lt_p]; exact Nat.zero_le _
            · have hmem : 1 ∈ Finset.Ico 1 (Nat.log p n₁ + 1) := Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩
              simpa using Finset.single_le_sum (f := fun i => n₁ / p ^ i) (fun _ _ => Nat.zero_le _) hmem
          have hv_real : (n₁ : ℝ) / (p : ℝ) - 1 ≤ (padicValNat p (Nat.factorial n₁) : ℝ) := by
            have h1 : (n₁ : ℝ) / (p : ℝ) - 1 < ((n₁ / p : ℕ) : ℝ) := by
              have hlt_nat : n₁ < (n₁ / p + 1) * p := by
                rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hp_pr.pos
              have hlt_r : (n₁ : ℝ) < ((n₁ / p : ℝ) + 1) * (p : ℝ) := by exact_mod_cast hlt_nat
              rw [← sub_lt_iff_lt_add, lt_div_iff₀ hp_pos]; linarith
            linarith [show ((n₁ / p : ℕ) : ℝ) ≤ (padicValNat p (Nat.factorial n₁) : ℝ) from by exact_mod_cast hv1]
          have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_pr.pos)
          calc (n₁ : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) - Real.log (p : ℝ)
              = ((n₁ : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) := by ring
            _ ≤ (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) := by gcongr
        refine le_trans ?_ (Finset.sum_le_sum hterm)
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hI_eq_diff : ∑ p ∈ I_osc, Real.log (p : ℝ) / (p : ℝ) =
            (∑ p ∈ (Finset.Icc 3 (Nat.floor y₁)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) -
            (∑ p ∈ (Finset.Icc 3 (Nat.floor ((n₁ : ℝ) ^ δ))).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) := by
          have hsub1 : (Finset.Icc 3 (Nat.floor ((n₁ : ℝ) ^ δ))).filter Nat.Prime ⊆
              (Finset.Icc 3 (Nat.floor y₁)).filter Nat.Prime := by
            intro p hp; simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
            exact ⟨⟨hp.1.1, Nat.le_floor (le_trans (Nat.le_of_le_floor hp.1.2) hy₁_gt.le)⟩, hp.2⟩
          have hdisj_i : Disjoint I_osc ((Finset.Icc 3 (Nat.floor ((n₁ : ℝ) ^ δ))).filter Nat.Prime) := by
            rw [Finset.disjoint_left]; intro p h1 h2
            simp only [I_osc, Finset.mem_filter, Finset.mem_Icc] at h1 h2
            have : (p : ℝ) ≤ (n₁ : ℝ) ^ δ := (Nat.le_floor_iff (by positivity)).mp h2.1.2
            linarith [h1.2.1]
          have hun_i : (Finset.Icc 3 (Nat.floor y₁)).filter Nat.Prime =
              I_osc ∪ (Finset.Icc 3 (Nat.floor ((n₁ : ℝ) ^ δ))).filter Nat.Prime := by
            ext p; simp only [Finset.mem_union, I_osc, Finset.mem_filter, Finset.mem_Icc]
            constructor
            · intro hp
              by_cases hle : (p : ℝ) ≤ (n₁ : ℝ) ^ δ
              · exact Or.inr ⟨⟨hp.1.1, Nat.le_floor hle⟩, hp.2⟩
              · refine Or.inl ⟨⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_le_floor hy₁_le_n₁)⟩, hp.2⟩,
                  lt_of_not_ge hle, (Nat.le_floor_iff (by positivity)).mp hp.1.2⟩
            · rintro (hp | hp)
              · exact ⟨⟨hp.1.1.1, Nat.le_floor hp.2.2⟩, hp.1.2⟩
              · exact ⟨⟨hp.1.1, Nat.le_floor (le_trans ((Nat.le_floor_iff (by positivity)).mp hp.1.2) hy₁_gt.le)⟩, hp.2⟩
          rw [hun_i, Finset.sum_union hdisj_i]; ring
        have h_p_pm1 : (1 - 1 / (n₁ : ℝ) ^ δ) *
            ∑ p ∈ I_osc, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤
            ∑ p ∈ I_osc, Real.log (p : ℝ) / (p : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro p hp
          have hp_mem := Finset.mem_filter.mp hp
          have hp_pr := (Finset.mem_filter.mp hp_mem.1).2
          have hp_gt : (n₁ : ℝ) ^ δ < (p : ℝ) := hp_mem.2.1
          have hp3 : (3 : ℝ) < (p : ℝ) := lt_of_le_of_lt hn₁_delta_ge3 hp_gt
          have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
          have hratio : (1 - 1 / (n₁ : ℝ) ^ δ) / ((p : ℝ) - 1) ≤ 1 / (p : ℝ) := by
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            have h1 : 1 / (p : ℝ) ≤ 1 / (n₁ : ℝ) ^ δ := one_div_le_one_div_of_le (by positivity) hp_gt.le
            calc (1 - 1 / (n₁ : ℝ) ^ δ) * (p : ℝ) ≤ (1 - 1 / (p : ℝ)) * (p : ℝ) := by gcongr; linarith
              _ = (p : ℝ) - 1 := by field_simp [(by linarith : (p : ℝ) ≠ 0)]
              _ = 1 * ((p : ℝ) - 1) := by ring
          calc (1 - 1 / (n₁ : ℝ) ^ δ) * (Real.log (p : ℝ) / ((p : ℝ) - 1))
              = Real.log (p : ℝ) * ((1 - 1 / (n₁ : ℝ) ^ δ) / ((p : ℝ) - 1)) := by ring
            _ ≤ Real.log (p : ℝ) * (1 / (p : ℝ)) := by gcongr
            _ = Real.log (p : ℝ) / (p : ℝ) := by ring
        have hmert_osc_lb : Real.log (y₁ / (n₁ : ℝ) ^ δ) - 2 * C_mert1 ≤
            ∑ p ∈ I_osc, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
          have hm1 := abs_le.mp (hMert1 y₁ (le_trans hn₁_delta_ge3 hy₁_gt.le))
          have hm2 := abs_le.mp (hMert1 ((n₁ : ℝ) ^ δ) hn₁_delta_ge3)
          have hsum_eq : ∑ p ∈ I_osc, Real.log (p : ℝ) / ((p : ℝ) - 1) =
              (∑ p ∈ (Finset.Icc 3 (Nat.floor y₁)).filter Nat.Prime, Real.log (p : ℝ) / ((p : ℝ) - 1)) -
              (∑ p ∈ (Finset.Icc 3 (Nat.floor ((n₁ : ℝ) ^ δ))).filter Nat.Prime, Real.log (p : ℝ) / ((p : ℝ) - 1)) := by
            have hdisj_i : Disjoint I_osc ((Finset.Icc 3 (Nat.floor ((n₁ : ℝ) ^ δ))).filter Nat.Prime) := by
              rw [Finset.disjoint_left]; intro p h1 h2
              simp only [I_osc, Finset.mem_filter, Finset.mem_Icc] at h1 h2
              have : (p : ℝ) ≤ (n₁ : ℝ) ^ δ := (Nat.le_floor_iff (by positivity)).mp h2.1.2
              linarith [h1.2.1]
            have hun_i : (Finset.Icc 3 (Nat.floor y₁)).filter Nat.Prime =
                I_osc ∪ (Finset.Icc 3 (Nat.floor ((n₁ : ℝ) ^ δ))).filter Nat.Prime := by
              ext p; simp only [Finset.mem_union, I_osc, Finset.mem_filter, Finset.mem_Icc]
              constructor
              · intro hp
                by_cases hle : (p : ℝ) ≤ (n₁ : ℝ) ^ δ
                · exact Or.inr ⟨⟨hp.1.1, Nat.le_floor hle⟩, hp.2⟩
                · refine Or.inl ⟨⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_le_floor hy₁_le_n₁)⟩, hp.2⟩,
                    lt_of_not_ge hle, (Nat.le_floor_iff (by positivity)).mp hp.1.2⟩
              · rintro (hp | hp)
                · exact ⟨⟨hp.1.1.1, Nat.le_floor hp.2.2⟩, hp.1.2⟩
                · exact ⟨⟨hp.1.1, Nat.le_floor (le_trans ((Nat.le_floor_iff (by positivity)).mp hp.1.2) hy₁_gt.le)⟩, hp.2⟩
            rw [hun_i, Finset.sum_union hdisj_i]; ring
          rw [hsum_eq, Real.log_div (by positivity) (by positivity)]
          linarith
        have hsum_log_I : ∑ p ∈ I_osc, Real.log (p : ℝ) ≤ (n₁ : ℝ) := by
          have hcard : (I_osc.card : ℝ) ≤ y₁ := by
            have hsub : I_osc ⊆ Finset.Icc 1 (Nat.floor y₁) := by
              intro p hp; simp only [I_osc, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
              exact ⟨by omega, Nat.le_floor hp.2.2⟩
            exact le_trans (by exact_mod_cast le_trans (Finset.card_le_card hsub) (by simp)) (Nat.floor_le (by positivity))
          have hterm_log : ∀ p ∈ I_osc, Real.log (p : ℝ) ≤ Real.log (n₁ : ℝ) := by
            intro p hp; simp only [I_osc, Finset.mem_filter, Finset.mem_Icc] at hp
            exact Real.log_le_log (by positivity) (by exact_mod_cast hp.1.1.2)
          calc ∑ p ∈ I_osc, Real.log (p : ℝ) ≤ (I_osc.card : ℝ) * Real.log (n₁ : ℝ) := by
                simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hterm_log
            _ ≤ y₁ * Real.log (n₁ : ℝ) := by gcongr
            _ ≤ ((n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2)) * Real.log (n₁ : ℝ) := by
                gcongr; dsimp [y₁]; exact div_le_div_of_nonneg_right (by exact_mod_cast le_of_lt h_lt_n₁) (by positivity)
            _ ≤ (n₁ : ℝ) := by
                have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
                have hpow : Real.log (n₁ : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 2) :=
                  le_self_pow₀ hlog1 (by omega)
                rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
                exact mul_le_mul_of_nonneg_left hpow (by positivity)
        have h_log_y1 : Real.log (y₁ / (n₁ : ℝ) ^ δ) =
            Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - ((A_R : ℝ) + 2) * Real.log (Real.log (n₁ : ℝ)) := by
          dsimp [y₁]
          rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
            Real.log_rpow hn₁_pos, Real.log_pow]
          push_cast; ring
        have herr1 : ((A_R : ℝ) + 2) * Real.log (Real.log (n₁ : ℝ)) ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
          have := hN₁ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
            have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith); positivity)] at this
          have h2 := (div_lt_iff₀ hlog_n₁_pos).mp this
          have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith)
          nlinarith
        have hCm1 : 2 * C_mert1 ≤ (ε / 50) * Real.log (n₁ : ℝ) := by
          have h7 := hN₇ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h7
          have h3 : 2 * C_mert1 / Real.log (n₁ : ℝ) ≤ ε / 50 := by
            calc 2 * C_mert1 / Real.log (n₁ : ℝ) = 2 * C_mert1 * (1 / Real.log (n₁ : ℝ)) := by ring
              _ ≤ 2 * C_mert1 * (ε / (100 * (C_mert1 + C_mert + C₂ + 10))) := by gcongr
              _ ≤ ε / 50 := by
                  have : 2 * C_mert1 / (100 * (C_mert1 + C_mert + C₂ + 10)) ≤ 1 / 50 := by
                    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
                  calc 2 * C_mert1 * (ε / (100 * (C_mert1 + C_mert + C₂ + 10)))
                      = ε * (2 * C_mert1 / (100 * (C_mert1 + C_mert + C₂ + 10))) := by ring
                    _ ≤ ε * (1 / 50) := by gcongr
                    _ = ε / 50 := by ring
          exact (div_le_iff₀ hlog_n₁_pos).mp h3
        have h_one_sub : 1 / (n₁ : ℝ) ^ δ ≤ ε / 20 := by
          have h1 : (n₁ : ℝ) ^ δ ≥ (Real.log (n₁ : ℝ)) ^ 2 := hlog2_le_ndelta
          have h7 := hN₇ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h7
          have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
          calc 1 / (n₁ : ℝ) ^ δ ≤ 1 / (Real.log (n₁ : ℝ)) ^ 2 := one_div_le_one_div_of_le (by positivity) h1
            _ ≤ 1 / Real.log (n₁ : ℝ) := one_div_le_one_div_of_le (by positivity) (by nlinarith)
            _ ≤ ε / (100 * (C_mert1 + C_mert + C₂ + 10)) := h7.le
            _ ≤ ε / 20 := by gcongr; linarith
        have h_1n_le : (n₁ : ℝ) ≤ (ε / 100) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          have h7 := hN₇ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h7
          have h1 : 1 ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
            have : 1 / Real.log (n₁ : ℝ) ≤ ε / 100 := le_trans h7.le (by gcongr; linarith)
            exact (div_le_iff₀ hlog_n₁_pos).mp this
          nlinarith [show (0 : ℝ) ≤ n₁ by positivity]
        have hmert_nn : 0 ≤ ∑ p ∈ I_osc, Real.log (p : ℝ) / ((p : ℝ) - 1) :=
          Finset.sum_nonneg (fun p hp => div_nonneg (Real.log_nonneg (by
            exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.pos)) (by
            have := (Finset.mem_filter.mp hp).1
            have : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp this).1).1
            exact_mod_cast (by omega : 0 ≤ (p : ℤ) - 1)))
        have h_lb1 : Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - (ε / 20) * Real.log (n₁ : ℝ) ≤
            ∑ p ∈ I_osc, Real.log (p : ℝ) / ((p : ℝ) - 1) := by linarith
        have h_lb1_nn : 0 ≤ Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) := by
          have := Real.log_le_log (by positivity) hh_gt.le
          rw [Real.log_rpow hn₁_pos] at this; linarith
        have h_lb1_ub : Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) ≤ Real.log (n₁ : ℝ) := by
          have : Real.log (h : ℝ) ≤ Real.log (n₁ : ℝ) := Real.log_le_log (by positivity) (by exact_mod_cast le_of_lt h_lt_n₁)
          linarith [show 0 ≤ δ * Real.log (n₁ : ℝ) by positivity]
        have h_sub_prod : (1 - 1 / (n₁ : ℝ) ^ δ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - (ε / 20) * Real.log (n₁ : ℝ)) ≤
            ∑ p ∈ I_osc, Real.log (p : ℝ) / (p : ℝ) := by
          have h1nonneg : 0 ≤ 1 - 1 / (n₁ : ℝ) ^ δ := by
            have : (1 : ℝ) ≤ (n₁ : ℝ) ^ δ := by linarith
            linarith [div_le_one (by positivity : (0 : ℝ) < (n₁ : ℝ) ^ δ) |>.mpr this]
          exact le_trans (mul_le_mul_of_nonneg_left h_lb1 h1nonneg) h_p_pm1
        have h_est : Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - (ε / 10) * Real.log (n₁ : ℝ) ≤
            (1 - 1 / (n₁ : ℝ) ^ δ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - (ε / 20) * Real.log (n₁ : ℝ)) := by
          have hdiff_le : Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - (ε / 20) * Real.log (n₁ : ℝ) ≤ Real.log (n₁ : ℝ) := by
            linarith [show 0 ≤ (ε / 20) * Real.log (n₁ : ℝ) by positivity]
          have h1n_nn : 0 ≤ 1 / (n₁ : ℝ) ^ δ := by positivity
          have : (1 / (n₁ : ℝ) ^ δ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - (ε / 20) * Real.log (n₁ : ℝ)) ≤
              (ε / 20) * Real.log (n₁ : ℝ) := by
            by_cases hneg : Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - (ε / 20) * Real.log (n₁ : ℝ) ≤ 0
            · exact le_trans (mul_nonpos_of_nonneg_of_nonpos h1n_nn hneg) (by positivity)
            · push_neg at hneg
              calc (1 / (n₁ : ℝ) ^ δ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - (ε / 20) * Real.log (n₁ : ℝ))
                  ≤ (ε / 20) * Real.log (n₁ : ℝ) := mul_le_mul h_one_sub hdiff_le hneg.le (by positivity)
          linarith
        nlinarith [show (0 : ℝ) ≤ n₁ by positivity]
      have hI_osc_bound : |∑ p ∈ I_osc,
          ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
            ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ))| ≤
          (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have hI_mem : ∀ p ∈ I_osc, (n₁ : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ≤ y₁ := by
          intro p hp; exact (Finset.mem_filter.mp hp).2
        obtain ⟨hpart_osc, hdisj_osc⟩ :=
          dyadic_partition_finset (by linarith : 1 ≤ (n₁ : ℝ) ^ δ) hy₁_gt.le I_osc hI_mem
        let H := Nat.floor (((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2))
        have hH_ge1 : 1 ≤ H := by
          have h5 := hN₅ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h5
          have h10 : 10 ≤ (δ / 2) * Real.log (n₁ : ℝ) := by
            have := (div_lt_iff₀ hlog_n₁_pos).mp h5; linarith
          exact Nat.le_floor (one_le_pow_of_one_le₀ (by linarith) _)
        obtain ⟨c_tilde, b_tilde, h_supp, h_ctilde_b, h_btilde0, h_btilde_b, h_vaaler_pw, h_L1⟩ :=
          vaaler_parity_approx H hH_ge1
        have hblock_bound : ∀ k ∈ dyadicBlocks ((n₁ : ℝ) ^ δ) y₁,
            |∑ p ∈ I_osc.filter (fun p : ℕ =>
                (n₁ : ℝ) ^ δ * (2 : ℝ) ^ k < (p : ℝ) ∧ (p : ℝ) ≤ 2 * ((n₁ : ℝ) ^ δ * (2 : ℝ) ^ k)),
              ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
                ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ))| ≤
            (ε / (16 * (Real.log (n₁ : ℝ) / Real.log 2 + 2))) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          intro k hk
          let P : ℝ := (n₁ : ℝ) ^ δ * (2 : ℝ) ^ k
          let I_k := I_osc.filter (fun p : ℕ => P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P)
          have hP_pos : 0 < P := by positivity
          have hP_lb : (n₁ : ℝ) ^ δ ≤ P := by
            dsimp [P]; exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
          have hP_lt_y₁ : P < y₁ := (Finset.mem_filter.mp hk).2
          have hP_le_n₁ : P ≤ (n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ 12 := by
            have hy1_le : y₁ ≤ (n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2) := by
              dsimp [y₁]; exact div_le_div_of_nonneg_right (by exact_mod_cast le_of_lt h_lt_n₁) (by positivity)
            have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
            have hpow_le : (Real.log (n₁ : ℝ)) ^ 12 ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 2) :=
              pow_le_pow_right₀ hlog1 (by omega)
            exact le_trans hP_lt_y₁.le (le_trans hy1_le (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow_le))
          have hP_le_h : P ≤ (h : ℝ) / (Real.log (h : ℝ)) ^ 12 := by
            have hlog1 : 1 ≤ Real.log (h : ℝ) := by
              have : δ * Real.log (n₁ : ℝ) ≤ Real.log (h : ℝ) := by
                have := Real.log_le_log (by positivity) hh_gt.le; rwa [Real.log_rpow hn₁_pos] at this
              have h5 := hN₅ n₁ (by omega)
              rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h5
              linarith [(div_lt_iff₀ hlog_n₁_pos).mp h5]
            have hlog_le : Real.log (h : ℝ) ≤ Real.log (n₁ : ℝ) :=
              Real.log_le_log (by positivity) (by exact_mod_cast le_of_lt h_lt_n₁)
            have hpow_le : (Real.log (h : ℝ)) ^ 12 ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 2) :=
              le_trans (pow_le_pow_left₀ (by positivity) hlog_le 12) (pow_le_pow_right₀ (by nlinarith) (by omega))
            exact le_trans hP_lt_y₁.le (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow_le)
          have hI_k : ∀ p ∈ I_k, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P := by
            intro p hp
            have h1 := Finset.mem_filter.mp hp
            have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1.1).1).2
            exact ⟨h2, h1.2.1, h1.2.2⟩
          have hh_ge_Nexp : N_exp ≤ h := by
            have h1 : (N_exp : ℝ) ≤ (n₁ : ℝ) ^ δ := le_trans (le_max_left _ _) (hN_exp_d n₁ (by omega))
            exact_mod_cast (lt_of_le_of_lt h1 hh_gt).le
          have hn₂_ge_Nexp : N_exp ≤ n₂ := by omega
          have hP_le_n₂ : P ≤ (n₂ : ℝ) / (Real.log (n₂ : ℝ)) ^ 12 := by
            have hlog_n2_le : Real.log (n₂ : ℝ) ≤ 2 * Real.log (n₁ : ℝ) := by
              have hn2_lt : (n₂ : ℝ) < 2 * (n₁ : ℝ) := by exact_mod_cast (by omega : n₂ < 2 * n₁)
              have h1 := Real.log_le_log (by positivity) hn2_lt.le
              rw [Real.log_mul (by norm_num) hn₁_pos.ne'] at h1
              have : Real.log 2 ≤ Real.log (n₁ : ℝ) := Real.log_le_log (by norm_num) (by linarith)
              linarith
            have hpow_le : (Real.log (n₂ : ℝ)) ^ 12 ≤ (2 * Real.log (n₁ : ℝ)) ^ 12 :=
              pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n₂))) hlog_n2_le 12
            have h2_12 : (2 : ℝ) ^ 12 ≤ (Real.log (n₁ : ℝ)) ^ 12 := by
              have hlog2 : 2 ≤ Real.log (n₁ : ℝ) := by nlinarith
              exact pow_le_pow_left₀ (by norm_num) hlog2 12
            have hpow_ar : (2 * Real.log (n₁ : ℝ)) ^ 12 ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 2) := by
              rw [mul_pow]
              calc (2 : ℝ) ^ 12 * (Real.log (n₁ : ℝ)) ^ 12
                  ≤ (Real.log (n₁ : ℝ)) ^ 12 * (Real.log (n₁ : ℝ)) ^ 12 := by gcongr
                _ = (Real.log (n₁ : ℝ)) ^ 24 := by ring
                _ ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 2) := pow_le_pow_right₀ (by nlinarith) (by omega)
            have hy1_le : y₁ ≤ (n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2) := by
              dsimp [y₁]; exact div_le_div_of_nonneg_right (by exact_mod_cast le_of_lt h_lt_n₁) (by positivity)
            have hn1_le_n2 : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast le_of_lt hlt
            exact le_trans hP_lt_y₁.le (le_trans hy1_le (div_le_div₀ (by positivity) hn1_le_n2 (by positivity)
              (le_trans hpow_le hpow_ar)))
          have hExp_at : ∀ (m : ℕ), N_exp ≤ m → m ≤ n₁ → P ≤ (m : ℝ) / (Real.log (m : ℝ)) ^ 12 →
              (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (m : ℝ)) ^ A_R ≤ (m : ℝ) / P →
              ∀ (hm1 : ℤ) (w : ℝ → ℝ) (W₀ : ℝ),
              hm1 ≠ 0 → |hm1| ≤ 2 * (Nat.floor ((Real.log (m : ℝ)) ^ (R + 2)) : ℤ) + 1 →
              (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) → 0 ≤ W₀ →
              ‖∑ p ∈ I_k, (w (p : ℝ) * Real.log (p : ℝ) : ℂ) *
                eExp ((hm1 : ℝ) * (m : ℝ) / (2 * (p : ℝ)))‖ ≤
                C₂ * W₀ * P * (Real.log (m : ℝ)) ^ (-((R : ℝ) + 2)) := by
            intro m hm_N hm_le hPm hTm hm1 w W₀ hm1_nz hm1_bd hw hW₀
            have hm_exp := hN_exp m hm_N
            have hP_m_lb : (m : ℝ) ^ δ ≤ P := by
              have hm_pos : (0 : ℝ) < m := by
                by_contra h0; push_neg at h0
                have hm0 : m = 0 := by exact_mod_cast (by linarith : (m : ℝ) ≤ 0)
                subst hm0; simp at hPm; linarith
              have h1 : (m : ℝ) ^ δ ≤ (n₁ : ℝ) ^ δ :=
                Real.rpow_le_rpow (by positivity) (by exact_mod_cast hm_le) hδ0.le
              exact le_trans h1 hP_lb
            have hA_nz : ∃ r ∈ ({1} : Finset ℕ), (fun _ : ℕ => hm1) r ≠ 0 :=
              ⟨1, Finset.mem_singleton_self 1, hm1_nz⟩
            have h1 := (hm_exp P I_k {1} (fun _ => hm1) w W₀ hA_nz hP_m_lb hPm hI_k
              (fun r hr => by rw [Finset.mem_singleton] at hr; subst hr; exact ⟨le_refl 1, by omega⟩)
              (fun r hr => by rw [Finset.mem_singleton] at hr; subst hr; exact hm1_bd)
              (fun r hr => by rw [Finset.mem_singleton] at hr; subst hr; simpa using hTm)
              hw hW₀).1.2
            simpa only [Finset.sum_singleton, pow_one] using h1
          have hTm_n1 : (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n₁ : ℝ)) ^ A_R ≤ (n₁ : ℝ) / P := by
            have hy1_le : y₁ ≤ (n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2) := by
              dsimp [y₁]; exact div_le_div_of_nonneg_right (by exact_mod_cast le_of_lt h_lt_n₁) (by positivity)
            have hP_div : (Real.log (n₁ : ℝ)) ^ (A_R + 2) ≤ (n₁ : ℝ) / P := by
              rw [le_div_iff₀ hP_pos]
              have h2 := le_trans hP_lt_y₁.le hy1_le
              rwa [le_div_iff₀ (by positivity), mul_comm] at h2
            have h2_le : (2 : ℝ) ^ (-(R : ℤ)) ≤ 1 := by
              rw [zpow_neg, zpow_natCast]
              exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
            have hpow_le : (Real.log (n₁ : ℝ)) ^ A_R ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 2) :=
              pow_le_pow_right₀ (by nlinarith) (by omega)
            calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n₁ : ℝ)) ^ A_R
                ≤ 1 * (Real.log (n₁ : ℝ)) ^ (A_R + 2) := mul_le_mul h2_le hpow_le (by positivity) (by norm_num)
              _ = (Real.log (n₁ : ℝ)) ^ (A_R + 2) := one_mul _
              _ ≤ (n₁ : ℝ) / P := hP_div
          have hTm_h : (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (h : ℝ)) ^ A_R ≤ (h : ℝ) / P := by
            have hP_div : (Real.log (n₁ : ℝ)) ^ (A_R + 2) ≤ (h : ℝ) / P := by
              rw [le_div_iff₀ hP_pos]
              have h2 : P ≤ (h : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2) := hP_lt_y₁.le
              rwa [le_div_iff₀ (by positivity), mul_comm] at h2
            have hlog_le : Real.log (h : ℝ) ≤ Real.log (n₁ : ℝ) :=
              Real.log_le_log (by positivity) (by exact_mod_cast le_of_lt h_lt_n₁)
            have h2_le : (2 : ℝ) ^ (-(R : ℤ)) ≤ 1 := by
              rw [zpow_neg, zpow_natCast]
              exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
            have hpow_le : (Real.log (h : ℝ)) ^ A_R ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 2) :=
              le_trans (pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ h))) hlog_le A_R)
                (pow_le_pow_right₀ (by nlinarith) (by omega))
            calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (h : ℝ)) ^ A_R
                ≤ 1 * (Real.log (n₁ : ℝ)) ^ (A_R + 2) := mul_le_mul h2_le hpow_le (by positivity) (by norm_num)
              _ ≤ (h : ℝ) / P := hP_div
          have hH_le_n1 : 4 * (H : ℤ) + 2 ≤ 2 * (Nat.floor ((Real.log (n₁ : ℝ)) ^ (R + 2)) : ℤ) + 1 := by
            have hH_le_real : (H : ℝ) ≤ ((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2) := Nat.floor_le (by positivity)
            have h2R : ((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2) ≤ (1 / 64 : ℝ) * (Real.log (n₁ : ℝ)) ^ (R + 2) := by
              rw [mul_pow]
              have hd_le : δ ^ (R + 2) ≤ 1 := pow_le_one₀ hδ0.le (by linarith)
              have h2_le : (1 / 2 : ℝ) ^ (R + 2) ≤ 1 / 64 := by
                calc (1 / 2 : ℝ) ^ (R + 2) ≤ (1 / 2 : ℝ) ^ 6 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
                  _ = 1 / 64 := by norm_num
              have : (δ / 2 : ℝ) ^ (R + 2) ≤ 1 / 64 := by
                rw [div_pow]; calc δ ^ (R + 2) / 2 ^ (R + 2) = δ ^ (R + 2) * (1 / 2 : ℝ) ^ (R + 2) := by ring
                  _ ≤ 1 * (1 / 64) := mul_le_mul hd_le h2_le (by positivity) (by norm_num)
                  _ = 1 / 64 := one_mul _
              exact mul_le_mul_of_nonneg_right this (by positivity)
            have hfl_lt : (Real.log (n₁ : ℝ)) ^ (R + 2) - 1 < (Nat.floor ((Real.log (n₁ : ℝ)) ^ (R + 2)) : ℝ) :=
              Nat.sub_one_lt_floor _
            have h_real : 4 * (H : ℝ) + 2 ≤ 2 * (Nat.floor ((Real.log (n₁ : ℝ)) ^ (R + 2)) : ℝ) + 1 := by
              have : 1 ≤ (H : ℝ) := by exact_mod_cast hH_ge1
              linarith
            exact_mod_cast h_real
          have hH_le_h : 2 * (H : ℤ) + 1 ≤ 2 * (Nat.floor ((Real.log (h : ℝ)) ^ (R + 2)) : ℤ) + 1 := by
            have hlog_h_ge : δ * Real.log (n₁ : ℝ) ≤ Real.log (h : ℝ) := by
              have := Real.log_le_log (by positivity) hh_gt.le; rwa [Real.log_rpow hn₁_pos] at this
            have hH_le_real : (H : ℝ) ≤ ((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2) := Nat.floor_le (by positivity)
            have h2R : ((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2) ≤ (Real.log (h : ℝ)) ^ (R + 2) := by
              apply pow_le_pow_left₀ (by positivity)
              linarith [show 0 ≤ δ * Real.log (n₁ : ℝ) by positivity]
            exact_mod_cast (by
              have : (H : ℝ) ≤ (Nat.floor ((Real.log (h : ℝ)) ^ (R + 2)) : ℝ) :=
                (Nat.le_floor_iff (by positivity)).mpr (le_trans hH_le_real h2R)
              linarith)
          let w_base : ℝ → ℝ := fun t =>
            let p := Nat.floor t
            if p = 0 then 0 else
              ((-1 : ℝ) ^ ((padicValNat p (Nat.factorial n₁) - n₁ / p) +
                (padicValNat p (Nat.factorial n₂) - n₂ / p))) *
              ((padicValNat p (Nat.factorial n₁) : ℝ) / ((n₁ : ℝ) / P))
          have hw_base_bd : ∀ t ∈ Set.Icc P (2 * P), |w_base t| ≤ 3 := by
            intro t ht
            dsimp [w_base]
            set p := Nat.floor t
            by_cases hp0 : p = 0
            · simp [hp0]
            · simp only [hp0, ↓reduceIte, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
              by_cases hp_pr : p.Prime
              · have hp_ge3 : 3 ≤ p := by
                  have hP3 : 3 ≤ P := le_trans hn₁_delta_ge3 hP_lb
                  have hlt_fl : P - 1 < (p : ℝ) := by
                    have := Nat.sub_one_lt_floor t; linarith [ht.1]
                  have : 2 < p := by exact_mod_cast (by linarith : (2 : ℝ) < (p : ℝ))
                  omega
                have hv := val_factorial_le_two_div (n := n₁) hp_pr hp_ge3
                have hP_le_t : P ≤ t := ht.1
                have hp_ge_P2 : (2 / 3 : ℝ) * P ≤ (p : ℝ) := by
                  have hP3 : 3 ≤ P := le_trans hn₁_delta_ge3 hP_lb
                  have hlt_fl : t - 1 < (p : ℝ) := Nat.sub_one_lt_floor t
                  linarith
                have hv3 : (padicValNat p (Nat.factorial n₁) : ℝ) ≤ 3 * (n₁ : ℝ) / P := by
                  calc (padicValNat p (Nat.factorial n₁) : ℝ) ≤ 2 * (n₁ : ℝ) / (p : ℝ) := hv
                    _ ≤ 2 * (n₁ : ℝ) / ((2 / 3 : ℝ) * P) := by gcongr
                    _ = 3 * (n₁ : ℝ) / P := by ring
                rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
                linarith
              · simp only [padicValNat.eq_zero_of_not_prime hp_pr, Nat.cast_zero, zero_div, abs_zero]
                norm_num
          have h_sum_rewrite : ∑ p ∈ I_k,
              ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
                ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) =
              ((n₁ : ℝ) / P) * (∑ p ∈ I_k,
                (w_base (p : ℝ) * Real.log (p : ℝ)) *
                  ((-1 : ℝ) ^ (Int.floor ((n₁ : ℝ) / (p : ℝ)))) *
                  ((-1 : ℝ) ^ (Int.floor ((n₂ : ℝ) / (p : ℝ))))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro p hp
            have hp_mem := hI_k p hp
            have hp_pr := hp_mem.1
            have hp_ne0 : p ≠ 0 := hp_pr.ne_zero
            have hfl_p : Nat.floor (p : ℝ) = p := Nat.floor_natCast p
            have hv_le1 : n₁ / p ≤ padicValNat p (Nat.factorial n₁) := by
              haveI : Fact p.Prime := ⟨hp_pr⟩
              have hleg := padicValNat_factorial (p := p) (n := n₁) (b := Nat.log p n₁ + 1) (Nat.lt_succ_self _)
              rw [hleg]
              rcases Nat.eq_zero_or_pos (Nat.log p n₁) with h0 | hpos
              · have : n₁ < p := by
                  by_contra hge; push_neg at hge; have := Nat.log_pos hp_pr.one_lt hge; omega
                rw [Nat.div_eq_of_lt this]; exact Nat.zero_le _
              · exact Finset.single_le_sum (f := fun i => n₁ / p ^ i) (fun _ _ => Nat.zero_le _)
                  (Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩)
            have hv_le2 : n₂ / p ≤ padicValNat p (Nat.factorial n₂) := by
              haveI : Fact p.Prime := ⟨hp_pr⟩
              have hleg := padicValNat_factorial (p := p) (n := n₂) (b := Nat.log p n₂ + 1) (Nat.lt_succ_self _)
              rw [hleg]
              rcases Nat.eq_zero_or_pos (Nat.log p n₂) with h0 | hpos
              · have : n₂ < p := by
                  by_contra hge; push_neg at hge; have := Nat.log_pos hp_pr.one_lt hge; omega
                rw [Nat.div_eq_of_lt this]; exact Nat.zero_le _
              · exact Finset.single_le_sum (f := fun i => n₂ / p ^ i) (fun _ _ => Nat.zero_le _)
                  (Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩)
            have hfl1 : Int.floor ((n₁ : ℝ) / (p : ℝ)) = ((n₁ / p : ℕ) : ℤ) := by
              rw [Int.floor_eq_iff]; constructor
              · rw [Int.cast_natCast, le_div_iff₀ (by exact_mod_cast hp_pr.pos)]
                exact_mod_cast Nat.div_mul_le_self n₁ p
              · rw [Int.cast_natCast, div_lt_iff₀ (by exact_mod_cast hp_pr.pos)]
                have := Nat.lt_div_mul_add (a := n₁) hp_pr.pos; rw [add_mul, one_mul] at this
                exact_mod_cast this
            have hfl2 : Int.floor ((n₂ : ℝ) / (p : ℝ)) = ((n₂ / p : ℕ) : ℤ) := by
              rw [Int.floor_eq_iff]; constructor
              · rw [Int.cast_natCast, le_div_iff₀ (by exact_mod_cast hp_pr.pos)]
                exact_mod_cast Nat.div_mul_le_self n₂ p
              · rw [Int.cast_natCast, div_lt_iff₀ (by exact_mod_cast hp_pr.pos)]
                have := Nat.lt_div_mul_add (a := n₂) hp_pr.pos; rw [add_mul, one_mul] at this
                exact_mod_cast this
            have hexp_eq : padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂) =
                ((padicValNat p (Nat.factorial n₁) - n₁ / p) +
                  (padicValNat p (Nat.factorial n₂) - n₂ / p)) + (n₁ / p + n₂ / p) := by omega
            dsimp [w_base]
            rw [hfl_p, if_neg hp_ne0, hfl1, hfl2, zpow_natCast, zpow_natCast]
            have h_pow : (-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂)) =
                (-1 : ℝ) ^ ((padicValNat p (Nat.factorial n₁) - n₁ / p) +
                  (padicValNat p (Nat.factorial n₂) - n₂ / p)) *
                (-1 : ℝ) ^ (n₁ / p) * (-1 : ℝ) ^ (n₂ / p) := by
              rw [hexp_eq, pow_add, pow_add]; ring
            rw [h_pow]
            have hn1P_ne : (n₁ : ℝ) / P ≠ 0 := by positivity
            field_simp [hn1P_ne]; ring
          let S_H := (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h)
          let Psi_tilde : ℝ → ℂ := fun x =>
            ∑ h ∈ S_H, c_tilde h * eExp ((h : ℝ) * x / 2)
          let B_tilde : ℝ → ℂ := fun x =>
            ∑ h ∈ Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1),
              b_tilde h * eExp ((h : ℝ) * x / 2)
          let mainC : ℂ := ∑ p ∈ I_k,
            ((w_base (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
              Psi_tilde ((n₁ : ℝ) / (p : ℝ)) * Psi_tilde ((n₂ : ℝ) / (p : ℝ))
          let errC : ℂ := ∑ p ∈ I_k,
            ((w_base (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
              ((((-1 : ℝ) ^ Int.floor ((n₁ : ℝ) / (p : ℝ)) : ℝ) : ℂ) *
                (((-1 : ℝ) ^ Int.floor ((n₂ : ℝ) / (p : ℝ)) : ℝ) : ℂ) -
                Psi_tilde ((n₁ : ℝ) / (p : ℝ)) * Psi_tilde ((n₂ : ℝ) / (p : ℝ)))
          have h_sum_re : (∑ p ∈ I_k,
              (w_base (p : ℝ) * Real.log (p : ℝ)) *
                ((-1 : ℝ) ^ (Int.floor ((n₁ : ℝ) / (p : ℝ)))) *
                ((-1 : ℝ) ^ (Int.floor ((n₂ : ℝ) / (p : ℝ))))) = (mainC + errC).re := by
            rw [Complex.add_re, Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro p _
            rw [← Complex.add_re, ← mul_add, add_sub_cancel]
            simp only [← Complex.ofReal_mul, Complex.ofReal_re]; ring
          have h_mainC_bd : ‖mainC‖ ≤
              ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ 2 *
                (6 * C₂ * P * (δ ^ (-(R : ℤ) - 2) + 1) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) := by
            have hmain_eq : mainC = ∑ h₁ ∈ S_H, ∑ h₂ ∈ S_H, (c_tilde h₁ * c_tilde h₂) *
                ∑ p ∈ I_k, ((w_base (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
                  eExp (((h₁ : ℝ) * (n₁ : ℝ) + (h₂ : ℝ) * (n₂ : ℝ)) / (2 * (p : ℝ))) := by
              dsimp [mainC, Psi_tilde]
              simp_rw [Finset.mul_sum, Finset.sum_mul]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro h₁ _
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro h₂ _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro p _
              have h_e : eExp ((h₁ : ℝ) * ((n₁ : ℝ) / (p : ℝ)) / 2) *
                  eExp ((h₂ : ℝ) * ((n₂ : ℝ) / (p : ℝ)) / 2) =
                  eExp (((h₁ : ℝ) * (n₁ : ℝ) + (h₂ : ℝ) * (n₂ : ℝ)) / (2 * (p : ℝ))) := by
                unfold eExp; rw [← Complex.exp_add]; congr 1; push_cast; ring
              rw [← h_e]; ring
            rw [hmain_eq]
            have hterm_bd : ∀ h₁ ∈ S_H, ∀ h₂ ∈ S_H,
                ‖∑ p ∈ I_k, ((w_base (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
                  eExp (((h₁ : ℝ) * (n₁ : ℝ) + (h₂ : ℝ) * (n₂ : ℝ)) / (2 * (p : ℝ)))‖ ≤
                6 * C₂ * P * (δ ^ (-(R : ℤ) - 2) + 1) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by
              intro h₁ hh₁ h₂ hh₂
              have hh₁_m := Finset.mem_filter.mp hh₁
              have hh₂_m := Finset.mem_filter.mp hh₂
              have hh₁_icc := Finset.mem_Icc.mp hh₁_m.1
              have hh₂_icc := Finset.mem_Icc.mp hh₂_m.1
              by_cases hsum0 : h₁ + h₂ = 0
              · have h_eq : ∀ p : ℕ,
                    ((h₁ : ℝ) * (n₁ : ℝ) + (h₂ : ℝ) * (n₂ : ℝ)) / (2 * (p : ℝ)) =
                    (h₂ : ℝ) * (h : ℝ) / (2 * (p : ℝ)) := by
                  intro p
                  have hn2_eq : (n₂ : ℝ) = (n₁ : ℝ) + (h : ℝ) := by exact_mod_cast (by omega : n₂ = n₁ + h)
                  have hh1_eq : (h₁ : ℝ) = -(h₂ : ℝ) := by exact_mod_cast (by omega : h₁ = -h₂)
                  rw [hn2_eq, hh1_eq]; ring
                simp_rw [h_eq]
                have h2_bd : |h₂| ≤ 2 * (Nat.floor ((Real.log (h : ℝ)) ^ (R + 2)) : ℤ) + 1 :=
                  le_trans (abs_le.mpr ⟨hh₂_icc.1, hh₂_icc.2⟩) hH_le_h
                have h_res := hExp_at h hh_ge_Nexp (by omega) hP_le_h hTm_h h₂ w_base 3 hh₂_m.2.1 h2_bd hw_base_bd (by norm_num)
                have hlogh_lb : δ * Real.log (n₁ : ℝ) ≤ Real.log (h : ℝ) := by
                  have := Real.log_le_log (by positivity) hh_gt.le; rwa [Real.log_rpow hn₁_pos] at this
                have hrpow_le : (Real.log (h : ℝ)) ^ (-((R : ℝ) + 2)) ≤
                    δ ^ (-(R : ℤ) - 2) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by
                  have h1 : (δ * Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) ≤ (Real.log (h : ℝ)) ^ (-((R : ℝ) + 2)) :=
                    Real.rpow_le_rpow_of_nonpos (by positivity) hlogh_lb (by linarith)
                  rw [Real.mul_rpow hδ0.le hlog_n₁_pos.le] at h1
                  have hdz : δ ^ (-((R : ℝ) + 2)) = δ ^ (-(R : ℤ) - 2) := by
                    rw [show (-((R : ℝ) + 2)) = ((-(R : ℤ) - 2 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
                  linarith
                calc ‖∑ p ∈ I_k, _‖ ≤ C₂ * 3 * P * (Real.log (h : ℝ)) ^ (-((R : ℝ) + 2)) := h_res
                  _ ≤ C₂ * 3 * P * (δ ^ (-(R : ℤ) - 2) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) := by gcongr
                  _ ≤ 6 * C₂ * P * (δ ^ (-(R : ℤ) - 2) + 1) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by
                      have : 0 ≤ C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by positivity
                      nlinarith [show 0 ≤ δ ^ (-(R : ℤ) - 2) by positivity]
              · let w_cos : ℝ → ℝ := fun t => w_base t * Real.cos (2 * Real.pi * ((h₂ : ℝ) * (h : ℝ) / (2 * t)))
                let w_sin : ℝ → ℝ := fun t => w_base t * Real.sin (2 * Real.pi * ((h₂ : ℝ) * (h : ℝ) / (2 * t)))
                have hw_cos : ∀ t ∈ Set.Icc P (2 * P), |w_cos t| ≤ 3 := fun t ht => by
                  dsimp [w_cos]; rw [abs_mul]
                  calc |w_base t| * |Real.cos _| ≤ 3 * 1 := mul_le_mul (hw_base_bd t ht) (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
                    _ = 3 := mul_one 3
                have hw_sin : ∀ t ∈ Set.Icc P (2 * P), |w_sin t| ≤ 3 := fun t ht => by
                  dsimp [w_sin]; rw [abs_mul]
                  calc |w_base t| * |Real.sin _| ≤ 3 * 1 := mul_le_mul (hw_base_bd t ht) (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)
                    _ = 3 := mul_one 3
                have h12_bd : |h₁ + h₂| ≤ 2 * (Nat.floor ((Real.log (n₁ : ℝ)) ^ (R + 2)) : ℤ) + 1 := by
                  have h1 : |h₁| ≤ 2 * (H : ℤ) + 1 := abs_le.mpr ⟨hh₁_icc.1, hh₁_icc.2⟩
                  have h2 : |h₂| ≤ 2 * (H : ℤ) + 1 := abs_le.mpr ⟨hh₂_icc.1, hh₂_icc.2⟩
                  exact le_trans (abs_add_le h₁ h₂) (le_trans (add_le_add h1 h2) (by linarith [hH_le_n1]))
                have h_cos_bd := hExp_at n₁ (by omega) (le_refl n₁) hP_le_n₁ hTm_n1 (h₁ + h₂) w_cos 3 hsum0 h12_bd hw_cos (by norm_num)
                have h_sin_bd := hExp_at n₁ (by omega) (le_refl n₁) hP_le_n₁ hTm_n1 (h₁ + h₂) w_sin 3 hsum0 h12_bd hw_sin (by norm_num)
                have h_split_cs : ∑ p ∈ I_k, ((w_base (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
                      eExp (((h₁ : ℝ) * (n₁ : ℝ) + (h₂ : ℝ) * (n₂ : ℝ)) / (2 * (p : ℝ))) =
                    (∑ p ∈ I_k, (w_cos (p : ℝ) * Real.log (p : ℝ) : ℂ) *
                      eExp (((h₁ + h₂ : ℤ) : ℝ) * (n₁ : ℝ) / (2 * (p : ℝ)))) +
                    Complex.I * (∑ p ∈ I_k, (w_sin (p : ℝ) * Real.log (p : ℝ) : ℂ) *
                      eExp (((h₁ + h₂ : ℤ) : ℝ) * (n₁ : ℝ) / (2 * (p : ℝ)))) := by
                  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl; intro p _
                  have hn2_eq : (n₂ : ℝ) = (n₁ : ℝ) + (h : ℝ) := by exact_mod_cast (by omega : n₂ = n₁ + h)
                  have h_e : eExp (((h₁ : ℝ) * (n₁ : ℝ) + (h₂ : ℝ) * (n₂ : ℝ)) / (2 * (p : ℝ))) =
                      eExp (((h₁ + h₂ : ℤ) : ℝ) * (n₁ : ℝ) / (2 * (p : ℝ))) *
                        eExp ((h₂ : ℝ) * (h : ℝ) / (2 * (p : ℝ))) := by
                    unfold eExp; rw [← Complex.exp_add]; congr 1; push_cast; rw [hn2_eq]; ring
                  have h_cis : eExp ((h₂ : ℝ) * (h : ℝ) / (2 * (p : ℝ))) =
                      (Real.cos (2 * Real.pi * ((h₂ : ℝ) * (h : ℝ) / (2 * (p : ℝ)))) : ℂ) +
                      Complex.I * (Real.sin (2 * Real.pi * ((h₂ : ℝ) * (h : ℝ) / (2 * (p : ℝ)))) : ℂ) := by
                    unfold eExp
                    rw [show (2 * Real.pi * ((h₂ : ℝ) * (h : ℝ) / (2 * (p : ℝ))) : ℂ) * Complex.I =
                        ((2 * Real.pi * ((h₂ : ℝ) * (h : ℝ) / (2 * (p : ℝ))) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                      Complex.exp_mul_I]
                    push_cast; rfl
                  rw [h_e, h_cis]; dsimp [w_cos, w_sin]; push_cast; ring
                rw [h_split_cs]
                calc ‖_ + Complex.I * _‖
                    ≤ ‖∑ p ∈ I_k, (w_cos (p : ℝ) * Real.log (p : ℝ) : ℂ) * _‖ +
                      ‖Complex.I * ∑ p ∈ I_k, (w_sin (p : ℝ) * Real.log (p : ℝ) : ℂ) * _‖ := norm_add_le _ _
                  _ = ‖∑ p ∈ I_k, (w_cos (p : ℝ) * Real.log (p : ℝ) : ℂ) * _‖ +
                      ‖∑ p ∈ I_k, (w_sin (p : ℝ) * Real.log (p : ℝ) : ℂ) * _‖ := by
                      rw [norm_mul, Complex.norm_I, one_mul]
                  _ ≤ C₂ * 3 * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) +
                      C₂ * 3 * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := add_le_add h_cos_bd h_sin_bd
                  _ ≤ 6 * C₂ * P * (δ ^ (-(R : ℤ) - 2) + 1) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by
                      have : 0 ≤ C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by positivity
                      nlinarith [show 0 ≤ δ ^ (-(R : ℤ) - 2) by positivity]
            calc ‖∑ h₁ ∈ S_H, ∑ h₂ ∈ S_H, _‖
                ≤ ∑ h₁ ∈ S_H, ‖∑ h₂ ∈ S_H, _‖ := norm_sum_le _ _
              _ ≤ ∑ h₁ ∈ S_H, ∑ h₂ ∈ S_H, ‖(c_tilde h₁ * c_tilde h₂) * _‖ :=
                  Finset.sum_le_sum (fun h₁ _ => norm_sum_le _ _)
              _ ≤ ∑ h₁ ∈ S_H, ∑ h₂ ∈ S_H, (‖c_tilde h₁‖ * ‖c_tilde h₂‖) *
                    (6 * C₂ * P * (δ ^ (-(R : ℤ) - 2) + 1) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) := by
                  apply Finset.sum_le_sum; intro h₁ hh₁
                  apply Finset.sum_le_sum; intro h₂ hh₂
                  rw [norm_mul, norm_mul]
                  exact mul_le_mul_of_nonneg_left (hterm_bd h₁ hh₁ h₂ hh₂) (by positivity)
              _ = (∑ h₁ ∈ S_H, ‖c_tilde h₁‖) * (∑ h₂ ∈ S_H, ‖c_tilde h₂‖) *
                    (6 * C₂ * P * (δ ^ (-(R : ℤ) - 2) + 1) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) := by
                  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
              _ ≤ ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ 2 *
                    (6 * C₂ * P * (δ ^ (-(R : ℤ) - 2) + 1) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) := by
                  rw [sq]; gcongr
          let L₁ : ℝ := (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)
          have hL1_ge1 : 1 ≤ L₁ := by
            dsimp [L₁]
            have hpi4 : 1 ≤ 4 / Real.pi := by rw [one_le_div Real.pi_pos]; linarith [Real.pi_lt_four]
            have hlog1 : 0 ≤ Real.log (2 * (H : ℝ) + 1) := Real.log_nonneg (by positivity)
            nlinarith
          have h_errC_bd : ‖errC‖ ≤ 3 * L₁ *
              (((4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) +
                12 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) +
               ((4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) +
                24 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)))) := by
            have hpw_bd : ∀ p ∈ I_k,
                ‖((((-1 : ℝ) ^ Int.floor ((n₁ : ℝ) / (p : ℝ)) : ℝ) : ℂ) *
                  (((-1 : ℝ) ^ Int.floor ((n₂ : ℝ) / (p : ℝ)) : ℝ) : ℂ) -
                  Psi_tilde ((n₁ : ℝ) / (p : ℝ)) * Psi_tilde ((n₂ : ℝ) / (p : ℝ)))‖ ≤
                L₁ * (B_tilde ((n₁ : ℝ) / (p : ℝ))).re + L₁ * (B_tilde ((n₂ : ℝ) / (p : ℝ))).re := by
              intro p hp
              have h1 := h_vaaler_pw ((n₁ : ℝ) / (p : ℝ))
              have h2 := h_vaaler_pw ((n₂ : ℝ) / (p : ℝ))
              have hB1_nn : 0 ≤ (B_tilde ((n₁ : ℝ) / (p : ℝ))).re := le_trans (norm_nonneg _) h1
              have hB2_nn : 0 ≤ (B_tilde ((n₂ : ℝ) / (p : ℝ))).re := le_trans (norm_nonneg _) h2
              have ha2_bd : ‖((((-1 : ℝ) ^ Int.floor ((n₂ : ℝ) / (p : ℝ)) : ℝ) : ℂ))‖ ≤ 1 := by
                rw [Complex.norm_real, Real.norm_eq_abs, abs_zpow, abs_neg, abs_one, one_zpow]
              have hb1_bd : ‖Psi_tilde ((n₁ : ℝ) / (p : ℝ))‖ ≤ L₁ := by
                dsimp [Psi_tilde]
                calc ‖∑ h ∈ S_H, c_tilde h * eExp ((h : ℝ) * ((n₁ : ℝ) / (p : ℝ)) / 2)‖
                    ≤ ∑ h ∈ S_H, ‖c_tilde h * eExp ((h : ℝ) * ((n₁ : ℝ) / (p : ℝ)) / 2)‖ := norm_sum_le _ _
                  _ = ∑ h ∈ S_H, ‖c_tilde h‖ := by
                      apply Finset.sum_congr rfl; intro h _
                      rw [norm_mul]; unfold eExp
                      rw [show (2 * Real.pi * ((h : ℝ) * ((n₁ : ℝ) / (p : ℝ)) / 2) : ℂ) * Complex.I =
                        ((2 * Real.pi * ((h : ℝ) * ((n₁ : ℝ) / (p : ℝ)) / 2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                        Complex.norm_exp_ofReal_mul_I, mul_one]
                  _ ≤ L₁ := h_L1
              have hid : (((-1 : ℝ) ^ Int.floor ((n₁ : ℝ) / (p : ℝ)) : ℝ) : ℂ) *
                    (((-1 : ℝ) ^ Int.floor ((n₂ : ℝ) / (p : ℝ)) : ℝ) : ℂ) -
                    Psi_tilde ((n₁ : ℝ) / (p : ℝ)) * Psi_tilde ((n₂ : ℝ) / (p : ℝ)) =
                  (((((-1 : ℝ) ^ Int.floor ((n₁ : ℝ) / (p : ℝ)) : ℝ) : ℂ) - Psi_tilde ((n₁ : ℝ) / (p : ℝ))) *
                    (((-1 : ℝ) ^ Int.floor ((n₂ : ℝ) / (p : ℝ)) : ℝ) : ℂ)) +
                  (Psi_tilde ((n₁ : ℝ) / (p : ℝ)) *
                    (((((-1 : ℝ) ^ Int.floor ((n₂ : ℝ) / (p : ℝ)) : ℝ) : ℂ) - Psi_tilde ((n₂ : ℝ) / (p : ℝ))))) := by ring
              rw [hid]
              calc ‖_ + _‖ ≤ ‖_‖ + ‖_‖ := norm_add_le _ _
                _ = ‖_ - _‖ * ‖_‖ + ‖Psi_tilde _‖ * ‖_ - _‖ := by rw [norm_mul, norm_mul]
                _ ≤ (B_tilde ((n₁ : ℝ) / (p : ℝ))).re * 1 + L₁ * (B_tilde ((n₂ : ℝ) / (p : ℝ))).re := by gcongr
                _ ≤ L₁ * (B_tilde ((n₁ : ℝ) / (p : ℝ))).re + L₁ * (B_tilde ((n₂ : ℝ) / (p : ℝ))).re := by nlinarith
            have hB1_sum : ∑ p ∈ I_k, Real.log (p : ℝ) * (B_tilde ((n₁ : ℝ) / (p : ℝ))).re ≤
                (4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) +
                  12 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by
              refine vaaler_btilde_dyadic_sum_bound H hH_ge1 b_tilde h_btilde0 h_btilde_b n₁ (by omega) P hP_pos I_k hI_k
                (fun h' hh' hbd => ?_) C₂ hC₂.le R
              have hbd' : |h'| ≤ 2 * (Nat.floor ((Real.log (n₁ : ℝ)) ^ (R + 2)) : ℤ) + 1 :=
                le_trans hbd (by linarith [hH_le_n1])
              simpa using hExp_at n₁ (by omega) (le_refl n₁) hP_le_n₁ hTm_n1 h' (fun _ => 1) 1 hh' hbd'
                (fun _ _ => by norm_num) (by norm_num)
            have hB2_sum : ∑ p ∈ I_k, Real.log (p : ℝ) * (B_tilde ((n₂ : ℝ) / (p : ℝ))).re ≤
                (4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) +
                  24 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by
              refine vaaler_btilde_dyadic_sum_bound H hH_ge1 b_tilde h_btilde0 h_btilde_b n₂ (by omega) P hP_pos I_k hI_k
                (fun h' hh' hbd => ?_) (2 * C₂) (by linarith) R
              have hbd' : |h'| ≤ 2 * (Nat.floor ((Real.log (n₁ : ℝ)) ^ (R + 2)) : ℤ) + 1 :=
                le_trans hbd (by linarith [hH_le_n1])
              let w_cos : ℝ → ℝ := fun t => Real.cos (2 * Real.pi * ((h' : ℝ) * (h : ℝ) / (2 * t)))
              let w_sin : ℝ → ℝ := fun t => Real.sin (2 * Real.pi * ((h' : ℝ) * (h : ℝ) / (2 * t)))
              have h_cs := hExp_at n₁ (by omega) (le_refl n₁) hP_le_n₁ hTm_n1 h' w_cos 1 hh' hbd'
                (fun t _ => Real.abs_cos_le_one _) (by norm_num)
              have h_sn := hExp_at n₁ (by omega) (le_refl n₁) hP_le_n₁ hTm_n1 h' w_sin 1 hh' hbd'
                (fun t _ => Real.abs_sin_le_one _) (by norm_num)
              have h_sp : ∑ p ∈ I_k, (Real.log (p : ℝ) : ℂ) * eExp ((h' : ℝ) * (n₂ : ℝ) / (2 * (p : ℝ))) =
                  (∑ p ∈ I_k, (w_cos (p : ℝ) * Real.log (p : ℝ) : ℂ) * eExp ((h' : ℝ) * (n₁ : ℝ) / (2 * (p : ℝ)))) +
                  Complex.I * (∑ p ∈ I_k, (w_sin (p : ℝ) * Real.log (p : ℝ) : ℂ) * eExp ((h' : ℝ) * (n₁ : ℝ) / (2 * (p : ℝ)))) := by
                rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl; intro p _
                have hn2_eq : (n₂ : ℝ) = (n₁ : ℝ) + (h : ℝ) := by exact_mod_cast (by omega : n₂ = n₁ + h)
                have h_e : eExp ((h' : ℝ) * (n₂ : ℝ) / (2 * (p : ℝ))) =
                    eExp ((h' : ℝ) * (n₁ : ℝ) / (2 * (p : ℝ))) * eExp ((h' : ℝ) * (h : ℝ) / (2 * (p : ℝ))) := by
                  unfold eExp; rw [← Complex.exp_add]; congr 1; rw [hn2_eq]; ring
                have h_cis : eExp ((h' : ℝ) * (h : ℝ) / (2 * (p : ℝ))) =
                    (Real.cos (2 * Real.pi * ((h' : ℝ) * (h : ℝ) / (2 * (p : ℝ)))) : ℂ) +
                    Complex.I * (Real.sin (2 * Real.pi * ((h' : ℝ) * (h : ℝ) / (2 * (p : ℝ)))) : ℂ) := by
                  unfold eExp
                  rw [show (2 * Real.pi * ((h' : ℝ) * (h : ℝ) / (2 * (p : ℝ))) : ℂ) * Complex.I =
                      ((2 * Real.pi * ((h' : ℝ) * (h : ℝ) / (2 * (p : ℝ))) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                    Complex.exp_mul_I]
                  push_cast; rfl
                rw [h_e, h_cis]; dsimp [w_cos, w_sin]; push_cast; ring
              rw [h_sp]
              calc ‖_ + Complex.I * _‖ ≤ ‖_‖ + ‖Complex.I * _‖ := norm_add_le _ _
                _ = ‖_‖ + ‖_‖ := by rw [norm_mul, Complex.norm_I, one_mul]
                _ ≤ C₂ * 1 * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) +
                    C₂ * 1 * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := add_le_add h_cs h_sn
                _ = 2 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by ring
            calc ‖errC‖ ≤ ∑ p ∈ I_k, ‖((w_base (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) * _‖ := norm_sum_le _ _
              _ ≤ ∑ p ∈ I_k, 3 * Real.log (p : ℝ) *
                    (L₁ * (B_tilde ((n₁ : ℝ) / (p : ℝ))).re + L₁ * (B_tilde ((n₂ : ℝ) / (p : ℝ))).re) := by
                  apply Finset.sum_le_sum; intro p hp
                  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
                  have hp_mem := hI_k p hp
                  have hw3 : |w_base (p : ℝ)| ≤ 3 := hw_base_bd (p : ℝ) ⟨hp_mem.2.1.le, hp_mem.2.2⟩
                  have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_mem.1.pos)
                  rw [abs_of_nonneg hlog_nn]
                  calc |w_base (p : ℝ)| * Real.log (p : ℝ) * ‖_‖
                      ≤ 3 * Real.log (p : ℝ) * (L₁ * (B_tilde ((n₁ : ℝ) / (p : ℝ))).re + L₁ * (B_tilde ((n₂ : ℝ) / (p : ℝ))).re) := by
                        gcongr; exact hpw_bd p hp
              _ = 3 * L₁ * ((∑ p ∈ I_k, Real.log (p : ℝ) * (B_tilde ((n₁ : ℝ) / (p : ℝ))).re) +
                    (∑ p ∈ I_k, Real.log (p : ℝ) * (B_tilde ((n₂ : ℝ) / (p : ℝ))).re)) := by
                  simp_rw [← Finset.sum_add_distrib, Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
              _ ≤ _ := by gcongr; linarith
          have h_comb : |∑ p ∈ I_k,
              ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
                ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ))| ≤
              ((n₁ : ℝ) / P) * (‖mainC‖ + ‖errC‖) := by
            rw [h_sum_rewrite, abs_mul, abs_of_nonneg (by positivity), h_sum_re]
            gcongr
            exact le_trans (Complex.abs_re_le_norm _) (norm_add_le _ _)
          have hL1_ub : L₁ ≤ 2 * ((R : ℝ) + 4) * (Real.log (Real.log (n₁ : ℝ)) + 1) := by
            dsimp [L₁]
            have hH_ub : 2 * (H : ℝ) + 1 ≤ (Real.log (n₁ : ℝ)) ^ (R + 3) := by
              have h1 : (H : ℝ) ≤ ((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2) := Nat.floor_le (by positivity)
              have h2 : ((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2) ≤ (Real.log (n₁ : ℝ)) ^ (R + 2) :=
                pow_le_pow_left₀ (by positivity) (by nlinarith) _
              have hlog10 : 10 ≤ Real.log (n₁ : ℝ) := by
                have h5 := hN₅ n₁ (by omega)
                rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h5
                have : 20 ≤ δ * Real.log (n₁ : ℝ) := by have := (div_lt_iff₀ hlog_n₁_pos).mp h5; linarith
                nlinarith
              have hpow1 : 1 ≤ (Real.log (n₁ : ℝ)) ^ (R + 2) := one_le_pow₀ (by linarith)
              calc 2 * (H : ℝ) + 1 ≤ 2 * (Real.log (n₁ : ℝ)) ^ (R + 2) + 1 := by linarith
                _ ≤ (Real.log (n₁ : ℝ)) * (Real.log (n₁ : ℝ)) ^ (R + 2) := by nlinarith
                _ = (Real.log (n₁ : ℝ)) ^ (R + 3) := (pow_succ' _ _).symm
            have hlog_bd : Real.log (2 * (H : ℝ) + 1) ≤ ((R : ℝ) + 3) * Real.log (Real.log (n₁ : ℝ)) := by
              have h1 := Real.log_le_log (by positivity) hH_ub
              rw [Real.log_pow] at h1; push_cast at h1; exact h1
            have h4pi : 4 / Real.pi ≤ 2 := by rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
            have hlog_nn : 0 ≤ Real.log (2 * (H : ℝ) + 1) := Real.log_nonneg (by positivity)
            calc (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)
                ≤ 2 * (((R : ℝ) + 3) * Real.log (Real.log (n₁ : ℝ)) + 1) := by gcongr
              _ ≤ 2 * ((R : ℝ) + 4) * (Real.log (Real.log (n₁ : ℝ)) + 1) := by
                  have hll_nn : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith)
                  nlinarith
          have hH1_lb : ((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2) ≤ (H : ℝ) + 1 :=
            (Nat.lt_floor_add_one _).le
          have hlog2P_ub : Real.log (2 * P) ≤ 2 * Real.log (n₁ : ℝ) := by
            have h1 : 2 * P ≤ 2 * (n₁ : ℝ) := by linarith [le_trans hP_lt_y₁.le hy₁_le_n₁]
            have h2 := Real.log_le_log (by positivity) h1
            rw [Real.log_mul (by norm_num) hn₁_pos.ne'] at h2
            have : Real.log 2 ≤ Real.log (n₁ : ℝ) := Real.log_le_log (by norm_num) (by linarith)
            linarith
          have h_inv_H : (4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) ≤
              8 * P * (δ / 2) ^ (-(R : ℤ) - 2) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 1)) := by
            have h1 : ((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2) =
                (δ / 2) ^ (R + 2 : ℤ) * (Real.log (n₁ : ℝ)) ^ (R + 2 : ℕ) := by
              rw [mul_pow]; congr 1; norm_cast
            have hpow_pos : 0 < ((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2) := by positivity
            calc (4 * P * Real.log (2 * P)) / ((H : ℝ) + 1)
                ≤ (4 * P * (2 * Real.log (n₁ : ℝ))) / (((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2)) := by gcongr
              _ = 8 * P * ((δ / 2) ^ (-(R : ℤ) - 2)) * ((Real.log (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ (R + 2)) := by
                  rw [mul_pow, zpow_sub₀ (by positivity), zpow_neg, zpow_natCast, zpow_two]; ring
              _ = 8 * P * (δ / 2) ^ (-(R : ℤ) - 2) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 1)) := by
                  congr 1
                  rw [show (-((R : ℝ) + 1)) = ((-(R + 1 : ℕ) : ℤ) : ℝ) by push_cast; ring,
                    Real.rpow_intCast, zpow_neg, zpow_natCast]
                  have hlog0 : Real.log (n₁ : ℝ) ≠ 0 := hlog_n₁_pos.ne'
                  field_simp [hlog0]; ring
          have hrpow_cmp : (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) ≤ (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 1)) :=
            Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by linarith)
          have hrpow_R1 : (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 1)) ≤ 1 / (Real.log (n₁ : ℝ)) ^ 5 := by
            rw [show (-((R : ℝ) + 1)) = ((-(R + 1 : ℕ) : ℤ) : ℝ) by push_cast; ring,
              Real.rpow_intCast, zpow_neg, zpow_natCast, one_div]
            exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by nlinarith) (by omega))
          have hd_cmp : δ ^ (-(R : ℤ) - 2) ≤ (δ / 2) ^ (-(R : ℤ) - 2) := by
            rw [zpow_sub₀ hδ0.ne', zpow_sub₀ (by positivity), zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
            have h1 : (δ / 2) ^ R ≤ δ ^ R := pow_le_pow_left₀ (by positivity) (by linarith) R
            have h2 : (δ / 2) ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
            gcongr
          have h_n1P_main : ((n₁ : ℝ) / P) * ‖mainC‖ ≤
              (C_osc_const / 10) * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
            have h1 := mul_le_mul_of_nonneg_left h_mainC_bd (by positivity : 0 ≤ (n₁ : ℝ) / P)
            have hL1_sq : L₁ ^ 2 ≤ 4 * ((R : ℝ) + 4) ^ 2 * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 := by
              calc L₁ ^ 2 ≤ (2 * ((R : ℝ) + 4) * (Real.log (Real.log (n₁ : ℝ)) + 1)) ^ 2 :=
                    pow_le_pow_left₀ (by positivity) hL1_ub 2
                _ = 4 * ((R : ℝ) + 4) ^ 2 * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 := by ring
            have hpow_le5 : (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) ≤ 1 / (Real.log (n₁ : ℝ)) ^ 5 :=
              le_trans hrpow_cmp hrpow_R1
            calc ((n₁ : ℝ) / P) * ‖mainC‖
                ≤ ((n₁ : ℝ) / P) * ((4 * ((R : ℝ) + 4) ^ 2 * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2) *
                    (6 * C₂ * P * ((δ / 2) ^ (-(R : ℤ) - 2) + 1) / (Real.log (n₁ : ℝ)) ^ 5)) := by
                    refine le_trans h1 ?_; gcongr
                    · exact le_trans hL1_sq (le_refl _)
                    · exact hpow_le5
              _ = 24 * ((R : ℝ) + 4) ^ 2 * C₂ * ((δ / 2) ^ (-(R : ℤ) - 2) + 1) * (n₁ : ℝ) *
                    (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
                    field_simp [hP_pos.ne']; ring
              _ ≤ (C_osc_const / 10) * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
                    gcongr; dsimp [C_osc_const]; nlinarith [show 0 ≤ ((R : ℝ) + 4) ^ 2 by positivity,
                      show 0 ≤ C₂ by positivity, show 0 ≤ (δ / 2) ^ (-(R : ℤ) - 2) by positivity]
          have h_n1P_err : ((n₁ : ℝ) / P) * ‖errC‖ ≤
              (C_osc_const / 10) * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
            have h1 := mul_le_mul_of_nonneg_left h_errC_bd (by positivity : 0 ≤ (n₁ : ℝ) / P)
            have hL1_le_sq : L₁ ≤ 2 * ((R : ℝ) + 4) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 := by
              have hll1 : 1 ≤ Real.log (Real.log (n₁ : ℝ)) + 1 := by
                have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith); linarith
              calc L₁ ≤ 2 * ((R : ℝ) + 4) * (Real.log (Real.log (n₁ : ℝ)) + 1) := hL1_ub
                _ ≤ 2 * ((R : ℝ) + 4) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 := by gcongr; exact le_self_pow₀ hll1 (by norm_num)
            have h_inner : ((4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) +
                12 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) +
               ((4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) +
                24 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) ≤
                (16 * (δ / 2) ^ (-(R : ℤ) - 2) + 36 * C₂) * P / (Real.log (n₁ : ℝ)) ^ 5 := by
              have hpow_le5 : (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) ≤ 1 / (Real.log (n₁ : ℝ)) ^ 5 :=
                le_trans hrpow_cmp hrpow_R1
              have h_inv_H5 : (4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) ≤
                  8 * P * (δ / 2) ^ (-(R : ℤ) - 2) / (Real.log (n₁ : ℝ)) ^ 5 := by
                calc (4 * P * Real.log (2 * P)) / ((H : ℝ) + 1)
                    ≤ 8 * P * (δ / 2) ^ (-(R : ℤ) - 2) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 1)) := h_inv_H
                  _ ≤ 8 * P * (δ / 2) ^ (-(R : ℤ) - 2) * (1 / (Real.log (n₁ : ℝ)) ^ 5) := by gcongr
                  _ = 8 * P * (δ / 2) ^ (-(R : ℤ) - 2) / (Real.log (n₁ : ℝ)) ^ 5 := by ring
              linarith
            calc ((n₁ : ℝ) / P) * ‖errC‖
                ≤ ((n₁ : ℝ) / P) * (3 * (2 * ((R : ℝ) + 4) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2) *
                    ((16 * (δ / 2) ^ (-(R : ℤ) - 2) + 36 * C₂) * P / (Real.log (n₁ : ℝ)) ^ 5)) := by
                    refine le_trans h1 ?_; gcongr
              _ = 6 * ((R : ℝ) + 4) * (16 * (δ / 2) ^ (-(R : ℤ) - 2) + 36 * C₂) * (n₁ : ℝ) *
                    (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
                    field_simp [hP_pos.ne']; ring
              _ ≤ (C_osc_const / 10) * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
                    gcongr; dsimp [C_osc_const]
                    have hR4 : (R : ℝ) + 4 ≤ ((R : ℝ) + 4) ^ 2 + 1 := by nlinarith
                    nlinarith [show 0 ≤ C₂ by positivity, show 0 ≤ (δ / 2) ^ (-(R : ℤ) - 2) by positivity]
          have h_osc_ball : C_osc_const * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 2 < ε / 100 := by
            have := hN_osc_fin n₁ (by omega)
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this; exact this
          have hlog_div2 : Real.log (n₁ : ℝ) / Real.log 2 + 2 ≤ 4 * Real.log (n₁ : ℝ) := by
            have hlog2_gt : 1 / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
            have h1 : Real.log (n₁ : ℝ) / Real.log 2 ≤ 2 * Real.log (n₁ : ℝ) := by
              rw [div_le_iff₀ (Real.log_pos (by norm_num))]; linarith
            linarith
          calc |∑ p ∈ I_k, _| ≤ ((n₁ : ℝ) / P) * (‖mainC‖ + ‖errC‖) := h_comb
            _ = ((n₁ : ℝ) / P) * ‖mainC‖ + ((n₁ : ℝ) / P) * ‖errC‖ := mul_add _ _ _
            _ ≤ (C_osc_const / 5) * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
                linarith [h_n1P_main, h_n1P_err]
            _ = (1 / (5 * (Real.log (n₁ : ℝ)) ^ 4)) * (n₁ : ℝ) * Real.log (n₁ : ℝ) *
                  (C_osc_const * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 2) := by
                field_simp [hlog_n₁_pos.ne']; ring
            _ ≤ (1 / (5 * (Real.log (n₁ : ℝ)) ^ 4)) * (n₁ : ℝ) * Real.log (n₁ : ℝ) * (ε / 100) := by
                gcongr
            _ ≤ (ε / (16 * (Real.log (n₁ : ℝ) / Real.log 2 + 2))) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
                gcongr
                rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
                have hlog2 : 2 ≤ Real.log (n₁ : ℝ) := by nlinarith
                have hlog4 : 16 ≤ (Real.log (n₁ : ℝ)) ^ 4 := by
                  calc (16 : ℝ) = 2 ^ 4 := by norm_num
                    _ ≤ (Real.log (n₁ : ℝ)) ^ 4 := pow_le_pow_left₀ (by norm_num) hlog2 4
                nlinarith [show 0 ≤ ε by positivity]
        rw [hpart_osc, Finset.sum_biUnion hdisj_osc]
        have hcard_blk : ((dyadicBlocks ((n₁ : ℝ) ^ δ) y₁).card : ℝ) ≤ Real.log (n₁ : ℝ) / Real.log 2 + 2 := by
          have h1 := dyadicBlocks_card_le (by linarith : 1 ≤ (n₁ : ℝ) ^ δ) hy₁_gt.le
          have h2 : Real.log (y₁ / (n₁ : ℝ) ^ δ) ≤ Real.log (n₁ : ℝ) := by
            apply Real.log_le_log (by positivity)
            exact le_trans (div_le_self (by positivity) (by linarith : 1 ≤ (n₁ : ℝ) ^ δ)) hy₁_le_n₁
          exact le_trans h1 (by gcongr)
        calc |∑ k ∈ dyadicBlocks ((n₁ : ℝ) ^ δ) y₁, ∑ p ∈ _, _|
            ≤ ∑ k ∈ dyadicBlocks ((n₁ : ℝ) ^ δ) y₁, |∑ p ∈ _, _| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _k ∈ dyadicBlocks ((n₁ : ℝ) ^ δ) y₁,
                (ε / (16 * (Real.log (n₁ : ℝ) / Real.log 2 + 2))) * (n₁ : ℝ) * Real.log (n₁ : ℝ) :=
              Finset.sum_le_sum hblock_bound
          _ = ((dyadicBlocks ((n₁ : ℝ) ^ δ) y₁).card : ℝ) *
                ((ε / (16 * (Real.log (n₁ : ℝ) / Real.log 2 + 2))) * (n₁ : ℝ) * Real.log (n₁ : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Real.log (n₁ : ℝ) / Real.log 2 + 2) *
                ((ε / (16 * (Real.log (n₁ : ℝ) / Real.log 2 + 2))) * (n₁ : ℝ) * Real.log (n₁ : ℝ)) := by gcongr
          _ = (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
              have hne : Real.log (n₁ : ℝ) / Real.log 2 + 2 ≠ 0 := by positivity
              field_simp [hne]; ring
          _ ≤ (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by gcongr; linarith
      rw [hS_osc_eq]
      have h_osc_lo : (1 / 2 : ℝ) * (n₁ : ℝ) * Real.log (h : ℝ) - (δ / 2) * (n₁ : ℝ) * Real.log (n₁ : ℝ) -
          (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) ≤
          (1 / 2 : ℝ) * ∑ p ∈ I_osc, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) -
          (1 / 2 : ℝ) * ∑ p ∈ I_osc,
            ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
              ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) := by
        have := (abs_le.mp hI_osc_bound).2
        linarith
      have h_osc_hi : (1 / 2 : ℝ) * ∑ p ∈ I_osc, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) -
          (1 / 2 : ℝ) * ∑ p ∈ I_osc,
            ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
              ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) ≤
          (1 / 2 : ℝ) * (n₁ : ℝ) * Real.log (h : ℝ) - (δ / 2) * (n₁ : ℝ) * Real.log (n₁ : ℝ) +
          (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have := (abs_le.mp hI_osc_bound).1
        linarith
      have h_tiny_nn : 0 ≤ ∑ p ∈ S_tiny, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      have h_collar_nn : 0 ≤ ∑ p ∈ S_collar, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      have h_upper_nn : 0 ≤ ∑ p ∈ S_upper, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      rw [abs_le]
      constructor <;> nlinarith [show 0 ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
  dsimp only
  exact ⟨h_branch1, h_branch2⟩

end GrasGreenbergBrocard
