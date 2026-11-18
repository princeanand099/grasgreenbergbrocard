import GrasGreenbergBrocard.Lem6_3ParityFlipOsc

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

set_option maxHeartbeats 4000000

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
  -- Choose N₀ large enough for all asymptotic error terms
  let R := Nat.floor (1 / δ)
  let A_R := 6 * R + 30
  have hR_ge4 : 4 ≤ R := Nat.le_floor (by rw [Nat.cast_ofNat, le_div_iff₀ hδ0]; linarith)
  have hR1_gt : 1 < ((R : ℝ) + 1) * δ := by
    have hlt := Nat.lt_floor_add_one (1 / δ)
    change 1 / δ < (R : ℝ) + 1 at hlt
    exact (div_lt_iff₀ hδ0).mp hlt
  -- Tendsto helpers for error terms -> 0
  have hloglog_div : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => Real.log t / t) Filter.atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
    exact h1.comp Real.tendsto_log_atTop
  have hinv_log : Filter.Tendsto (fun x : ℝ => 1 / Real.log x) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h_err1 : Filter.Tendsto
      (fun n : ℕ => ((A_R : ℝ) + 4) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      Filter.atTop (nhds 0) := by
    have := (hloglog_div.const_mul ((A_R : ℝ) + 4)).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, mul_div_assoc] using this
  have h_err2 : Filter.Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) Filter.atTop (nhds 0) :=
    hinv_log.comp tendsto_natCast_atTop_atTop
  have h_err3 : Filter.Tendsto
      (fun n : ℕ => (Real.log (Real.log (n : ℝ))) ^ 2 / Real.log (n : ℝ))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => (Real.log t) ^ 2 / t) Filter.atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num)
    exact (h1.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (h_err1.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / 100 by positivity)))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    (h_err2.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / (100 * (C_mert + C₂ + 10)) by positivity)))
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp
    (h_err3.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / (1000 * (C₂ + 1) * (δ ^ (-(R : ℤ) - 2) + 1)) by positivity)))
  -- Also need (n₁)^{δ(R+1)} > 2 n₁ and (δ/2 * log n₁)^{R+2} ≥ 100 and ≤ (δ log n₁)^{R+2} / 4
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
          simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
        have hb : Filter.Tendsto (fun t : ℝ => 1 / t) Filter.atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop Filter.tendsto_id
        simpa [add_div] using ha.add hb
      simpa [div_pow] using ht.pow 2
    have h2 := (h1.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, mul_div_assoc] using h2.const_mul C_osc_const
  obtain ⟨N_osc_fin, hN_osc_fin⟩ := Filter.eventually_atTop.mp
    (h_err_osc.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / 100 by positivity)))
  let N₀ := max (max (max N_exp N₁) (max N₂ N₃)) (max (max N₄ N₅) (max N₆ (max N₇ (max N_exp_d (max N_osc_fin 1000)))))
  refine ⟨N₀, by omega, ?_⟩
  intro n₁ n₂ hn₁ hlt h_lt_n₁
  set h := n₂ - n₁
  have hn₁_pos : (0 : ℝ) < n₁ := by exact_mod_cast (by omega : 0 < n₁)
  have hlog_n₁_pos : 0 < Real.log (n₁ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n₁))
  -- Upper range p ≥ y₂ = h * (log n₁)^2 + 2
  let y₂ : ℝ := (h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2 + 2
  have hy₂_ge2 : 2 ≤ y₂ := by dsimp [y₂]; linarith [show (0 : ℝ) ≤ (h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2 by positivity]
  -- Weight on p ≥ y₂ is ≤ 2 n₁ log(2 n₁) / (log n₁)^2
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
        simpa using (padicValNat_dvd_iff_le hP_pos.ne').mpr (Nat.succ_le_of_lt hv_pos)
      · intro p hp
        exact Nat.prime_iff.mp (hS p hp).1
    have hP_le : (P_ratio n₁ n₂ : ℝ) ≤ (2 * (n₁ : ℝ)) ^ h := by
      have hprod_eq : P_ratio n₁ n₂ = ∏ j ∈ Finset.Ioc n₁ n₂, j := by
        have hfac := P_ratio_mul_factorial hlt
        have hprod_all : ∀ m, n₁ ≤ m → Nat.factorial m = Nat.factorial n₁ * ∏ j ∈ Finset.Ioc n₁ m, j := by
          intro m hm
          induction m, hm using Nat.le_induction with
          | base => simp
          | succ k hk ih => rw [Nat.factorial_succ, Finset.prod_Ioc_succ_top hk, ih]; ring
        have hprod := hprod_all n₂ (le_of_lt hlt)
        have : P_ratio n₁ n₂ * Nat.factorial n₁ = (∏ j ∈ Finset.Ioc n₁ n₂, j) * Nat.factorial n₁ := by
          rw [hfac, hprod]; ring
        exact mul_right_cancel₀ (Nat.factorial_pos n₁).ne' this
      rw [hprod_eq]
      have hle_nat : ∏ j ∈ Finset.Ioc n₁ n₂, j ≤ (2 * n₁) ^ h := by
        calc ∏ j ∈ Finset.Ioc n₁ n₂, j
            ≤ ∏ _j ∈ Finset.Ioc n₁ n₂, (2 * n₁) := Finset.prod_le_prod' (fun j hj => by
              have := (Finset.mem_Ioc.mp hj).2; omega)
          _ = (2 * n₁) ^ (Finset.Ioc n₁ n₂).card := Finset.prod_const _
          _ = (2 * n₁) ^ h := by rw [Nat.card_Ioc]
      exact_mod_cast hle_nat
    have hpos_prod : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hS p hp).1.pos)
    have hP_pos : 0 < P_ratio n₁ n₂ := by
      have hmul := P_ratio_mul_factorial hlt
      by_contra h0; have : P_ratio n₁ n₂ = 0 := by omega
      rw [this, zero_mul] at hmul; exact (Nat.factorial_pos n₂).ne' hmul.symm
    have hlog_sum_le : ∑ p ∈ S, Real.log (p : ℝ) ≤ (h : ℝ) * Real.log (2 * (n₁ : ℝ)) := by
      have h1 : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (P_ratio n₁ n₂ : ℝ) := by
        exact_mod_cast Nat.le_of_dvd hP_pos hdvd_P
      have h2 := Real.log_le_log (by exact_mod_cast hpos_prod) (le_trans h1 hP_le)
      rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hS p hp).1.ne_zero),
        Real.log_pow] at h2
      exact h2
    calc (2 * (n₁ : ℝ) / ((h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2)) * ∑ p ∈ S, Real.log (p : ℝ)
        ≤ (2 * (n₁ : ℝ) / ((h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2)) * ((h : ℝ) * Real.log (2 * (n₁ : ℝ))) := by
          gcongr
      _ = 2 * (n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2 := by
          have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
          field_simp [hh0]
  -- Tiny range p ≤ B bound via Mertens_div_p_band_le
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
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_pr.pos)
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
    change ∑ p ∈ S_all, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤ _
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
          have h1n : (1 : ℝ) ≤ (n₁ : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n₁)) hδ0.le
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
          ext p; simp only [Finset.notMem_empty, iff_false]
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
        have : Real.log 2 ≤ Real.log (n₁ : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n₁))
        linarith
      have h1 : 1 / Real.log (n₁ : ℝ) ≤ ε / 40 := by
        have : ε / (100 * (C_mert + C₂ + 10)) ≤ ε / 40 := by
          gcongr; linarith
        linarith
      calc 2 * (n₁ : ℝ) * Real.log (2 * (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2
          ≤ 2 * (n₁ : ℝ) * (2 * Real.log (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ 2 := by gcongr
        _ = 4 * (n₁ : ℝ) / Real.log (n₁ : ℝ) := by field_simp [hlog_n₁_pos'.ne']; ring
        _ = 4 * (1 / Real.log (n₁ : ℝ)) * (n₁ : ℝ) := by ring
        _ ≤ 4 * (ε / 40) * (n₁ : ℝ) := by gcongr
        _ = (ε / 10) * (n₁ : ℝ) := by ring
        _ ≤ (ε / 10) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
            have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
            exact le_mul_of_one_le_right (by positivity) hlog1
    have h_le1_small : 2 * (n₁ : ℝ) * (Real.log ((Real.log (n₁ : ℝ)) ^ 2) + C_mert + 1) ≤
        (ε / 10) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      rw [Real.log_pow, Nat.cast_ofNat]
      have hloglog_le : Real.log (Real.log (n₁ : ℝ)) ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
        have h1 : Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) ≤
            ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) := by
          have hll_nn : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith)
          have hA4 : (1 : ℝ) ≤ (A_R : ℝ) + 4 := by
            have : (4 : ℝ) ≤ A_R := by exact_mod_cast (by omega : 4 ≤ A_R)
            linarith
          exact div_le_div_of_nonneg_right (le_mul_of_one_le_left hll_nn hA4) hlog_n₁_pos.le
        have h2 := (div_lt_iff₀ hlog_n₁_pos').mp (lt_of_le_of_lt h1 herr_ball1)
        linarith
      have hCm_le : C_mert + 1 ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
        have h1 : (C_mert + 1) / Real.log (n₁ : ℝ) ≤ ε / 100 := by
          have := (mul_lt_mul_of_pos_left herr_ball2 (by positivity : 0 < C_mert + 1))
          calc (C_mert + 1) / Real.log (n₁ : ℝ)
              = (C_mert + 1) * (1 / Real.log (n₁ : ℝ)) := by ring
            _ ≤ (C_mert + 1) * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
            _ ≤ ε / 100 := by
                have : (C_mert + 1) / (100 * (C_mert + C₂ + 10)) ≤ 1 / 100 := by
                  rw [div_le_div_iff₀ (by positivity) (by positivity)]
                  nlinarith only [hC_mert_pos, hC₂]
                calc (C_mert + 1) * (ε / (100 * (C_mert + C₂ + 10)))
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
              have hterm1 : (2 / (Real.log (n₁ : ℝ)) ^ 2) * δ ≤ (ε / 20) * (1 / 4) :=
                mul_le_mul h2_div hδ1 hδ0.le (by positivity)
              have hterm2 : (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (ε / 10) ≤ 2 * (ε / 10) := by
                nlinarith only [ha_le1, hε]
              exact mul_le_mul_of_nonneg_right (by linarith only [hterm1, hterm2]) hlog_n₁_pos.le
          _ ≤ (δ + ε / 2) * Real.log (n₁ : ℝ) := mul_le_mul_of_nonneg_right (by linarith only [hε]) hlog_n₁_pos.le
      calc (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) *
            (δ * Real.log (n₁ : ℝ) + Real.log (3 : ℝ) + C_mert)
          = (n₁ : ℝ) * ((1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) *
              (δ * Real.log (n₁ : ℝ) + Real.log (3 : ℝ) + C_mert)) := by ring
        _ ≤ (n₁ : ℝ) * ((δ + ε / 2) * Real.log (n₁ : ℝ)) := by gcongr
        _ = (δ + ε / 2) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
    linarith only [hS_gt_ub, hS_le1_ub, hS_le2_ub, hS_le_eq, h_gt_small, h_le1_small, h_le2_small,
      show 0 ≤ ε * (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
  -- Now prove h_branch2: (n₁ : ℝ) ^ δ < (h : ℝ)
  have h_branch2 : (n₁ : ℝ) ^ δ < (h : ℝ) →
      |parityFlipWeight n₁ n₂ - (1 / 2 : ℝ) * (n₁ : ℝ) * Real.log (h : ℝ)| ≤
        (δ + ε) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
    intro hh_gt
    -- Subcase A: h ≤ n₁^δ * (log n₁)^(A_R + 2)
    by_cases hh_small : (h : ℝ) ≤ (n₁ : ℝ) ^ δ * (Real.log (n₁ : ℝ)) ^ (A_R + 2)
    · have hy₂_le : y₂ ≤ 3 * (n₁ : ℝ) ^ δ * (Real.log (n₁ : ℝ)) ^ (A_R + 4) := by
        dsimp [y₂]
        have h1n : (1 : ℝ) ≤ (n₁ : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n₁)) hδ0.le
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
        change ∑ p ∈ S_all, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤ _
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
              ext p; simp only [Finset.notMem_empty, iff_false]
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
            have : Real.log 2 ≤ Real.log (n₁ : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n₁))
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
                have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
                exact le_mul_of_one_le_right (by positivity) hlog1
        have h_le1_small : 2 * (n₁ : ℝ) * (Real.log ((Real.log (n₁ : ℝ)) ^ 2) + C_mert + 1) ≤
            (ε / 10) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          rw [Real.log_pow, Nat.cast_ofNat]
          have hloglog_le : Real.log (Real.log (n₁ : ℝ)) ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
            have h1 : Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) ≤
                ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) := by
              have hll_nn : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith)
              have hA4 : (1 : ℝ) ≤ (A_R : ℝ) + 4 := by linarith only [show (0 : ℝ) ≤ A_R from Nat.cast_nonneg _]
              exact div_le_div_of_nonneg_right (le_mul_of_one_le_left hll_nn hA4) hlog_n₁_pos.le
            have h2 := (div_lt_iff₀ hlog_n₁_pos).mp (lt_of_le_of_lt h1 herr_ball1)
            linarith
          have hCm_le : C_mert + 1 ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
            have h1 : (C_mert + 1) / Real.log (n₁ : ℝ) ≤ ε / 100 := by
              calc (C_mert + 1) / Real.log (n₁ : ℝ)
                  = (C_mert + 1) * (1 / Real.log (n₁ : ℝ)) := by ring
                _ ≤ (C_mert + 1) * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
                _ ≤ ε / 100 := by
                    have : (C_mert + 1) / (100 * (C_mert + C₂ + 10)) ≤ 1 / 100 := by
                      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [hC_mert_pos, hC₂]
                    calc (C_mert + 1) * (ε / (100 * (C_mert + C₂ + 10)))
                        = ε * ((C_mert + 1) / (100 * (C_mert + C₂ + 10))) := by ring
                      _ ≤ ε * (1 / 100) := by gcongr
                      _ = ε / 100 := by ring
            exact (div_le_iff₀ hlog_n₁_pos).mp h1
          nlinarith only [hloglog_le, hCm_le, hn₁_pos, hlog_n₁_pos]
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
                      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [hC_mert1_pos, hC_mert_pos, hC₂]
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
                  have hterm1 : (2 / (Real.log (n₁ : ℝ)) ^ 2) * δ ≤ (ε / 20) * (1 / 4) :=
                    mul_le_mul ha_eps hδ1 hδ0.le (by positivity)
                  have hterm2 : (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (ε / 10) ≤ 2 * (ε / 10) := by
                    nlinarith only [ha_le1, hε]
                  exact mul_le_mul_of_nonneg_right (by linarith only [hterm1, hterm2]) hlog_n₁_pos.le
              _ ≤ (δ + ε / 4) * Real.log (n₁ : ℝ) := mul_le_mul_of_nonneg_right (by linarith only [hε]) hlog_n₁_pos.le
          calc (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) *
                (δ * Real.log (n₁ : ℝ) + ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) + Real.log 3 + C_mert)
              = (n₁ : ℝ) * ((1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) *
                  (δ * Real.log (n₁ : ℝ) + ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) + Real.log 3 + C_mert)) := by ring
            _ ≤ (n₁ : ℝ) * ((δ + ε / 4) * Real.log (n₁ : ℝ)) := by gcongr
            _ = (δ + ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
        linarith only [hS_gt_ub, hS_le1_ub, hS_le2_ub, hS_le_eq, h_gt_small, h_le1_small, h_le2_small,
          show 0 ≤ ε * (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
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
          have hll_nn : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith only [hlog_ge3])
          linarith only [h2, hll_nn]
        linarith
      rw [abs_le]; constructor <;> nlinarith only [hpf_ub, hpf_nn, hlogh_lb, hlogh_ub, hn₁_pos, hlog_n₁_pos, hδ0, hδ1, hε]
    -- Subcase B: h > n₁^δ * (log n₁)^(A_R + 2)
    · push Not at hh_small
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
          have h1 : Real.exp 2 ≤ Real.exp (δ * Real.log (n₁ : ℝ)) := Real.exp_le_exp.mpr (by linarith)
          have h2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
          have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          nlinarith
        rwa [Real.rpow_def_of_pos hn₁_pos, mul_comm]
      unfold parityFlipWeight
      let S_all := (Finset.Icc 3 n₁).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (P_ratio n₁ n₂))
      let S_tiny := S_all.filter (fun p : ℕ => (p : ℝ) ≤ (n₁ : ℝ) ^ δ)
      let S_osc := S_all.filter (fun p : ℕ => (n₁ : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ≤ y₁)
      let S_collar := S_all.filter (fun p : ℕ => y₁ < (p : ℝ) ∧ (p : ℝ) < y₂)
      let S_upper := S_all.filter (fun p : ℕ => y₂ ≤ (p : ℝ))
      have hy₁_pos : 0 < y₁ := lt_trans (by positivity) hy₁_gt
      have hh_pos : (0 : ℝ) < h := lt_trans (by positivity) hh_gt
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
      -- 1. S_tiny ≤ (δ + ε/8) n₁ log n₁
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
              ext p; simp only [Finset.notMem_empty, iff_false]
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
            (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          rw [Real.log_pow, Nat.cast_ofNat]
          have hll : Real.log (Real.log (n₁ : ℝ)) ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
            have h1 : Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) ≤
                ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) / Real.log (n₁ : ℝ) := by
              have hll_nn : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith)
              have hA4 : (1 : ℝ) ≤ (A_R : ℝ) + 4 := by linarith only [show (0 : ℝ) ≤ A_R from Nat.cast_nonneg _]
              exact div_le_div_of_nonneg_right (le_mul_of_one_le_left hll_nn hA4) hlog_n₁_pos.le
            linarith [(div_lt_iff₀ hlog_n₁_pos).mp (lt_of_le_of_lt h1 herr1)]
          have hCm : C_mert + 1 ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
            have h1 : (C_mert + 1) / Real.log (n₁ : ℝ) ≤ ε / 100 := by
              calc (C_mert + 1) / Real.log (n₁ : ℝ) = (C_mert + 1) * (1 / Real.log (n₁ : ℝ)) := by ring
                _ ≤ (C_mert + 1) * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
                _ ≤ ε / 100 := by
                    have : (C_mert + 1) / (100 * (C_mert + C₂ + 10)) ≤ 1 / 100 := by
                      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [hC_mert_pos, hC₂]
                    calc (C_mert + 1) * (ε / (100 * (C_mert + C₂ + 10)))
                        = ε * ((C_mert + 1) / (100 * (C_mert + C₂ + 10))) := by ring
                      _ ≤ ε * (1 / 100) := by gcongr
                      _ = ε / 100 := by ring
            exact (div_le_iff₀ hlog_n₁_pos).mp h1
          calc 2 * (n₁ : ℝ) * (2 * Real.log (Real.log (n₁ : ℝ)) + C_mert + 1)
              ≤ 2 * (n₁ : ℝ) * (2 * ((ε / 100) * Real.log (n₁ : ℝ)) + (ε / 100) * Real.log (n₁ : ℝ)) := by
                gcongr
            _ = (3 * ε / 50) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) := by ring
            _ ≤ (ε / 16) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) :=
              mul_le_mul_of_nonneg_right (by linarith only [hε]) (mul_nonneg hn₁_pos.le hlog_n₁_pos.le)
            _ = (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
        have ht2_sm : (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) * (δ * Real.log (n₁ : ℝ) + C_mert) ≤
            (δ + ε / 20) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          have ha1 : 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; linarith only [hlog_ge3]
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
                      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [hC_mert1_pos, hC_mert_pos, hC₂]
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
              _ ≤ (δ + (ε / 40) * (1 / 4) + 2 * (ε / 100)) * Real.log (n₁ : ℝ) := by
                have hterm1 : (2 / (Real.log (n₁ : ℝ)) ^ 2) * δ ≤ (ε / 40) * (1 / 4) :=
                  mul_le_mul ha_eps hδ1 hδ0.le (by positivity)
                have hterm2 : (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (ε / 100) ≤ 2 * (ε / 100) := by
                  nlinarith
                exact mul_le_mul_of_nonneg_right (by linarith) hlog_n₁_pos.le
              _ ≤ (δ + ε / 20) * Real.log (n₁ : ℝ) := mul_le_mul_of_nonneg_right (by linarith only [hε]) hlog_n₁_pos.le
          calc (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) * (δ * Real.log (n₁ : ℝ) + C_mert)
              = (n₁ : ℝ) * ((1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (δ * Real.log (n₁ : ℝ) + C_mert)) := by ring
            _ ≤ (n₁ : ℝ) * ((δ + ε / 20) * Real.log (n₁ : ℝ)) := by gcongr
            _ = (δ + ε / 20) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
        have h_comb_tiny : (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) +
            (δ + ε / 20) * (n₁ : ℝ) * Real.log (n₁ : ℝ) ≤
            (δ + ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          have h1 : ε / 16 + (δ + ε / 20) ≤ δ + ε / 8 := by linarith only [hε]
          calc (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) + (δ + ε / 20) * (n₁ : ℝ) * Real.log (n₁ : ℝ)
              = (ε / 16 + (δ + ε / 20)) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) := by ring
            _ ≤ (δ + ε / 8) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) :=
              mul_le_mul_of_nonneg_right h1 (mul_nonneg hn₁_pos.le hlog_n₁_pos.le)
            _ = (δ + ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
        linarith only [ht1, ht2, ht1_sm, ht2_sm, h_comb_tiny]
      have hlog2_le_ndelta : (Real.log (n₁ : ℝ)) ^ 2 ≤ (n₁ : ℝ) ^ δ := by
        have h6 := hN₆ n₁ (by omega)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h6
        exact (div_lt_one (by positivity)).mp h6 |>.le
      -- 2. S_collar ≤ (ε/8) n₁ log n₁
      have hS_collar_ub : ∑ p ∈ S_collar, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
          (ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have hsub : S_collar ⊆ ((Finset.Icc 3 (Nat.floor y₂)).filter Nat.Prime).filter (fun p : ℕ => y₁ < (p : ℝ)) := by
          intro p hp; simp only [S_collar, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨⟨⟨hp.1.1.1, Nat.le_floor hp.2.2.le⟩, hp.1.2.1⟩, hp.2.1⟩
        have h1 := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
          (h_band_exact y₁ y₂ (le_trans hlog2_le_ndelta hy₁_gt.le) hy₁_lt_y₂.le)
        have hy_ratio : y₂ / y₁ ≤ 3 * (Real.log (n₁ : ℝ)) ^ (A_R + 4) := by
          have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith only [hlog_n₁_pos, hlog_ge3]
          have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
          have hy2_le : y₂ ≤ 3 * (h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2 := by
            have h1 : (2 : ℝ) ≤ 2 * (h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2 := by
              have hsq1 : (1 : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ 2 := by linarith only [hlog_ge3]
              calc (2 : ℝ) = 2 * 1 * 1 := by norm_num
                _ ≤ 2 * (h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2 := by gcongr
            dsimp [y₂]; linarith only [h1]
          rw [div_le_iff₀ (by positivity)]
          have hpow_eq : (Real.log (n₁ : ℝ)) ^ (A_R + 4) =
              (Real.log (n₁ : ℝ)) ^ (A_R + 2) * (Real.log (n₁ : ℝ)) ^ 2 := by
            rw [← pow_add]
          have hne : (Real.log (n₁ : ℝ)) ^ (A_R + 2) ≠ 0 := by positivity
          calc y₂ ≤ 3 * (h : ℝ) * (Real.log (n₁ : ℝ)) ^ 2 := hy2_le
            _ = 3 * (Real.log (n₁ : ℝ)) ^ (A_R + 4) * y₁ := by
                dsimp [y₁]; rw [hpow_eq]; field_simp [hne]
        have hlog_ratio : Real.log (y₂ / y₁) ≤ ((A_R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) + Real.log 3 := by
          have h2 := Real.log_le_log (div_pos (by positivity) hy₁_pos) hy_ratio
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
                    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [hC_mert1_pos, hC_mert_pos, hC₂]
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
          _ ≤ 2 * (n₁ : ℝ) * ((ε / 100 + ε / 50) * Real.log (n₁ : ℝ)) := by
            have hlog_nn : 0 ≤ Real.log (y₂ / y₁) + C_mert := by
              have hy_ge1 : 1 ≤ y₂ / y₁ := (one_le_div hy₁_pos).mpr hy₁_lt_y₂.le
              have := Real.log_nonneg hy_ge1
              linarith only [this, hC_mert_pos]
            gcongr; linarith only [hlog_ratio, herr1, herr2]
          _ ≤ (ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
              have : 2 * (ε / 100 + ε / 50) ≤ ε / 8 := by linarith
              nlinarith [show 0 ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
      -- 3. S_upper ≤ (ε/8) n₁ log n₁
      have hS_upper_ub : ∑ p ∈ S_upper, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) ≤
          (ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have h1 := h_upper_bound S_upper (fun p hp => by
          simp only [S_upper, S_all, Finset.mem_filter, Finset.mem_Icc] at hp
          exact ⟨hp.1.2.1, hp.1.1.1, hp.1.1.2, hp.2, hp.1.2.2⟩)
        have hlog2n : Real.log (2 * (n₁ : ℝ)) ≤ 2 * Real.log (n₁ : ℝ) := by
          rw [Real.log_mul (by norm_num) hn₁_pos.ne']
          have : Real.log 2 ≤ Real.log (n₁ : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n₁))
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
              have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
              calc 4 * (ε / 40) * (n₁ : ℝ) = (ε / 10) * (n₁ : ℝ) := by ring
                _ ≤ (ε / 8) * (n₁ : ℝ) := by nlinarith only [hε, hn₁_pos]
                _ ≤ (ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := le_mul_of_one_le_right (by positivity) hlog1
      -- 4. S_osc = (1/2) n₁ log h - (δ/2) n₁ log n₁ ± (ε/4) n₁ log n₁
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
      -- Main term upper & lower bounds
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
            dsimp [y₁]; exact div_le_self (by positivity) (one_le_pow₀ (by nlinarith only [hlog_ge3, hlog_n₁_pos]))
          have hnd_pos : (0 : ℝ) < (n₁ : ℝ) ^ δ := by positivity
          have h2 := Real.log_le_log (div_pos hy₁_pos hnd_pos) (div_le_div_of_nonneg_right hy1_le_h hnd_pos.le)
          rw [Real.log_div hy₁_pos.ne' hnd_pos.ne', Real.log_div hh_pos.ne' hnd_pos.ne', Real.log_rpow hn₁_pos] at h2
          rw [Real.log_div hy₁_pos.ne' hnd_pos.ne', Real.log_rpow hn₁_pos]
          exact h2
        have hCm : C_mert ≤ (ε / 20) * Real.log (n₁ : ℝ) := by
          have h2 := hN₂ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
          have h3 : C_mert / Real.log (n₁ : ℝ) ≤ ε / 20 := by
            calc C_mert / Real.log (n₁ : ℝ) = C_mert * (1 / Real.log (n₁ : ℝ)) := by ring
              _ ≤ C_mert * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
              _ ≤ ε / 20 := by
                  have : C_mert / (100 * (C_mert + C₂ + 10)) ≤ 1 / 20 := by
                    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [hC_mert1_pos, hC_mert_pos, hC₂]
                  calc C_mert * (ε / (100 * (C_mert + C₂ + 10)))
                      = ε * (C_mert / (100 * (C_mert + C₂ + 10))) := by ring
                    _ ≤ ε * (1 / 20) := by gcongr
                    _ = ε / 20 := by ring
          exact (div_le_iff₀ hlog_n₁_pos).mp h3
        have ha_eps : 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ ε / 20 := by
          have h2 := hN₂ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
          have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith only [hlog_ge3, hlog_n₁_pos]
          calc 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ 2 / Real.log (n₁ : ℝ) := by gcongr; nlinarith only [hlog1]
            _ = 2 * (1 / Real.log (n₁ : ℝ)) := by ring
            _ ≤ 2 * (ε / (100 * (C_mert + C₂ + 10))) := by gcongr
            _ ≤ ε / 20 := by
                have : 2 / (100 * (C_mert + C₂ + 10)) ≤ 1 / 20 := by
                  rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [hC_mert_pos, hC₂]
                calc 2 * (ε / (100 * (C_mert + C₂ + 10)))
                    = ε * (2 / (100 * (C_mert + C₂ + 10))) := by ring
                  _ ≤ ε * (1 / 20) := by gcongr
                  _ = ε / 20 := by ring
        have ha1 : 2 / (Real.log (n₁ : ℝ)) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        have hdiff_nn : 0 ≤ Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) := by
          have := Real.log_le_log (by positivity) hh_gt.le
          rw [Real.log_rpow hn₁_pos] at this; linarith only [this]
        have hdiff_le : Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) ≤ Real.log (n₁ : ℝ) := by
          have : Real.log (h : ℝ) ≤ Real.log (n₁ : ℝ) := Real.log_le_log hh_pos (by exact_mod_cast le_of_lt h_lt_n₁)
          linarith only [this, show 0 ≤ δ * Real.log (n₁ : ℝ) by positivity]
        calc ∑ p ∈ I_osc, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)
            ≤ (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) * (Real.log (y₁ / (n₁ : ℝ) ^ δ) + C_mert) := h1
          _ ≤ (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * (n₁ : ℝ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) + C_mert) := by gcongr
          _ = (n₁ : ℝ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ)) +
              (n₁ : ℝ) * ((2 / (Real.log (n₁ : ℝ)) ^ 2) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ)) +
                (1 + 2 / (Real.log (n₁ : ℝ)) ^ 2) * C_mert) := by ring
          _ ≤ (n₁ : ℝ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ)) +
              (n₁ : ℝ) * ((ε / 20) * Real.log (n₁ : ℝ) + 2 * ((ε / 20) * Real.log (n₁ : ℝ))) := by gcongr; linarith only [ha1]
          _ ≤ (n₁ : ℝ) * Real.log (h : ℝ) - δ * (n₁ : ℝ) * Real.log (n₁ : ℝ) + (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
              have h_nl : 0 ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) := by positivity
              have h_err : (n₁ : ℝ) * (ε / 20 * Real.log (n₁ : ℝ) + 2 * (ε / 20 * Real.log (n₁ : ℝ))) ≤
                  (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by nlinarith only [h_nl, hε]
              linarith only [h_err]
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
            rcases Nat.eq_zero_or_pos (Nat.log p n₁) with hlog0 | hlog_pos
            · have hn1_lt_p : n₁ < p := by
                by_contra hge; push Not at hge
                have : 1 ≤ Nat.log p n₁ := Nat.log_pos hp_pr.one_lt hge
                omega
              rw [Nat.div_eq_of_lt hn1_lt_p]; exact Nat.zero_le _
            · have hmem : 1 ∈ Finset.Ico 1 (Nat.log p n₁ + 1) := Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩
              simpa using Finset.single_le_sum (f := fun i => n₁ / p ^ i) (fun _ _ => Nat.zero_le _) hmem
          have hv_real : (n₁ : ℝ) / (p : ℝ) - 1 ≤ (padicValNat p (Nat.factorial n₁) : ℝ) := by
            have h1 : (n₁ : ℝ) / (p : ℝ) - 1 < ((n₁ / p : ℕ) : ℝ) := by
              have hlt_nat : n₁ < (n₁ / p + 1) * p := by
                rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hp_pr.pos
              have hlt_r : (n₁ : ℝ) < (((n₁ / p : ℕ) : ℝ) + 1) * (p : ℝ) := by exact_mod_cast hlt_nat
              rw [sub_lt_iff_lt_add, div_lt_iff₀ hp_pos]; exact hlt_r
            linarith only [h1, show ((n₁ / p : ℕ) : ℝ) ≤ (padicValNat p (Nat.factorial n₁) : ℝ) from by exact_mod_cast hv1]
          have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_pr.pos)
          calc (n₁ : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) - Real.log (p : ℝ)
              = ((n₁ : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) := by ring
            _ ≤ (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) := by gcongr
        refine le_trans ?_ (Finset.sum_le_sum hterm)
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        have hn₁_d_nn : (0 : ℝ) ≤ (n₁ : ℝ) ^ δ := Real.rpow_nonneg hn₁_pos.le _
        have hdisj_i : Disjoint I_osc ((Finset.Icc 3 (Nat.floor ((n₁ : ℝ) ^ δ))).filter Nat.Prime) := by
          rw [Finset.disjoint_left]; intro p h1 h2
          simp only [I_osc, Finset.mem_filter, Finset.mem_Icc] at h1 h2
          have : (p : ℝ) ≤ (n₁ : ℝ) ^ δ := (Nat.le_floor_iff hn₁_d_nn).mp h2.1.2
          linarith only [h1.2.1, this]
        have hun_i : (Finset.Icc 3 (Nat.floor y₁)).filter Nat.Prime =
            I_osc ∪ (Finset.Icc 3 (Nat.floor ((n₁ : ℝ) ^ δ))).filter Nat.Prime := by
          ext p; simp only [Finset.mem_union, I_osc, Finset.mem_filter, Finset.mem_Icc]
          constructor
          · intro hp
            by_cases hle : (p : ℝ) ≤ (n₁ : ℝ) ^ δ
            · exact Or.inr ⟨⟨hp.1.1, Nat.le_floor hle⟩, hp.2⟩
            · refine Or.inl ⟨⟨⟨hp.1.1, le_trans hp.1.2 (by simpa [Nat.floor_natCast] using Nat.floor_le_floor hy₁_le_n₁)⟩, hp.2⟩,
                lt_of_not_ge hle, (Nat.le_floor_iff hy₁_pos.le).mp hp.1.2⟩
          · rintro (hp | hp)
            · exact ⟨⟨hp.1.1.1, Nat.le_floor hp.2.2⟩, hp.1.2⟩
            · exact ⟨⟨hp.1.1, Nat.le_floor (le_trans ((Nat.le_floor_iff hn₁_d_nn).mp hp.1.2) hy₁_gt.le)⟩, hp.2⟩
        have hI_eq_diff : ∑ p ∈ I_osc, Real.log (p : ℝ) / (p : ℝ) =
            (∑ p ∈ (Finset.Icc 3 (Nat.floor y₁)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) -
            (∑ p ∈ (Finset.Icc 3 (Nat.floor ((n₁ : ℝ) ^ δ))).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) := by
          rw [hun_i, Finset.sum_union hdisj_i, add_sub_cancel_right]
        have h_p_pm1 : (1 - 1 / (n₁ : ℝ) ^ δ) *
            ∑ p ∈ I_osc, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤
            ∑ p ∈ I_osc, Real.log (p : ℝ) / (p : ℝ) := by
          have hn₁_d_pos : (0 : ℝ) < (n₁ : ℝ) ^ δ := by positivity
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro p hp
          have hp_mem := Finset.mem_filter.mp hp
          have hp_pr := (Finset.mem_filter.mp hp_mem.1).2
          have hp_gt : (n₁ : ℝ) ^ δ < (p : ℝ) := hp_mem.2.1
          have hp3 : (3 : ℝ) < (p : ℝ) := lt_of_le_of_lt hn₁_delta_ge3 hp_gt
          have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith only [hp3])
          have hratio : (1 - 1 / (n₁ : ℝ) ^ δ) / ((p : ℝ) - 1) ≤ 1 / (p : ℝ) := by
            rw [div_le_div_iff₀ (by linarith only [hp3]) (by linarith only [hp3])]
            have h1 : 1 / (p : ℝ) ≤ 1 / (n₁ : ℝ) ^ δ := one_div_le_one_div_of_le hn₁_d_pos hp_gt.le
            calc (1 - 1 / (n₁ : ℝ) ^ δ) * (p : ℝ) ≤ (1 - 1 / (p : ℝ)) * (p : ℝ) := by gcongr
              _ = (p : ℝ) - 1 := by field_simp [(by linarith only [hp3] : (p : ℝ) ≠ 0)]
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
            rw [hun_i, Finset.sum_union hdisj_i, add_sub_cancel_right]
          rw [hsum_eq, Real.log_div hy₁_pos.ne' (by positivity)]
          linarith only [hm1.1, hm2.2]
        have hsum_log_I : ∑ p ∈ I_osc, Real.log (p : ℝ) ≤ (n₁ : ℝ) := by
          have hcard : (I_osc.card : ℝ) ≤ y₁ := by
            have hsub : I_osc ⊆ Finset.Icc 1 (Nat.floor y₁) := by
              intro p hp; simp only [I_osc, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
              exact ⟨by omega, Nat.le_floor hp.2.2⟩
            exact le_trans (by exact_mod_cast le_trans (Finset.card_le_card hsub) (by simp)) (Nat.floor_le (by positivity))
          have hterm_log : ∀ p ∈ I_osc, Real.log (p : ℝ) ≤ Real.log (n₁ : ℝ) := by
            intro p hp; simp only [I_osc, Finset.mem_filter, Finset.mem_Icc] at hp
            exact Real.log_le_log (by exact_mod_cast hp.1.2.pos) (by exact_mod_cast hp.1.1.2)
          calc ∑ p ∈ I_osc, Real.log (p : ℝ) ≤ (I_osc.card : ℝ) * Real.log (n₁ : ℝ) := by
                simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hterm_log
            _ ≤ y₁ * Real.log (n₁ : ℝ) :=
                mul_le_mul_of_nonneg_right hcard hlog_n₁_pos.le
            _ ≤ ((n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2)) * Real.log (n₁ : ℝ) := by
                refine mul_le_mul_of_nonneg_right ?_ hlog_n₁_pos.le
                exact div_le_div_of_nonneg_right (by exact_mod_cast le_of_lt h_lt_n₁) (by positivity)
            _ ≤ (n₁ : ℝ) := by
                have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith
                have hpow : Real.log (n₁ : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 2) :=
                  le_self_pow₀ hlog1 (by omega)
                rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
                exact mul_le_mul_of_nonneg_left hpow (by positivity)
        have h_log_y1 : Real.log (y₁ / (n₁ : ℝ) ^ δ) =
            Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - ((A_R : ℝ) + 2) * Real.log (Real.log (n₁ : ℝ)) := by
          dsimp [y₁]
          rw [Real.log_div (div_ne_zero hh_pos.ne' (by positivity)) (by positivity),
            Real.log_div hh_pos.ne' (by positivity),
            Real.log_rpow hn₁_pos, Real.log_pow]
          push_cast; ring
        have herr1 : ((A_R : ℝ) + 2) * Real.log (Real.log (n₁ : ℝ)) ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
          have := hN₁ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
            have : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith); positivity)] at this
          have h2 := (div_lt_iff₀ hlog_n₁_pos).mp this
          have hll_nn : 0 ≤ Real.log (Real.log (n₁ : ℝ)) := Real.log_nonneg (by nlinarith only [hlog_ge3])
          linarith only [h2, hll_nn]
        have hCm1 : 2 * C_mert1 ≤ (ε / 50) * Real.log (n₁ : ℝ) := by
          have h7 := hN₇ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h7
          have h3 : 2 * C_mert1 / Real.log (n₁ : ℝ) ≤ ε / 50 := by
            calc 2 * C_mert1 / Real.log (n₁ : ℝ) = 2 * C_mert1 * (1 / Real.log (n₁ : ℝ)) := by ring
              _ ≤ 2 * C_mert1 * (ε / (100 * (C_mert1 + C_mert + C₂ + 10))) := by gcongr
              _ ≤ ε / 50 := by
                  have : 2 * C_mert1 / (100 * (C_mert1 + C_mert + C₂ + 10)) ≤ 1 / 50 := by
                    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [hC_mert1_pos, hC_mert_pos, hC₂]
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
            _ ≤ ε / 20 := by gcongr; linarith only [hC_mert1_pos, hC_mert_pos, hC₂]
        have h_1n_le : (n₁ : ℝ) ≤ (ε / 100) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          have h7 := hN₇ n₁ (by omega)
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h7
          have h1 : 1 ≤ (ε / 100) * Real.log (n₁ : ℝ) := by
            have : 1 / Real.log (n₁ : ℝ) ≤ ε / 100 := le_trans h7.le (by gcongr; linarith)
            exact (div_le_iff₀ hlog_n₁_pos).mp this
          nlinarith only [h1, hn₁_pos]
        have h_lb1 : Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - (ε / 20) * Real.log (n₁ : ℝ) ≤
            ∑ p ∈ I_osc, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
          rw [h_log_y1] at hmert_osc_lb
          have h_e : ((A_R : ℝ) + 2) * Real.log (Real.log (n₁ : ℝ)) + 2 * C_mert1 ≤
              (ε / 20) * Real.log (n₁ : ℝ) := by
            nlinarith only [herr1, hCm1, hε, hlog_n₁_pos]
          linarith only [hmert_osc_lb, h_e]
        have h_lb1_nn : 0 ≤ Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) := by
          have := Real.log_le_log (by positivity) hh_gt.le
          rw [Real.log_rpow hn₁_pos] at this; linarith
        have h_lb1_ub : Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) ≤ Real.log (n₁ : ℝ) := by
          have : Real.log (h : ℝ) ≤ Real.log (n₁ : ℝ) := Real.log_le_log hh_pos (by exact_mod_cast le_of_lt h_lt_n₁)
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
            · push Not at hneg
              calc (1 / (n₁ : ℝ) ^ δ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - (ε / 20) * Real.log (n₁ : ℝ))
                  ≤ (ε / 20) * Real.log (n₁ : ℝ) := mul_le_mul h_one_sub hdiff_le hneg.le (by positivity)
          linarith only [this]
        have h_prod1 : (n₁ : ℝ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - (ε / 10) * Real.log (n₁ : ℝ)) ≤
            (n₁ : ℝ) * ∑ p ∈ I_osc, Real.log (p : ℝ) / (p : ℝ) :=
          mul_le_mul_of_nonneg_left (le_trans h_est h_sub_prod) hn₁_pos.le
        have h_sub1 : (n₁ : ℝ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - (ε / 10) * Real.log (n₁ : ℝ)) -
            (ε / 100) * (n₁ : ℝ) * Real.log (n₁ : ℝ) ≤
            (n₁ : ℝ) * ∑ p ∈ I_osc, Real.log (p : ℝ) / (p : ℝ) - ∑ p ∈ I_osc, Real.log (p : ℝ) := by
          linarith only [h_prod1, hsum_log_I, h_1n_le]
        have h_final_lb : (n₁ : ℝ) * Real.log (h : ℝ) - δ * (n₁ : ℝ) * Real.log (n₁ : ℝ) -
            (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) ≤
            (n₁ : ℝ) * (Real.log (h : ℝ) - δ * Real.log (n₁ : ℝ) - (ε / 10) * Real.log (n₁ : ℝ)) -
              (ε / 100) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          nlinarith only [hε, hn₁_pos, hlog_n₁_pos]
        exact le_trans h_final_lb h_sub1
      have hI_osc_bound : |∑ p ∈ I_osc,
          ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
            ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ))| ≤
          (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        refine lem_6_3_osc_bound δ hδ0 hδ1 ε hε C₂ hC₂ N_exp ?_ hR_ge4 N₅ N_exp_d N_osc_fin
          hN₅ hN_exp_d hN_osc_fin n₁ n₂ (by omega) (by omega) (by omega) (by omega) (by omega) hlog_ge3 hlt h_lt_n₁
          hn₁_pos hlog_n₁_pos hh_gt hy₁_gt hy₁_le_n₁ hn₁_delta_ge3
        intro b hb P I hm1 w W₀ hPb hPb2 hIb hm1_nz hm1_bd hTb hw hW₀
        exact ((hN_exp b hb) P I {1} (fun _ => hm1) w W₀ ⟨1, Finset.mem_singleton_self 1, hm1_nz⟩
          hPb hPb2 hIb
          (fun r hr => by rw [Finset.mem_singleton] at hr; subst hr; exact ⟨le_refl 1, by omega⟩)
          (fun r hr => by rw [Finset.mem_singleton] at hr; subst hr; exact hm1_bd)
          (fun r hr => by rw [Finset.mem_singleton] at hr; subst hr; simpa using hTb)
          hw hW₀).1.2
      rw [hS_osc_eq]
      have h_osc_lo : (1 / 2 : ℝ) * (n₁ : ℝ) * Real.log (h : ℝ) - (δ / 2) * (n₁ : ℝ) * Real.log (n₁ : ℝ) -
          (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) ≤
          (1 / 2 : ℝ) * ∑ p ∈ I_osc, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) -
          (1 / 2 : ℝ) * ∑ p ∈ I_osc,
            ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
              ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) := by
        have := (abs_le.mp hI_osc_bound).2
        linarith only [this, hI_main_lb]
      have h_osc_hi : (1 / 2 : ℝ) * ∑ p ∈ I_osc, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) -
          (1 / 2 : ℝ) * ∑ p ∈ I_osc,
            ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
              ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) ≤
          (1 / 2 : ℝ) * (n₁ : ℝ) * Real.log (h : ℝ) - (δ / 2) * (n₁ : ℝ) * Real.log (n₁ : ℝ) +
          (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have := (abs_le.mp hI_osc_bound).1
        linarith only [this, hI_main_ub]
      have h_tiny_nn : 0 ≤ ∑ p ∈ S_tiny, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      have h_collar_nn : 0 ≤ ∑ p ∈ S_collar, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      have h_upper_nn : 0 ≤ ∑ p ∈ S_upper, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) :=
        Finset.sum_nonneg (fun _ _ => by positivity)
      have h_ub_tot : ∑ p ∈ S_tiny, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) +
          ∑ p ∈ S_osc, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) +
          ∑ p ∈ S_collar, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) +
          ∑ p ∈ S_upper, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) -
          (1 / 2 : ℝ) * (n₁ : ℝ) * Real.log (h : ℝ) ≤
          (δ + ε) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have hcoeff : (δ + ε / 8) + (- (δ / 2) + ε / 4) + ε / 8 + ε / 8 ≤ δ + ε := by
          linarith only [hδ0, hε]
        have hmul : (δ + ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) +
            (- (δ / 2) * (n₁ : ℝ) * Real.log (n₁ : ℝ) + (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ)) +
            (ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) + (ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) ≤
            (δ + ε) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          calc _ = ((δ + ε / 8) + (- (δ / 2) + ε / 4) + ε / 8 + ε / 8) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) := by ring
            _ ≤ (δ + ε) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) :=
              mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hn₁_pos.le hlog_n₁_pos.le)
            _ = (δ + ε) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
        linarith only [hS_tiny_ub, h_osc_hi, hS_collar_ub, hS_upper_ub, hmul]
      have h_lb_tot : -((δ + ε) * (n₁ : ℝ) * Real.log (n₁ : ℝ)) ≤
          ∑ p ∈ S_tiny, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) +
          ∑ p ∈ S_osc, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) +
          ∑ p ∈ S_collar, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) +
          ∑ p ∈ S_upper, (padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ) -
          (1 / 2 : ℝ) * (n₁ : ℝ) * Real.log (h : ℝ) := by
        have hcoeff : -(δ + ε) ≤ -(δ / 2) - ε / 4 := by linarith only [hδ0, hε]
        have hmul : -((δ + ε) * (n₁ : ℝ) * Real.log (n₁ : ℝ)) ≤
            -(δ / 2) * (n₁ : ℝ) * Real.log (n₁ : ℝ) - (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          calc _ = (-(δ + ε)) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) := by ring
            _ ≤ (-(δ / 2) - ε / 4) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) :=
              mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hn₁_pos.le hlog_n₁_pos.le)
            _ = -(δ / 2) * (n₁ : ℝ) * Real.log (n₁ : ℝ) - (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
        linarith only [h_tiny_nn, h_osc_lo, h_collar_nn, h_upper_nn, hmul]
      exact abs_le.mpr ⟨h_lb_tot, h_ub_tot⟩
  exact ⟨h_branch1, h_branch2⟩

end GrasGreenbergBrocard
