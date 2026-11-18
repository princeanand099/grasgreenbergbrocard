import GrasGreenbergBrocard.Thm6_4CapacityDiamond

/-!
# Section 6.4 (Part 2): Polarization Concentration (Theorem 6.4(b))

This file formalizes **Theorem 6.4(b) (Polarization Concentration via Rankin Spherical Cap
Cauchy–Schwarz)** and the resulting `C_ε η^{-2} N^ε` counting bound.
-/

open scoped BigOperators
open Real Finset Filter

set_option maxHeartbeats 2000000

namespace GrasGreenbergBrocard

/-- **Theorem 6.4(b) (Polarization Concentration via Rankin Spherical Cap Cauchy–Schwarz)**:
For any `ε ∈ (0, 1/4)` and `η ∈ (0, 1/2]`, there exists `N₀` such that for all `N' ≥ N₀`,
any interval `[N', N' + ⌊(N')^{1-ε}⌋]` contains at most `⌊(η^2 * ε)⁻¹⌋ + 1` solutions `n` with
`|θ_ε(n) - 1/2| ≥ η`, and `#{4 ≤ n ≤ N : ∃ m, n! + 1 = m^2 ∧ |θ_ε(n) - 1/2| ≥ η} ≤ C_ε * η^{-2} * N^ε`. -/
private def PolBad (ε η : ℝ) (n : ℕ) : Prop :=
  ∃ m : ℕ, Nat.factorial n + 1 = m ^ 2 ∧ |theta_eps_weight ε n m - 1 / 2| ≥ η

open Classical in
theorem thm_6_4_polarization_concentration (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 4)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      (∀ N' : ℕ, N₀ ≤ N' →
        ((Finset.Icc N' (N' + Nat.floor ((N' : ℝ) ^ (1 - ε)))).filter (fun n =>
          ∃ m : ℕ, Nat.factorial n + 1 = m ^ 2 ∧ |theta_eps_weight ε n m - 1 / 2| ≥ η)).card ≤
          Nat.floor ((η ^ 2 * ε)⁻¹) + 1) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        (((Finset.Icc 4 N).filter (fun n =>
          ∃ m : ℕ, Nat.factorial n + 1 = m ^ 2 ∧ |theta_eps_weight ε n m - 1 / 2| ≥ η)).card : ℝ) ≤
          C * η ^ (-2 : ℤ) * (N : ℝ) ^ ε) := by
  let M : ℕ := Nat.floor ((η ^ 2 * ε)⁻¹) + 1
  let τ₀ : ℝ := η ^ 2 * ε / (1000 * (1 + η ^ 2 * ε))
  have hτ₀_pos : 0 < τ₀ := by positivity
  have hτ₀_lt : τ₀ < 1 / 100 := by
    dsimp [τ₀]
    have : η ^ 2 * ε < 10 * (1 + η ^ 2 * ε) := by nlinarith
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h_band := multi_modulus_power_band_equidistribution 2 1 (by norm_num) (1 - ε / 2) 1
    (by linarith) (by linarith) le_rfl
  obtain ⟨N_band, hN_band⟩ := Filter.eventually_atTop.mp
    (Asymptotics.IsLittleO.bound h_band (show (0 : ℝ) < ε * τ₀ / 16 by positivity))
  obtain ⟨N_sodd, hN_sodd⟩ := Filter.eventually_atTop.mp
    (Asymptotics.IsLittleO.bound S_odd_asymptotic (show (0 : ℝ) < τ₀ / (100 * ((M : ℝ) + 1)) by positivity))
  obtain ⟨N_seven, hN_seven⟩ := Filter.eventually_atTop.mp
    (Asymptotics.IsLittleO.bound S_even_asymptotic (show (0 : ℝ) < τ₀ / (100 * ((M : ℝ) + 1)) by positivity))
  have h_inv_eps : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-ε)) Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hε0 |>.comp tendsto_natCast_atTop_atTop
  have h_inv_eps2 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(ε / 2)) * Real.log (n : ℝ)) Filter.atTop (nhds 0) := by
    refine (log_pow_div_rpow_tendsto_zero 1 (by positivity : (0 : ℝ) < ε / 2)).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [pow_one, Real.rpow_neg (by positivity), div_eq_mul_inv, mul_comm]
  have h_inv_log : Filter.Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N_e1, hN_e1⟩ := Filter.eventually_atTop.mp
    (h_inv_eps.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < τ₀ / (100 * ((M : ℝ) + 1)) by positivity)))
  obtain ⟨N_e2, hN_e2⟩ := Filter.eventually_atTop.mp
    (h_inv_eps2.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < η * ε * τ₀ / 100 by positivity)))
  obtain ⟨N_il, hN_il⟩ := Filter.eventually_atTop.mp
    (h_inv_log.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / 100 by positivity)))
  obtain ⟨N_il_tau, hN_il_tau⟩ := Filter.eventually_atTop.mp
    (h_inv_log.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < τ₀ / (100 * ((M : ℝ) + 1)) by positivity)))
  let N₀ := max (max (max N_band N_sodd) (max N_seven N_e1)) (max N_e2 (max N_il (max N_il_tau 1000)))
  have h_int_bd : ∀ N' : ℕ, N₀ ≤ N' →
      ((Finset.Icc N' (N' + Nat.floor ((N' : ℝ) ^ (1 - ε)))).filter (fun n =>
        ∃ m : ℕ, Nat.factorial n + 1 = m ^ 2 ∧ |theta_eps_weight ε n m - 1 / 2| ≥ η)).card ≤ M := by
    intro N' hN'
    set L := Nat.floor ((N' : ℝ) ^ (1 - ε))
    set S_pol := (Finset.Icc N' (N' + L)).filter (fun n =>
      ∃ m : ℕ, Nat.factorial n + 1 = m ^ 2 ∧ |theta_eps_weight ε n m - 1 / 2| ≥ η)
    by_contra h_gt
    push Not at h_gt
    set t := S_pol.card
    have ht_ge : M + 1 ≤ t := h_gt
    let P_base := (Finset.Icc 3 N').filter Nat.Prime
    let W_tot := S_odd N' + S_even N'
    have hlogN'_pos : 0 < Real.log (N' : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N'))
    have hNlog_nn : 0 ≤ (N' : ℝ) * Real.log (N' : ℝ) := mul_nonneg (Nat.cast_nonneg _) hlogN'_pos.le
    have hW_tot_eq : W_tot = ∑ p ∈ P_base, (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) := by
      unfold W_tot S_odd S_even Podd Peven P_base
      have hdisj : Disjoint ((Finset.Icc 2 N').filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (Nat.factorial N')) |>.filter (3 ≤ ·))
          ((Finset.Icc 2 N').filter (fun p => p.Prime ∧ 2 ∣ padicValNat p (Nat.factorial N')) |>.filter (3 ≤ ·)) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [Finset.mem_filter] at h1 h2; exact h1.1.2.2 h2.1.2.2
      rw [← Finset.sum_union hdisj]
      congr 1; ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro (⟨⟨⟨_, hpN⟩, hp_pr, _⟩, hp3⟩ | ⟨⟨⟨_, hpN⟩, hp_pr, _⟩, hp3⟩) <;> exact ⟨⟨hp3, hpN⟩, hp_pr⟩
      · rintro ⟨⟨hp3, hpN⟩, hp_pr⟩
        by_cases h2d : 2 ∣ padicValNat p (Nat.factorial N')
        · exact Or.inr ⟨⟨⟨by omega, hpN⟩, hp_pr, h2d⟩, hp3⟩
        · exact Or.inl ⟨⟨⟨by omega, hpN⟩, hp_pr, h2d⟩, hp3⟩
    have hSodd_bd_tight : |S_odd N' - (1 / 2 : ℝ) * (N' : ℝ) * Real.log (N' : ℝ)| ≤ (τ₀ / (100 * ((M : ℝ) + 1))) * (N' : ℝ) * Real.log (N' : ℝ) := by
      have h := hN_sodd N' (by omega)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hNlog_nn] at h; simpa [mul_assoc] using h
    have hSodd_bd : |S_odd N' - (1 / 2 : ℝ) * (N' : ℝ) * Real.log (N' : ℝ)| ≤ (τ₀ / 4) * (N' : ℝ) * Real.log (N' : ℝ) := by
      have h1 : τ₀ / (100 * ((M : ℝ) + 1)) ≤ τ₀ / 4 := by gcongr; linarith [show (1 : ℝ) ≤ M by exact_mod_cast (by omega : 1 ≤ M)]
      nlinarith [hNlog_nn]
    have hSeven_bd_tight : |S_even N' - (1 / 2 : ℝ) * (N' : ℝ) * Real.log (N' : ℝ)| ≤ (τ₀ / (100 * ((M : ℝ) + 1))) * (N' : ℝ) * Real.log (N' : ℝ) := by
      have h := hN_seven N' (by omega)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hNlog_nn] at h; simpa [mul_assoc] using h
    have hSeven_bd : |S_even N' - (1 / 2 : ℝ) * (N' : ℝ) * Real.log (N' : ℝ)| ≤ (τ₀ / 4) * (N' : ℝ) * Real.log (N' : ℝ) := by
      have h1 : τ₀ / (100 * ((M : ℝ) + 1)) ≤ τ₀ / 4 := by gcongr; linarith [show (1 : ℝ) ≤ M by exact_mod_cast (by omega : 1 ≤ M)]
      nlinarith [hNlog_nn]
    have hW_tot_lb : (1 - τ₀ / 2) * (N' : ℝ) * Real.log (N' : ℝ) ≤ W_tot := by
      have h1 := (abs_le.mp hSodd_bd).1; have h2 := (abs_le.mp hSeven_bd).1
      dsimp [W_tot]; linarith
    have hW_tot_ub : W_tot ≤ (1 + τ₀ / 2) * (N' : ℝ) * Real.log (N' : ℝ) := by
      have h1 := (abs_le.mp hSodd_bd).2; have h2 := (abs_le.mp hSeven_bd).2
      dsimp [W_tot]; linarith
    have hW_tot_pos : 0 < W_tot := by nlinarith [show (0 : ℝ) < N' by positivity]
    let w : ℕ → ℝ := fun p => (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) / W_tot
    have hw_nn : ∀ p, 0 ≤ w p := fun p => by
      dsimp [w]; refine div_nonneg (mul_nonneg (Nat.cast_nonneg _) ?_) hW_tot_pos.le
      rcases eq_or_ne p 0 with rfl | hp0
      · simp
      · exact Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hp0)
    have hw_sum : ∑ p ∈ P_base, w p = 1 := by
      dsimp [w]; rw [← Finset.sum_div, ← hW_tot_eq, div_self hW_tot_pos.ne']
    let P_I : Finset ℕ := (Podd N').filter (fun p : ℕ => 3 ≤ p ∧ (N' : ℝ) ^ (1 - ε / 2) < (p : ℝ))
    have hP_I_sub : P_I ⊆ P_base := by
      intro p hp; simp only [P_I, Podd, P_base, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.2.1, hp.1.1.2⟩, hp.1.2⟩
    let W_I := ∑ p ∈ P_I, w p
    have hband_sum_eq : ∑ p ∈ P_I, (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) =
        ∑ p ∈ (Finset.Icc 2 N').filter (fun p : ℕ =>
          p.Prime ∧ (N' : ℝ) ^ (1 - ε / 2) < (p : ℝ) ∧ (p : ℝ) ≤ (N' : ℝ) ^ (1 : ℝ) ∧
          padicValNat p (Nat.factorial N') ≡ 1 [MOD 2]),
          (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) := by
      congr 1; ext p; simp only [P_I, Podd, Finset.mem_filter, Finset.mem_Icc, Real.rpow_one]
      constructor
      · rintro ⟨⟨⟨_, hpN⟩, hp_pr, hp_odd⟩, hp3, hp_gt⟩
        refine ⟨⟨by omega, hpN⟩, hp_pr, hp_gt, by exact_mod_cast hpN, ?_⟩
        rw [Nat.ModEq]; omega
      · rintro ⟨⟨hp2, hpN⟩, hp_pr, hp_gt, _, hp_mod⟩
        have hp3 : 3 ≤ p := by
          have : (2 : ℝ) < (N' : ℝ) ^ (1 - ε / 2) := by
            have h1 : (1000 : ℝ) ^ (1 / 2 : ℝ) ≤ (N' : ℝ) ^ (1 - ε / 2) := by
              have : (1000 : ℝ) ^ (1 / 2 : ℝ) ≤ (1000 : ℝ) ^ (1 - ε / 2) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              exact le_trans this (Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : 1000 ≤ N')) (by linarith))
            have h2 : (2 : ℝ) < (1000 : ℝ) ^ (1 / 2 : ℝ) := by
              rw [← Real.sqrt_eq_rpow, Real.lt_sqrt (by norm_num)]; norm_num
            linarith
          have : (2 : ℝ) < (p : ℝ) := lt_trans this hp_gt
          exact_mod_cast (by
            have : 2 < p := by exact_mod_cast this
            omega)
        refine ⟨⟨⟨by omega, hpN⟩, hp_pr, ?_⟩, hp3, hp_gt⟩
        intro h2d; rw [Nat.ModEq] at hp_mod; omega
    have hband_bd : |∑ p ∈ P_I, (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) -
        ((1 - (1 - ε / 2)) / 2) * (N' : ℝ) * Real.log (N' : ℝ)| ≤
        (ε * τ₀ / 16) * (N' : ℝ) * Real.log (N' : ℝ) := by
      rw [hband_sum_eq]
      have h := hN_band N' (by omega)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hNlog_nn] at h
      simpa [mul_assoc] using h
    have hW_I_lb : (ε / 4) * (1 - τ₀) ≤ W_I := by
      have h1 := (abs_le.mp hband_bd).1
      have h2 : (ε / 4 - ε * τ₀ / 16) * (N' : ℝ) * Real.log (N' : ℝ) ≤
          ∑ p ∈ P_I, (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) := by linarith
      dsimp [W_I, w]; rw [← Finset.sum_div, le_div_iff₀ hW_tot_pos]
      have h3 : (ε / 4) * (1 - τ₀) * (1 + τ₀ / 2) ≤ ε / 4 - ε * τ₀ / 16 := by
        nlinarith [hε0, hτ₀_pos, hτ₀_lt]
      calc (ε / 4) * (1 - τ₀) * W_tot
          ≤ (ε / 4) * (1 - τ₀) * ((1 + τ₀ / 2) * (N' : ℝ) * Real.log (N' : ℝ)) :=
            mul_le_mul_of_nonneg_left hW_tot_ub (by nlinarith [hε0, hτ₀_lt])
        _ ≤ (ε / 4 - ε * τ₀ / 16) * (N' : ℝ) * Real.log (N' : ℝ) := by
            nlinarith [hNlog_nn]
        _ ≤ _ := h2
    have hW_I_ub : W_I ≤ (ε / 4) * (1 + τ₀) := by
      have h1 := (abs_le.mp hband_bd).2
      have h2 : ∑ p ∈ P_I, (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) ≤
          (ε / 4 + ε * τ₀ / 16) * (N' : ℝ) * Real.log (N' : ℝ) := by linarith
      dsimp [W_I, w]; rw [← Finset.sum_div, div_le_iff₀ hW_tot_pos]
      have h3 : (ε / 4 + ε * τ₀ / 16) ≤ (ε / 4) * (1 + τ₀) * (1 - τ₀ / 2) := by
        nlinarith [hε0, hτ₀_pos, hτ₀_lt]
      calc _ ≤ (ε / 4 + ε * τ₀ / 16) * (N' : ℝ) * Real.log (N' : ℝ) := h2
        _ ≤ (ε / 4) * (1 + τ₀) * ((1 - τ₀ / 2) * (N' : ℝ) * Real.log (N' : ℝ)) := by
            nlinarith [hNlog_nn]
        _ ≤ (ε / 4) * (1 + τ₀) * W_tot :=
            mul_le_mul_of_nonneg_left hW_tot_lb (by positivity)
    have hW_I_pos : 0 < W_I := by linarith
    let v_I : ℕ → ℝ := fun p => if p ∈ P_I then 1 / Real.sqrt W_I else 0
    have hv_I_norm : ∑ p ∈ P_base, w p * (v_I p) ^ 2 = 1 := by
      have h1 : ∑ p ∈ P_base, w p * (v_I p) ^ 2 = ∑ p ∈ P_I, w p * (1 / W_I) := by
        rw [← Finset.sum_filter_of_ne (p := (· ∈ P_I))]
        · have hfilt : P_base.filter (· ∈ P_I) = P_I := by
            ext p; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hP_I_sub h, h⟩⟩
          rw [hfilt]; apply Finset.sum_congr rfl; intro p hp
          dsimp [v_I]; rw [if_pos hp, one_div, inv_pow, Real.sq_sqrt hW_I_pos.le, one_div]
        · intro p _ hp; dsimp [v_I]; rw [if_neg hp]; ring
      rw [h1, ← Finset.sum_mul]
      change W_I * (1 / W_I) = 1
      exact mul_one_div_cancel hW_I_pos.ne'
    have hm_ex : ∀ n ∈ S_pol, ∃ m : ℕ, Nat.factorial n + 1 = m ^ 2 ∧ |theta_eps_weight ε n m - 1 / 2| ≥ η :=
      fun n hn => (Finset.mem_filter.mp hn).2
    choose m_fn hm_sq hm_pol using fun n (hn : n ∈ S_pol) => hm_ex n hn
    let u : ∀ n, n ∈ S_pol → ℕ → ℝ := fun n hn p => if p ∣ (m_fn n hn + 1) / 2 then 1 else -1
    have hu_norm : ∀ n (hn : n ∈ S_pol), ∑ p ∈ P_base, w p * (u n hn p) ^ 2 = 1 := by
      intro n hn
      have h1 : ∀ p ∈ P_base, w p * (u n hn p) ^ 2 = w p := by
        intro p _; dsimp [u]; split_ifs <;> ring
      rw [Finset.sum_congr rfl h1, hw_sum]
    have h_uv_lb : ∀ n (hn : n ∈ S_pol),
        Real.sqrt (η ^ 2 * ε * (1 - 20 * τ₀)) ≤ |∑ p ∈ P_base, w p * u n hn p * v_I p| := by
      intro n hn
      set m := m_fn n hn
      have hm := hm_sq n hn
      have hpol := hm_pol n hn
      have hn_mem := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      let P_I_n := (Podd n).filter (fun p => 3 ≤ p ∧ (n : ℝ) ^ (1 - ε / 2) < (p : ℝ))
      let den_n := ∑ p ∈ P_I_n, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
      let num_n := ∑ p ∈ P_I_n.filter (fun p => p ∣ B_part n ((m + 1) / 2)),
        (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
      have hθ_eq : theta_eps_weight ε n m = if 0 < den_n then num_n / den_n else 0 := rfl
      have hden_pos : 0 < den_n := by
        by_contra hle
        rw [hθ_eq, if_neg hle] at hpol
        have h_band_n := hN_band n (by omega)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h_band_n
        have hden_eq : den_n = ∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
            p.Prime ∧ (n : ℝ) ^ (1 - ε / 2) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) ∧
            padicValNat p (Nat.factorial n) ≡ 1 [MOD 2]),
            (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
          dsimp [den_n, P_I_n]; congr 1; ext p
          simp only [Podd, Finset.mem_filter, Finset.mem_Icc, Real.rpow_one]
          constructor
          · rintro ⟨⟨⟨_, hpn⟩, hp_pr, hp_odd⟩, hp3, hp_gt⟩
            refine ⟨⟨by omega, hpn⟩, hp_pr, hp_gt, by exact_mod_cast hpn, ?_⟩
            rw [Nat.ModEq]; omega
          · rintro ⟨⟨_, hpn⟩, hp_pr, hp_gt, _, hp_mod⟩
            have hp3 : 3 ≤ p := by
              have : (2 : ℝ) < (n : ℝ) ^ (1 - ε / 2) := by
                have h1 : (1000 : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ (1 - ε / 2) := by
                  have : (1000 : ℝ) ^ (1 / 2 : ℝ) ≤ (1000 : ℝ) ^ (1 - ε / 2) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                  exact le_trans this (Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : 1000 ≤ n)) (by linarith))
                have h2 : (2 : ℝ) < (1000 : ℝ) ^ (1 / 2 : ℝ) := by
                  rw [← Real.sqrt_eq_rpow, Real.lt_sqrt (by norm_num)]; norm_num
                linarith
              have : 2 < p := by exact_mod_cast lt_trans this hp_gt
              omega
            refine ⟨⟨⟨by omega, hpn⟩, hp_pr, ?_⟩, hp3, hp_gt⟩
            intro h2d; rw [Nat.ModEq] at hp_mod; omega
        rw [hden_eq] at hle
        have h1 := (abs_le.mp h_band_n).1
        have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        have : (ε / 4 - ε * τ₀ / 4) * (n : ℝ) * Real.log (n : ℝ) > 0 := by nlinarith [show 0 < (n : ℝ) by positivity]
        linarith
      rw [hθ_eq, if_pos hden_pos] at hpol
      have h2num_sub : 2 * num_n - den_n =
          ∑ p ∈ P_I_n, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) * u n hn p := by
        have h_u_eq : ∀ p ∈ P_I_n, u n hn p =
            if p ∣ B_part n ((m + 1) / 2) then (1 : ℝ) else -1 := by
          intro p hp
          have hp_mem := Finset.mem_filter.mp hp
          have hp_pr := (Finset.mem_filter.mp hp_mem.1).2.1
          have hp3 := hp_mem.2.1
          dsimp [u]
          have hiff : p ∣ (m + 1) / 2 ↔ p ∣ B_part n ((m + 1) / 2) := by
            constructor
            · intro hpm
              unfold B_part
              exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hp_mem.1, hp3⟩, hpm⟩)
            · intro hpB
              unfold B_part at hpB
              rw [hp_pr.prime.dvd_finset_prod_iff] at hpB
              obtain ⟨q, hq, hqd⟩ := hpB
              have hq_mem := Finset.mem_filter.mp hq
              have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp_pr (Finset.mem_filter.mp (Finset.mem_filter.mp hq_mem.1).1).2.1).mp (hp_pr.dvd_of_dvd_pow hqd)
              subst hpq; exact hq_mem.2
          by_cases h1 : p ∣ (m + 1) / 2
          · rw [if_pos h1, if_pos (hiff.mp h1)]
          · rw [if_neg h1, if_neg (fun h => h1 (hiff.mpr h))]
        have hsum1 : ∑ p ∈ P_I_n, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) * u n hn p =
            ∑ p ∈ P_I_n, (if p ∣ B_part n ((m + 1) / 2) then
              (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
            else -((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ))) := by
          apply Finset.sum_congr rfl; intro p hp
          rw [h_u_eq p hp]; split_ifs <;> ring
        rw [hsum1, ← Finset.sum_filter_add_sum_filter_not P_I_n (fun p => p ∣ B_part n ((m + 1) / 2))]
        have hpos_sum : ∑ p ∈ P_I_n.filter (fun p => p ∣ B_part n ((m + 1) / 2)),
            (if p ∣ B_part n ((m + 1) / 2) then
              (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
            else -((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ))) = num_n := by
          apply Finset.sum_congr rfl; intro p hp; rw [if_pos (Finset.mem_filter.mp hp).2]
        have hneg_sum : ∑ p ∈ P_I_n.filter (fun p => ¬ p ∣ B_part n ((m + 1) / 2)),
            (if p ∣ B_part n ((m + 1) / 2) then
              (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
            else -((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ))) =
            -(den_n - num_n) := by
          have hden_split := Finset.sum_filter_add_sum_filter_not P_I_n (fun p => p ∣ B_part n ((m + 1) / 2))
            (fun p => (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ))
          rw [← Finset.sum_neg_distrib]
          have : ∑ p ∈ P_I_n.filter (fun p => ¬ p ∣ B_part n ((m + 1) / 2)),
              (if p ∣ B_part n ((m + 1) / 2) then
                (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
              else -((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ))) =
              ∑ p ∈ P_I_n.filter (fun p => ¬ p ∣ B_part n ((m + 1) / 2)),
                -((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) := by
            apply Finset.sum_congr rfl; intro p hp; rw [if_neg (Finset.mem_filter.mp hp).2]
          rw [this, Finset.sum_neg_distrib]; linarith
        rw [hpos_sum, hneg_sum]; ring
      have h_abs_n : 2 * η * den_n ≤ |∑ p ∈ P_I_n, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) * u n hn p| := by
        rw [← h2num_sub]
        have h1 : |num_n / den_n - 1 / 2| = |2 * num_n - den_n| / (2 * den_n) := by
          rw [show num_n / den_n - 1 / 2 = (2 * num_n - den_n) / (2 * den_n) by field_simp [hden_pos.ne'],
            abs_div, abs_of_pos (by positivity)]
        rw [h1, ge_iff_le, le_div_iff₀ (by positivity)] at hpol
        linarith
      have hdiff_sum : |∑ p ∈ P_I_n, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) * u n hn p -
          ∑ p ∈ P_I, (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) * u n hn p| ≤
          10 * (N' : ℝ) ^ (1 - ε / 2) * Real.log (2 * (N' : ℝ)) := by
        let U_union := P_I_n ∪ P_I
        have h_eq1 : ∑ p ∈ P_I_n, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) * u n hn p =
            ∑ p ∈ U_union, (if p ∈ P_I_n then (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) * u n hn p else 0) := by
          rw [← Finset.sum_filter_of_ne (p := (· ∈ P_I_n))]
          · congr 1; ext p; simp [U_union]
          · intro p _ hp; rw [if_neg hp]
        have h_eq2 : ∑ p ∈ P_I, (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) * u n hn p =
            ∑ p ∈ U_union, (if p ∈ P_I then (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) * u n hn p else 0) := by
          rw [← Finset.sum_filter_of_ne (p := (· ∈ P_I))]
          · congr 1; ext p; simp [U_union]
          · intro p _ hp; rw [if_neg hp]
        rw [h_eq1, h_eq2, ← Finset.sum_sub_distrib]
        have hn_le_2N' : (n : ℝ) ≤ 2 * (N' : ℝ) := by
          have hL_le : (L : ℝ) ≤ (N' : ℝ) ^ (1 - ε) := Nat.floor_le (by positivity)
          have hpow_le : (N' : ℝ) ^ (1 - ε) ≤ (N' : ℝ) := by
            calc (N' : ℝ) ^ (1 - ε) ≤ (N' : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N')) (by linarith)
              _ = (N' : ℝ) := Real.rpow_one _
          have : (n : ℝ) ≤ (N' : ℝ) + (L : ℝ) := by exact_mod_cast hn_mem.2
          linarith
        have h_fac_ratio : Real.log ((Nat.factorial n / Nat.factorial N' : ℕ) : ℝ) ≤ (N' : ℝ) ^ (1 - ε) * Real.log (2 * (N' : ℝ)) := by
          by_cases h_eqN : n = N'
          · subst h_eqN; rw [Nat.div_self (Nat.factorial_pos _)]; simp; positivity
          · have hlt_N : N' < n := by omega
            have hprod_eq : Nat.factorial n / Nat.factorial N' = ∏ j ∈ Finset.Ioc N' n, j := by
              have hfac := Nat.div_mul_cancel (Nat.factorial_dvd_factorial hlt_N.le)
              have hprod : Nat.factorial n = Nat.factorial N' * ∏ j ∈ Finset.Ioc N' n, j := by
                have hle : N' ≤ n := hlt_N.le
                induction n, hle using Nat.le_induction with
                | base => simp
                | succ k hk ih => rw [Nat.factorial_succ, Finset.prod_Ioc_succ_top hk, ih]; ring
              have : (Nat.factorial n / Nat.factorial N') * Nat.factorial N' =
                  (∏ j ∈ Finset.Ioc N' n, j) * Nat.factorial N' := by rw [hfac, hprod]; ring
              exact mul_right_cancel₀ (Nat.factorial_pos N').ne' this
            have hle_nat : ∏ j ∈ Finset.Ioc N' n, j ≤ (2 * N') ^ (n - N') := by
              calc ∏ j ∈ Finset.Ioc N' n, j ≤ ∏ _j ∈ Finset.Ioc N' n, (2 * N') :=
                    Finset.prod_le_prod' (fun j hj => by
                      have := (Finset.mem_Ioc.mp hj).2
                      exact_mod_cast le_trans (by exact_mod_cast this) hn_le_2N')
                _ = (2 * N') ^ (Finset.Ioc N' n).card := Finset.prod_const _
                _ = (2 * N') ^ (n - N') := by rw [Nat.card_Ioc]
            have hpos_p : 0 < Nat.factorial n / Nat.factorial N' := by
              rw [hprod_eq]; exact Finset.prod_pos (fun j hj => by have := (Finset.mem_Ioc.mp hj).1; omega)
            have h1 := Real.log_le_log (by exact_mod_cast hpos_p) (by exact_mod_cast (hprod_eq ▸ hle_nat))
            rw [Nat.cast_pow, Real.log_pow] at h1
            have hsub_le : ((n - N' : ℕ) : ℝ) ≤ (N' : ℝ) ^ (1 - ε) := by
              have : n - N' ≤ L := by omega
              exact le_trans (by exact_mod_cast this) (Nat.floor_le (by positivity))
            have hlog2N : 0 ≤ Real.log (2 * (N' : ℝ)) := Real.log_nonneg (by linarith [show (1000 : ℝ) ≤ N' by exact_mod_cast (by omega : 1000 ≤ N')])
            exact le_trans h1 (mul_le_mul_of_nonneg_right hsub_le hlog2N)
        have hU_term : ∀ p ∈ U_union,
            |(if p ∈ P_I_n then (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) * u n hn p else 0) -
             (if p ∈ P_I then (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) * u n hn p else 0)| ≤
            if p ∈ P_I_n ∧ p ∈ P_I then
              ((padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N') : ℕ) : ℝ) * Real.log (p : ℝ)
            else (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
          intro p hp
          by_cases h1 : p ∈ P_I_n <;> by_cases h2 : p ∈ P_I
          · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]
            have hu1 : |u n hn p| = 1 := by dsimp [u]; split_ifs <;> norm_num
            have hv_le : padicValNat p (Nat.factorial N') ≤ padicValNat p (Nat.factorial n) := by
              have hp_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2.1
              haveI : Fact p.Prime := ⟨hp_pr⟩
              exact (Nat.factorization_le_iff_dvd (Nat.factorial_pos N').ne' (Nat.factorial_pos n).ne').mpr
                (Nat.factorial_dvd_factorial hn_mem.1) p
            have hdiff_r : (padicValNat p (Nat.factorial n) : ℝ) - (padicValNat p (Nat.factorial N') : ℝ) =
                ((padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N') : ℕ) : ℝ) := by
              exact_mod_cast (by omega : (padicValNat p (Nat.factorial n) : ℤ) - padicValNat p (Nat.factorial N') =
                ↑(padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N')))
            have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2.1.pos)
            calc |((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) * u n hn p) -
                  ((padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) * u n hn p)|
                = |((padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N') : ℕ) : ℝ) * Real.log (p : ℝ)| * |u n hn p| := by
                  rw [← hdiff_r, abs_mul]; congr 1; ring_nf
              _ = ((padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N') : ℕ) : ℝ) * Real.log (p : ℝ) := by
                  rw [hu1, mul_one, abs_of_nonneg (by positivity)]
          · rw [if_neg (by tauto), if_pos h1, if_neg h2, sub_zero, abs_mul,
              show |u n hn p| = 1 by dsimp [u]; split_ifs <;> norm_num, mul_one,
              abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2.1.pos)))]
          · rw [if_neg (by tauto), if_neg h1, if_pos h2, zero_sub, abs_neg, abs_mul,
              show |u n hn p| = 1 by dsimp [u]; split_ifs <;> norm_num, mul_one,
              abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2.1.pos)))]
            have hp_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2.1
            haveI : Fact p.Prime := ⟨hp_pr⟩
            have hv_le : padicValNat p (Nat.factorial N') ≤ padicValNat p (Nat.factorial n) :=
              (Nat.factorization_le_iff_dvd (Nat.factorial_pos N').ne' (Nat.factorial_pos n).ne').mpr
                (Nat.factorial_dvd_factorial hn_mem.1) p
            have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_pr.pos)
            gcongr
          · simp [U_union] at hp; tauto
        have h_sum_abs := Finset.abs_sum_le_sum_abs _ U_union
        have h_le_u := le_trans h_sum_abs (Finset.sum_le_sum hU_term)
        let U1 := U_union.filter (fun p => p ∈ P_I_n ∧ p ∈ P_I)
        let U2 := U_union.filter (fun p => ¬ (p ∈ P_I_n ∧ p ∈ P_I) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 - ε / 2))
        let U3 := U_union.filter (fun p => ¬ (p ∈ P_I_n ∧ p ∈ P_I) ∧ (n : ℝ) ^ (1 - ε / 2) < (p : ℝ))
        have hU1_ub : ∑ p ∈ U1, ((padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N') : ℕ) : ℝ) * Real.log (p : ℝ) ≤
            (N' : ℝ) ^ (1 - ε / 2) * Real.log (2 * (N' : ℝ)) := by
          have hdvd_U1 : ∏ p ∈ U1, p ^ (padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N')) ∣
              Nat.factorial n / Nat.factorial N' := by
            apply Finset.prod_primes_dvd
            · intro p hp
              have hp_m := Finset.mem_filter.mp hp
              have hp_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hp_m.2.2).1).2.1
              haveI : Fact p.Prime := ⟨hp_pr⟩
              have hP_pos : 0 < Nat.factorial n / Nat.factorial N' := Nat.div_pos (Nat.factorial_le hn_mem.1) (Nat.factorial_pos N')
              have hv_eq : padicValNat p (Nat.factorial n / Nat.factorial N') =
                  padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N') := by
                have hmul := Nat.div_mul_cancel (Nat.factorial_dvd_factorial hn_mem.1)
                have hv := congrArg (padicValNat p) hmul
                rw [padicValNat.mul hP_pos.ne' (Nat.factorial_pos N').ne'] at hv; omega
              rw [← hv_eq]; exact pow_padicValNat_dvd
            · intro p hp q hq hpq
              exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).2.2).1).2.1
                (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).2.2).1).2.1).mpr hpq)
          have hpos_U1 : 0 < ∏ p ∈ U1, p ^ (padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N')) :=
            Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).2.2).1).2.1.pos _)
          have hP_pos : 0 < Nat.factorial n / Nat.factorial N' := Nat.div_pos (Nat.factorial_le hn_mem.1) (Nat.factorial_pos N')
          have hlog_U1 := Real.log_le_log (by exact_mod_cast hpos_U1) (by exact_mod_cast Nat.le_of_dvd hP_pos hdvd_U1)
          rw [Nat.cast_prod, Real.log_prod _ _ (fun p hp => pow_ne_zero _ (by
            exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).2.2).1).2.1.ne_zero))] at hlog_U1
          have hsum_eq : ∑ p ∈ U1, ((padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N') : ℕ) : ℝ) * Real.log (p : ℝ) =
              ∑ p ∈ U1, Real.log ((p ^ (padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N')) : ℕ) : ℝ) := by
            apply Finset.sum_congr rfl; intro p _; rw [Nat.cast_pow, Real.log_pow]
          rw [hsum_eq]
          have hpow_le : (N' : ℝ) ^ (1 - ε) ≤ (N' : ℝ) ^ (1 - ε / 2) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N')) (by linarith)
          have hlog2N : 0 ≤ Real.log (2 * (N' : ℝ)) := Real.log_nonneg (by linarith [show (1000 : ℝ) ≤ N' by exact_mod_cast (by omega : 1000 ≤ N')])
          exact le_trans hlog_U1 (le_trans h_fac_ratio (mul_le_mul_of_nonneg_right hpow_le hlog2N))
        have hv_ub_U : ∀ p ∈ U_union, (padicValNat p (Nat.factorial n) : ℝ) ≤ 4 * (N' : ℝ) ^ (ε / 2) := by
          intro p hp
          have hp_pr : p.Prime := by
            simp only [U_union, Finset.mem_union] at hp
            rcases hp with h | h <;> exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1
          have hp3 : 3 ≤ p := by
            simp only [U_union, Finset.mem_union] at hp
            rcases hp with h | h <;> exact (Finset.mem_filter.mp h).2.1
          have hp_gt : (N' : ℝ) ^ (1 - ε / 2) < (p : ℝ) := by
            simp only [U_union, Finset.mem_union] at hp
            rcases hp with h | h
            · have h1 := (Finset.mem_filter.mp h).2.2
              have h2 : (N' : ℝ) ^ (1 - ε / 2) ≤ (n : ℝ) ^ (1 - ε / 2) :=
                Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn_mem.1) (by linarith)
              linarith
            · exact (Finset.mem_filter.mp h).2.2
          have hv2 := val_factorial_le_two_div (n := n) hp_pr hp3
          calc (padicValNat p (Nat.factorial n) : ℝ) ≤ 2 * (n : ℝ) / (p : ℝ) := hv2
            _ ≤ 2 * (2 * (N' : ℝ)) / ((N' : ℝ) ^ (1 - ε / 2)) := by gcongr
            _ = 4 * ((N' : ℝ) / (N' : ℝ) ^ (1 - ε / 2)) := by ring
            _ = 4 * (N' : ℝ) ^ (ε / 2) := by
                congr 1; rw [← Real.rpow_one (N' : ℝ), ← Real.rpow_sub (by positivity)]; ring_nf; rw [Real.rpow_one]
        have hU2_ub : ∑ p ∈ U2, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
            5 * (N' : ℝ) ^ (1 - ε / 2) * Real.log (2 * (N' : ℝ)) := by
          have hcard_U2 : (U2.card : ℝ) ≤ (N' : ℝ) ^ (1 - 3 * ε / 2) + 1 := by
            have hsub : U2 ⊆ Finset.Icc (Nat.floor ((N' : ℝ) ^ (1 - ε / 2)) + 1) (Nat.floor ((n : ℝ) ^ (1 - ε / 2))) := by
              intro p hp
              have hp_m := Finset.mem_filter.mp hp
              have hp_gt : (N' : ℝ) ^ (1 - ε / 2) < (p : ℝ) := by
                simp only [U_union, Finset.mem_union] at hp_m
                rcases hp_m.1 with h | h
                · exact lt_of_le_of_lt (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn_mem.1) (by linarith))
                    (Finset.mem_filter.mp h).2.2
                · exact (Finset.mem_filter.mp h).2.2
              exact Finset.mem_Icc.mpr ⟨by
                by_contra hle; push Not at hle
                have : (p : ℝ) ≤ Nat.floor ((N' : ℝ) ^ (1 - ε / 2)) := by exact_mod_cast hle
                linarith [Nat.floor_le (by positivity : 0 ≤ (N' : ℝ) ^ (1 - ε / 2))], Nat.le_floor hp_m.2.2⟩
            have hcard1 : U2.card ≤ Nat.floor ((n : ℝ) ^ (1 - ε / 2)) - Nat.floor ((N' : ℝ) ^ (1 - ε / 2)) := by
              have := Finset.card_le_card hsub; simp only [Nat.card_Icc] at this; omega
            have hdiff_r : ((Nat.floor ((n : ℝ) ^ (1 - ε / 2)) : ℝ) - (Nat.floor ((N' : ℝ) ^ (1 - ε / 2)) : ℝ)) ≤
                (n : ℝ) ^ (1 - ε / 2) - (N' : ℝ) ^ (1 - ε / 2) + 1 := by
              linarith [Nat.floor_le (by positivity : 0 ≤ (n : ℝ) ^ (1 - ε / 2)),
                Nat.sub_one_lt_floor ((N' : ℝ) ^ (1 - ε / 2))]
            have hconc : (n : ℝ) ^ (1 - ε / 2) - (N' : ℝ) ^ (1 - ε / 2) ≤ (N' : ℝ) ^ (1 - 3 * ε / 2) := by
              let x : ℝ := ((n : ℝ) - (N' : ℝ)) / (N' : ℝ)
              have hx_nn : 0 ≤ x := div_nonneg (by exact_mod_cast (by omega : (N' : ℤ) ≤ n)) (by positivity)
              have hx_le : x ≤ (N' : ℝ) ^ (-ε) := by
                dsimp [x]
                have h1 : (n : ℝ) - (N' : ℝ) ≤ (N' : ℝ) ^ (1 - ε) := by
                  have : n - N' ≤ L := by omega
                  have hsub_eq : (n : ℝ) - (N' : ℝ) = ((n - N' : ℕ) : ℝ) := by exact_mod_cast (by omega : (n : ℤ) - N' = ↑(n - N'))
                  rw [hsub_eq]; exact le_trans (by exact_mod_cast this) (Nat.floor_le (by positivity))
                calc ((n : ℝ) - (N' : ℝ)) / (N' : ℝ) ≤ (N' : ℝ) ^ (1 - ε) / (N' : ℝ) := by gcongr
                  _ = (N' : ℝ) ^ (-ε) := by rw [← Real.rpow_one (N' : ℝ), ← Real.rpow_sub (by positivity)]; ring_nf
              have h1x : (1 + x) ^ (1 - ε / 2) ≤ 1 + x := by
                simpa using Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith : 1 - ε / 2 ≤ 1)
              have hn_eq : (n : ℝ) = (N' : ℝ) * (1 + x) := by dsimp [x]; field_simp [(by positivity : (N' : ℝ) ≠ 0)]; ring
              calc (n : ℝ) ^ (1 - ε / 2) - (N' : ℝ) ^ (1 - ε / 2)
                  = (N' : ℝ) ^ (1 - ε / 2) * ((1 + x) ^ (1 - ε / 2) - 1) := by
                    rw [hn_eq, Real.mul_rpow (by positivity) (by linarith)]; ring
                _ ≤ (N' : ℝ) ^ (1 - ε / 2) * x := by gcongr; linarith
                _ ≤ (N' : ℝ) ^ (1 - ε / 2) * (N' : ℝ) ^ (-ε) := by gcongr
                _ = (N' : ℝ) ^ (1 - 3 * ε / 2) := by rw [← Real.rpow_add (by positivity)]; ring_nf
            have hcard1_r : (U2.card : ℝ) ≤ (Nat.floor ((n : ℝ) ^ (1 - ε / 2)) : ℝ) -
                (Nat.floor ((N' : ℝ) ^ (1 - ε / 2)) : ℝ) := by
              have hle_fl : Nat.floor ((N' : ℝ) ^ (1 - ε / 2)) ≤ Nat.floor ((n : ℝ) ^ (1 - ε / 2)) :=
                Nat.floor_mono (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn_mem.1) (by linarith))
              exact_mod_cast hcard1
            linarith
          have hterm_U2 : ∀ p ∈ U2, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
              4 * (N' : ℝ) ^ (ε / 2) * Real.log (2 * (N' : ℝ)) := by
            intro p hp
            have hp_m := Finset.mem_filter.mp hp
            have hp_le_n : p ≤ n := by
              simp only [U_union, Finset.mem_union] at hp_m
              rcases hp_m.1 with h | h
              · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1).2
              · exact le_trans (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1).2 hn_mem.1
            have hlog_le : Real.log (p : ℝ) ≤ Real.log (2 * (N' : ℝ)) :=
              Real.log_le_log (by
                simp only [U_union, Finset.mem_union] at hp_m
                rcases hp_m.1 with h | h <;> exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1.pos)
                (le_trans (by exact_mod_cast hp_le_n) hn_le_2N')
            exact mul_le_mul (hv_ub_U p hp_m.1) hlog_le (Real.log_nonneg (by
              simp only [U_union, Finset.mem_union] at hp_m
              rcases hp_m.1 with h | h <;> exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1.pos)) (by positivity)
          have h1_le_eps : ((N' : ℝ) ^ (1 - 3 * ε / 2) + 1) * (4 * (N' : ℝ) ^ (ε / 2)) ≤ 5 * (N' : ℝ) ^ (1 - ε / 2) := by
            have h1 : (N' : ℝ) ^ (1 - 3 * ε / 2) * (N' : ℝ) ^ (ε / 2) = (N' : ℝ) ^ (1 - ε) := by
              rw [← Real.rpow_add (by positivity)]; ring_nf
            have h2 : (N' : ℝ) ^ (1 - ε) ≤ (N' : ℝ) ^ (1 - ε / 2) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N')) (by linarith)
            have h3 : (N' : ℝ) ^ (ε / 2) ≤ (N' : ℝ) ^ (1 - ε / 2) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N')) (by linarith)
            nlinarith
          have hlog2N : 0 ≤ Real.log (2 * (N' : ℝ)) := Real.log_nonneg (by linarith [show (1000 : ℝ) ≤ N' by exact_mod_cast (by omega : 1000 ≤ N')])
          calc ∑ p ∈ U2, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
              ≤ (U2.card : ℝ) * (4 * (N' : ℝ) ^ (ε / 2) * Real.log (2 * (N' : ℝ))) := by
                simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hterm_U2
            _ ≤ ((N' : ℝ) ^ (1 - 3 * ε / 2) + 1) * (4 * (N' : ℝ) ^ (ε / 2) * Real.log (2 * (N' : ℝ))) := by gcongr
            _ = (((N' : ℝ) ^ (1 - 3 * ε / 2) + 1) * (4 * (N' : ℝ) ^ (ε / 2))) * Real.log (2 * (N' : ℝ)) := by ring
            _ ≤ (5 * (N' : ℝ) ^ (1 - ε / 2)) * Real.log (2 * (N' : ℝ)) := by gcongr
            _ = 5 * (N' : ℝ) ^ (1 - ε / 2) * Real.log (2 * (N' : ℝ)) := by ring
        have hU3_ub : ∑ p ∈ U3, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
            4 * (N' : ℝ) ^ (1 - ε / 2) * Real.log (2 * (N' : ℝ)) := by
          have hdvd_U3 : ∏ p ∈ U3, p ∣ Nat.factorial n / Nat.factorial N' := by
            apply Finset.prod_primes_dvd
            · intro p hp
              have hp_m := Finset.mem_filter.mp hp
              have hp_gt : (n : ℝ) ^ (1 - ε / 2) < (p : ℝ) := hp_m.2.2
              have hp_n1 : ¬ (p ∈ P_I_n ∧ p ∈ P_I) := hp_m.2.1
              have hp_pr : p.Prime := by
                simp only [U_union, Finset.mem_union] at hp_m
                rcases hp_m.1 with h | h <;> exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1
              haveI : Fact p.Prime := ⟨hp_pr⟩
              have hP_pos : 0 < Nat.factorial n / Nat.factorial N' := Nat.div_pos (Nat.factorial_le hn_mem.1) (Nat.factorial_pos N')
              by_contra hndvd
              have hv0 : padicValNat p (Nat.factorial n) = padicValNat p (Nat.factorial N') := by
                have hmul := Nat.div_mul_cancel (Nat.factorial_dvd_factorial hn_mem.1)
                have hv := congrArg (padicValNat p) hmul
                rw [padicValNat.mul hP_pos.ne' (Nat.factorial_pos N').ne',
                  padicValNat.eq_zero_of_not_dvd hndvd, zero_add] at hv; exact hv
              apply hp_n1
              simp only [U_union, Finset.mem_union] at hp_m
              rcases hp_m.1 with hp_In | hp_I
              · refine ⟨hp_In, ?_⟩
                have hp_le_N' : p ≤ N' := by
                  by_contra hgt; push Not at hgt
                  apply hndvd
                  have hmul := Nat.div_mul_cancel (Nat.factorial_dvd_factorial hn_mem.1)
                  have hp_fac : p ∣ Nat.factorial n := Nat.dvd_factorial hp_pr.pos
                    (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp_In).1).1).2
                  have hp_nfac : ¬ p ∣ Nat.factorial N' := fun h => by have := hp_pr.dvd_factorial.mp h; omega
                  rw [← hmul] at hp_fac
                  exact (hp_pr.dvd_mul.mp hp_fac).resolve_right hp_nfac
                have hp_mem := Finset.mem_filter.mp hp_In
                refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hp_le_N'⟩, hp_pr, ?_⟩,
                  hp_mem.2.1, lt_of_le_of_lt (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn_mem.1) (by linarith)) hp_gt⟩
                rw [← hv0]; exact (Finset.mem_filter.mp hp_mem.1).2.2
              · have hp_mem := Finset.mem_filter.mp hp_I
                have hp_le_n : p ≤ n := le_trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hp_mem.1).1).2 hn_mem.1
                refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hp_le_n⟩, hp_pr, ?_⟩,
                  hp_mem.2.1, hp_gt⟩, hp_I⟩
                rw [hv0]; exact (Finset.mem_filter.mp hp_mem.1).2.2
            · intro p hp q hq hpq
              have hp_m := Finset.mem_filter.mp hp; have hq_m := Finset.mem_filter.mp hq
              have hp_pr : p.Prime := by
                simp only [U_union, Finset.mem_union] at hp_m
                rcases hp_m.1 with h | h <;> exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1
              have hq_pr : q.Prime := by
                simp only [U_union, Finset.mem_union] at hq_m
                rcases hq_m.1 with h | h <;> exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1
              exact (Nat.coprime_primes hp_pr hq_pr).mpr hpq
          have hpos_U3 : 0 < ∏ p ∈ U3, p := Finset.prod_pos (fun p hp => by
            have hp_m := Finset.mem_filter.mp hp
            simp only [U_union, Finset.mem_union] at hp_m
            rcases hp_m.1 with h | h <;> exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1.pos)
          have hP_pos : 0 < Nat.factorial n / Nat.factorial N' := Nat.div_pos (Nat.factorial_le hn_mem.1) (Nat.factorial_pos N')
          have hlog_U3 := Real.log_le_log (by exact_mod_cast hpos_U3) (by exact_mod_cast Nat.le_of_dvd hP_pos hdvd_U3)
          rw [Nat.cast_prod, Real.log_prod _ _ (fun p hp => by
            have hp_m := Finset.mem_filter.mp hp
            simp only [U_union, Finset.mem_union] at hp_m
            rcases hp_m.1 with h | h <;> exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1.ne_zero)] at hlog_U3
          have hsum_U3_le : ∑ p ∈ U3, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
              4 * (N' : ℝ) ^ (ε / 2) * ∑ p ∈ U3, Real.log (p : ℝ) := by
            rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro p hp
            have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
              have hp_m := Finset.mem_filter.mp hp
              simp only [U_union, Finset.mem_union] at hp_m
              rcases hp_m.1 with h | h <;> exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1.pos)
            exact mul_le_mul_of_nonneg_right (hv_ub_U p (Finset.mem_filter.mp hp).1) hlog_nn
          have hpow_sum : (N' : ℝ) ^ (ε / 2) * ((N' : ℝ) ^ (1 - ε) * Real.log (2 * (N' : ℝ))) =
              (N' : ℝ) ^ (1 - ε / 2) * Real.log (2 * (N' : ℝ)) := by
            rw [← mul_assoc, ← Real.rpow_add (by positivity)]; ring_nf
          calc ∑ p ∈ U3, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
              ≤ 4 * (N' : ℝ) ^ (ε / 2) * ∑ p ∈ U3, Real.log (p : ℝ) := hsum_U3_le
            _ ≤ 4 * (N' : ℝ) ^ (ε / 2) * ((N' : ℝ) ^ (1 - ε) * Real.log (2 * (N' : ℝ))) := by
                gcongr; exact le_trans hlog_U3 h_fac_ratio
            _ = 4 * (N' : ℝ) ^ (1 - ε / 2) * Real.log (2 * (N' : ℝ)) := by rw [mul_assoc, hpow_sum]
        have hU_split : ∑ p ∈ U_union, (if p ∈ P_I_n ∧ p ∈ P_I then
              ((padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N') : ℕ) : ℝ) * Real.log (p : ℝ)
            else (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) =
            (∑ p ∈ U1, ((padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N') : ℕ) : ℝ) * Real.log (p : ℝ)) +
            (∑ p ∈ U2, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) +
            (∑ p ∈ U3, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) := by
          rw [← Finset.sum_filter_add_sum_filter_not U_union (fun p => p ∈ P_I_n ∧ p ∈ P_I)]
          congr 1
          · apply Finset.sum_congr rfl; intro p hp; rw [if_pos (Finset.mem_filter.mp hp).2]
          · rw [← Finset.sum_filter_add_sum_filter_not (U_union.filter (fun p => ¬ (p ∈ P_I_n ∧ p ∈ P_I)))
              (fun p => (p : ℝ) ≤ (n : ℝ) ^ (1 - ε / 2))]
            have hU2_eq : (U_union.filter (fun p => ¬ (p ∈ P_I_n ∧ p ∈ P_I))).filter (fun p => (p : ℝ) ≤ (n : ℝ) ^ (1 - ε / 2)) = U2 := by
              ext p; simp [U2, Finset.mem_filter]; tauto
            have hU3_eq : (U_union.filter (fun p => ¬ (p ∈ P_I_n ∧ p ∈ P_I))).filter (fun p => ¬ (p : ℝ) ≤ (n : ℝ) ^ (1 - ε / 2)) = U3 := by
              ext p; simp [U3, Finset.mem_filter]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.1, h1.2, by linarith⟩
            rw [hU2_eq, hU3_eq]
            congr 1 <;> (apply Finset.sum_congr rfl; intro p hp; rw [if_neg (Finset.mem_filter.mp hp).2.1])
        linarith
      have h_uv_eq : ∑ p ∈ P_base, w p * u n hn p * v_I p =
          (∑ p ∈ P_I, (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) * u n hn p) /
            (W_tot * Real.sqrt W_I) := by
        have h1 : ∑ p ∈ P_base, w p * u n hn p * v_I p =
            ∑ p ∈ P_I, w p * u n hn p * (1 / Real.sqrt W_I) := by
          rw [← Finset.sum_filter_of_ne (p := (· ∈ P_I))]
          · have hfilt : P_base.filter (· ∈ P_I) = P_I := by
              ext p; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hP_I_sub h, h⟩⟩
            rw [hfilt]; apply Finset.sum_congr rfl; intro p hp; dsimp [v_I]; rw [if_pos hp]
          · intro p _ hp; dsimp [v_I]; rw [if_neg hp]; ring
        rw [h1]; dsimp [w]; rw [← Finset.sum_div, Finset.sum_div]
        apply Finset.sum_congr rfl; intro p _; ring
      have hdiff_small : 10 * (N' : ℝ) ^ (1 - ε / 2) * Real.log (2 * (N' : ℝ)) ≤
          η * (ε / 4) * τ₀ * (N' : ℝ) * Real.log (N' : ℝ) := by
        have h2 := hN_e2 N' (by omega)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
        have hlog2N : Real.log (2 * (N' : ℝ)) ≤ 2 * Real.log (N' : ℝ) := by
          rw [Real.log_mul (by norm_num) (by positivity)]
          have : Real.log 2 ≤ Real.log (N' : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ N'))
          linarith
        have hpow_eq : (N' : ℝ) ^ (1 - ε / 2) = (N' : ℝ) * (N' : ℝ) ^ (-(ε / 2)) := by
          rw [← Real.rpow_one_add' (by positivity) (by linarith : 1 + -(ε / 2) ≠ 0)]; ring_nf
        calc 10 * (N' : ℝ) ^ (1 - ε / 2) * Real.log (2 * (N' : ℝ))
            ≤ 10 * ((N' : ℝ) * (N' : ℝ) ^ (-(ε / 2))) * (2 * Real.log (N' : ℝ)) := by rw [hpow_eq]; gcongr
          _ = 20 * (N' : ℝ) * ((N' : ℝ) ^ (-(ε / 2)) * Real.log (N' : ℝ)) := by ring
          _ ≤ 20 * (N' : ℝ) * (η * ε * τ₀ / 100) := by gcongr
          _ = η * (ε / 4) * τ₀ * (N' : ℝ) * (4 / 5 : ℝ) := by ring
          _ ≤ η * (ε / 4) * τ₀ * (N' : ℝ) * Real.log (N' : ℝ) := by
              gcongr; linarith [show 1 ≤ Real.log (N' : ℝ) by
                have : (1000 : ℝ) ≤ N' := by exact_mod_cast (by omega : 1000 ≤ N')
                have : Real.exp 1 < 1000 := by linarith [Real.exp_one_lt_d9]
                exact (Real.le_log_iff_exp_le (by positivity)).mpr (by linarith)]
      have hden_lb : (ε / 4) * (1 - τ₀) * (N' : ℝ) * Real.log (N' : ℝ) ≤ den_n := by
        have h_band_n := hN_band n (by omega)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h_band_n
        have hden_eq : den_n = ∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
            p.Prime ∧ (n : ℝ) ^ (1 - ε / 2) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) ∧
            padicValNat p (Nat.factorial n) ≡ 1 [MOD 2]),
            (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
          dsimp [den_n, P_I_n]; congr 1; ext p
          simp only [Podd, Finset.mem_filter, Finset.mem_Icc, Real.rpow_one]
          constructor
          · rintro ⟨⟨⟨_, hpn⟩, hp_pr, hp_odd⟩, hp3, hp_gt⟩
            refine ⟨⟨by omega, hpn⟩, hp_pr, hp_gt, by exact_mod_cast hpn, ?_⟩
            rw [Nat.ModEq]; omega
          · rintro ⟨⟨_, hpn⟩, hp_pr, hp_gt, _, hp_mod⟩
            have hp3 : 3 ≤ p := by
              have : (2 : ℝ) < (n : ℝ) ^ (1 - ε / 2) := by
                have h1 : (1000 : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ (1 - ε / 2) := by
                  have : (1000 : ℝ) ^ (1 / 2 : ℝ) ≤ (1000 : ℝ) ^ (1 - ε / 2) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                  exact le_trans this (Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : 1000 ≤ n)) (by linarith))
                have h2 : (2 : ℝ) < (1000 : ℝ) ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow, Real.lt_sqrt (by norm_num)]; norm_num
                linarith
              have : 2 < p := by exact_mod_cast lt_trans this hp_gt
              omega
            refine ⟨⟨⟨by omega, hpn⟩, hp_pr, ?_⟩, hp3, hp_gt⟩
            intro h2d; rw [Nat.ModEq] at hp_mod; omega
        rw [← hden_eq] at h_band_n
        have h1 := (abs_le.mp h_band_n).1
        have h_nlog : (N' : ℝ) * Real.log (N' : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
          gcongr <;> exact_mod_cast hn_mem.1
        nlinarith [show 0 < ε by positivity, show 0 < τ₀ by positivity]
      have h_num_lb : 2 * η * (ε / 4) * (1 - 2 * τ₀) * (N' : ℝ) * Real.log (N' : ℝ) ≤
          |∑ p ∈ P_I, (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) * u n hn p| := by
        have h1 : |∑ p ∈ P_I_n, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) * u n hn p| -
            |∑ p ∈ P_I_n, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) * u n hn p -
              ∑ p ∈ P_I, (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) * u n hn p| ≤
            |∑ p ∈ P_I, (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) * u n hn p| :=
          abs_sub_abs_le_abs_sub _ _
        have h2 : 2 * η * ((ε / 4) * (1 - τ₀) * (N' : ℝ) * Real.log (N' : ℝ)) ≤ 2 * η * den_n := by gcongr
        nlinarith [show 0 < (N' : ℝ) * Real.log (N' : ℝ) by positivity]
      rw [h_uv_eq, abs_div, abs_of_pos (mul_pos hW_tot_pos (Real.sqrt_pos.mpr hW_I_pos)), Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [div_pow, mul_pow, Real.sq_sqrt hW_I_pos.le, le_div_iff₀ (by positivity)]
      have h_sq_lb : (2 * η * (ε / 4) * (1 - 2 * τ₀) * (N' : ℝ) * Real.log (N' : ℝ)) ^ 2 ≤
          |∑ p ∈ P_I, (padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) * u n hn p| ^ 2 :=
        pow_le_pow_left₀ (by positivity) h_num_lb 2
      have h_denom_ub : W_tot ^ 2 * W_I ≤
          ((1 + τ₀ / 2) * (N' : ℝ) * Real.log (N' : ℝ)) ^ 2 * ((ε / 4) * (1 + τ₀)) := by gcongr
      have h_alg : η ^ 2 * ε * (1 - 20 * τ₀) * ((1 + τ₀ / 2) ^ 2 * (ε / 4) * (1 + τ₀)) ≤
          (2 * η * (ε / 4) * (1 - 2 * τ₀)) ^ 2 := by
        have h1 : (1 - 20 * τ₀) * (1 + τ₀ / 2) ^ 2 * (1 + τ₀) ≤ (1 - 2 * τ₀) ^ 2 := by
          nlinarith [show 0 < τ₀ by positivity, show τ₀ < 1 / 100 by exact hτ₀_lt]
        calc η ^ 2 * ε * (1 - 20 * τ₀) * ((1 + τ₀ / 2) ^ 2 * (ε / 4) * (1 + τ₀))
            = (η ^ 2 * ε ^ 2 / 4) * ((1 - 20 * τ₀) * (1 + τ₀ / 2) ^ 2 * (1 + τ₀)) := by ring
          _ ≤ (η ^ 2 * ε ^ 2 / 4) * (1 - 2 * τ₀) ^ 2 := by gcongr
          _ = (2 * η * (ε / 4) * (1 - 2 * τ₀)) ^ 2 := by ring
      calc η ^ 2 * ε * (1 - 20 * τ₀) * (W_tot ^ 2 * W_I)
          ≤ η ^ 2 * ε * (1 - 20 * τ₀) * (((1 + τ₀ / 2) * (N' : ℝ) * Real.log (N' : ℝ)) ^ 2 * ((ε / 4) * (1 + τ₀))) := by gcongr
        _ = (η ^ 2 * ε * (1 - 20 * τ₀) * ((1 + τ₀ / 2) ^ 2 * (ε / 4) * (1 + τ₀))) *
              ((N' : ℝ) * Real.log (N' : ℝ)) ^ 2 := by ring
        _ ≤ (2 * η * (ε / 4) * (1 - 2 * τ₀)) ^ 2 * ((N' : ℝ) * Real.log (N' : ℝ)) ^ 2 := by gcongr
        _ = (2 * η * (ε / 4) * (1 - 2 * τ₀) * (N' : ℝ) * Real.log (N' : ℝ)) ^ 2 := by ring
        _ ≤ _ := h_sq_lb
    have h_uu_ub : ∀ n₁ (hn₁ : n₁ ∈ S_pol) n₂ (hn₂ : n₂ ∈ S_pol), n₁ < n₂ →
        |∑ p ∈ P_base, w p * u n₁ hn₁ p * u n₂ hn₂ p| ≤ τ₀ / ((M : ℝ) + 1) := by
      intro n₁ hn₁ n₂ hn₂ hlt
      have hn1_m := Finset.mem_Icc.mp (Finset.mem_filter.mp hn₁).1
      have hn2_m := Finset.mem_Icc.mp (Finset.mem_filter.mp hn₂).1
      set m₁ := m_fn n₁ hn₁; set m₂ := m_fn n₂ hn₂
      have hm₁ := hm_sq n₁ hn₁; have hm₂ := hm_sq n₂ hn₂
      have ⟨_, _, _, _, hXY, _, _, _, _, hZW, _, _, hprod⟩ :=
        prop_6_1_coprime_and_factorization (by omega) hlt hm₁ hm₂
      have hZW_XY := log_ZW_and_XY_bounds (by omega) hlt hm₁ hm₂
      let P_XY := P_base.filter (fun p => p ∣ X_gcd m₁ m₂ * Y_gcd m₁ m₂)
      let P_ZW := P_base.filter (fun p => p ∣ Z_gcd m₁ m₂ * W_gcd m₁ m₂)
      have hdisj_XZ : Disjoint P_XY P_ZW := by
        rw [Finset.disjoint_left]; intro p h1 h2
        have hp_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
        have hp1 := (Finset.mem_filter.mp h1).2
        have hp2 := (Finset.mem_filter.mp h2).2
        have hcop_all : Nat.Coprime (X_gcd m₁ m₂ * Y_gcd m₁ m₂) (Z_gcd m₁ m₂ * W_gcd m₁ m₂) := by
          have ⟨_, _, _, _, _, hXZ, hXW, hYZ, hYW, _⟩ :=
            prop_6_1_coprime_and_factorization (by omega) hlt hm₁ hm₂
          exact (hXZ.mul_right hXW).mul_left (hYZ.mul_right hYW)
        exact hp_pr.not_dvd_one (hcop_all ▸ Nat.dvd_gcd hp1 hp2)
      have hun_XZ : P_base = P_XY ∪ P_ZW := by
        ext p; simp only [Finset.mem_union, P_XY, P_ZW, Finset.mem_filter, P_base, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hp3, hpN'⟩, hp_pr⟩
          have hp_fac : p ∣ Nat.factorial n₁ := Nat.dvd_factorial hp_pr.pos (by omega)
          have hp_xyzw : p ∣ X_gcd m₁ m₂ * Y_gcd m₁ m₂ * (Z_gcd m₁ m₂ * W_gcd m₁ m₂) := by
            have h1 : 4 * (X_gcd m₁ m₂ * Y_gcd m₁ m₂ * (Z_gcd m₁ m₂ * W_gcd m₁ m₂)) = Nat.factorial n₁ := by
              rw [← hprod]; ring
            rw [← h1] at hp_fac
            have hp2 : p ≠ 2 := by omega
            exact (hp_pr.dvd_mul.mp hp_fac).resolve_left (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_two).mp (hp_pr.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h))))
          rcases hp_pr.dvd_mul.mp hp_xyzw with h1 | h2
          · exact Or.inl ⟨⟨⟨hp3, hpN'⟩, hp_pr⟩, h1⟩
          · exact Or.inr ⟨⟨⟨hp3, hpN'⟩, hp_pr⟩, h2⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      have hsum_XZ : ∑ p ∈ P_base, w p * u n₁ hn₁ p * u n₂ hn₂ p =
          (∑ p ∈ P_XY, w p) - (∑ p ∈ P_ZW, w p) := by
        rw [hun_XZ, Finset.sum_union hdisj_XZ]
        congr 1
        · apply Finset.sum_congr rfl; intro p hp
          have hp_m := Finset.mem_filter.mp hp
          have hp_pr := (Finset.mem_filter.mp hp_m.1).2
          have hcop1 := (brocard_u1_u2_rel (by omega) hm₁).2.2.2.1
          have hcop2 := (brocard_u1_u2_rel (by omega) hm₂).2.2.2.1
          dsimp [u]
          rcases hp_pr.dvd_mul.mp hp_m.2 with hpX | hpY
          · have hp_nB1 : ¬ p ∣ (m₁ + 1) / 2 := fun h => hp_pr.not_dvd_one (hcop1 ▸ Nat.dvd_gcd (dvd_trans hpX (Nat.gcd_dvd_left _ _)) h)
            have hp_nB2 : ¬ p ∣ (m₂ + 1) / 2 := fun h => hp_pr.not_dvd_one (hcop2 ▸ Nat.dvd_gcd (dvd_trans hpX (Nat.gcd_dvd_right _ _)) h)
            rw [if_neg hp_nB1, if_neg hp_nB2]; ring
          · have hp_B1 : p ∣ (m₁ + 1) / 2 := dvd_trans hpY (Nat.gcd_dvd_left _ _)
            have hp_B2 : p ∣ (m₂ + 1) / 2 := dvd_trans hpY (Nat.gcd_dvd_right _ _)
            rw [if_pos hp_B1, if_pos hp_B2]; ring
        · rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro p hp
          have hp_m := Finset.mem_filter.mp hp
          have hp_pr := (Finset.mem_filter.mp hp_m.1).2
          have hcop1 := (brocard_u1_u2_rel (by omega) hm₁).2.2.2.1
          have hcop2 := (brocard_u1_u2_rel (by omega) hm₂).2.2.2.1
          dsimp [u]
          rcases hp_pr.dvd_mul.mp hp_m.2 with hpZ | hpW
          · have hp_A1 : p ∣ (m₁ - 1) / 2 := dvd_trans hpZ (Nat.gcd_dvd_left _ _)
            have hp_nB1 : ¬ p ∣ (m₁ + 1) / 2 := fun h => hp_pr.not_dvd_one (hcop1 ▸ Nat.dvd_gcd hp_A1 h)
            have hp_B2 : p ∣ (m₂ + 1) / 2 := dvd_trans hpZ (Nat.gcd_dvd_right _ _)
            rw [if_neg hp_nB1, if_pos hp_B2]; ring
          · have hp_B1 : p ∣ (m₁ + 1) / 2 := dvd_trans hpW (Nat.gcd_dvd_left _ _)
            have hp_A2 : p ∣ (m₂ - 1) / 2 := dvd_trans hpW (Nat.gcd_dvd_right _ _)
            have hp_nB2 : ¬ p ∣ (m₂ + 1) / 2 := fun h => hp_pr.not_dvd_one (hcop2 ▸ Nat.dvd_gcd hp_A2 h)
            rw [if_pos hp_B1, if_neg hp_nB2]; ring
      have h_a_ub : ∑ p ∈ P_XY, w p ≤ Real.log ((X_gcd m₁ m₂ : ℝ) * Y_gcd m₁ m₂) / W_tot := by
        dsimp [w]; rw [← Finset.sum_div]; gcongr
        have hdvd_XY : ∏ p ∈ P_XY, p ^ padicValNat p (Nat.factorial N') ∣ X_gcd m₁ m₂ * Y_gcd m₁ m₂ := by
          apply Finset.prod_primes_dvd
          · intro p hp
            have hp_m := Finset.mem_filter.mp hp
            have hp_pr := (Finset.mem_filter.mp hp_m.1).2
            haveI : Fact p.Prime := ⟨hp_pr⟩
            have h1 : padicValNat p (Nat.factorial N') ≤ padicValNat p (Nat.factorial n₁) :=
              (Nat.factorization_le_iff_dvd (Nat.factorial_pos N').ne' (Nat.factorial_pos n₁).ne').mpr
                (Nat.factorial_dvd_factorial hn1_m.1) p
            have h2 : padicValNat p (Nat.factorial n₁) ≤ padicValNat p (X_gcd m₁ m₂ * Y_gcd m₁ m₂) := by
              have h_cop_ZW : Nat.Coprime (p ^ padicValNat p (Nat.factorial n₁)) (4 * (Z_gcd m₁ m₂ * W_gcd m₁ m₂)) := by
                apply Nat.Coprime.pow_left
                have hp3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp_m.1).1).1
                have hp2 : p ≠ 2 := by omega
                have hcop4 := hp_pr.coprime_iff_not_dvd.mpr (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_two).mp (hp_pr.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h))))
                have hndvd_ZW : ¬ p ∣ Z_gcd m₁ m₂ * W_gcd m₁ m₂ := fun hzw =>
                  Finset.disjoint_left.mp hdisj_XZ hp (Finset.mem_filter.mpr ⟨hp_m.1, hzw⟩)
                exact hcop4.mul_right (hp_pr.coprime_iff_not_dvd.mpr hndvd_ZW)
              have hfac_eq : 4 * (Z_gcd m₁ m₂ * W_gcd m₁ m₂) * (X_gcd m₁ m₂ * Y_gcd m₁ m₂) = Nat.factorial n₁ := by
                rw [← hprod]; ring
              have hpow_dvd : p ^ padicValNat p (Nat.factorial n₁) ∣ X_gcd m₁ m₂ * Y_gcd m₁ m₂ :=
                h_cop_ZW.dvd_of_dvd_mul_left (hfac_eq.symm ▸ pow_padicValNat_dvd)
              have ⟨hX_pos, hY_pos, _⟩ := prop_6_1_coprime_and_factorization (by omega) hlt hm₁ hm₂
              exact (Nat.factorization_le_iff_dvd (pow_pos hp_pr.pos _).ne' (mul_pos hX_pos hY_pos).ne').mpr hpow_dvd p |>.trans' (by
                simp [Nat.factorization_def _ hp_pr, padicValNat_pow_eq, padicValNat_self])
            exact dvd_trans (pow_dvd_pow p h1) (dvd_trans (pow_dvd_pow p h2) pow_padicValNat_dvd)
          · intro p hp q hq hpq
            exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
              (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2).mpr hpq)
        have ⟨hX_pos, hY_pos, _⟩ := prop_6_1_coprime_and_factorization (by omega) hlt hm₁ hm₂
        have hpos_p : 0 < ∏ p ∈ P_XY, p ^ padicValNat p (Nat.factorial N') :=
          Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.pos _)
        have hle := Real.log_le_log (by exact_mod_cast hpos_p) (by exact_mod_cast Nat.le_of_dvd (mul_pos hX_pos hY_pos) hdvd_XY)
        rw [Nat.cast_prod, Real.log_prod _ _ (fun p hp => pow_ne_zero _ (by
          exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.ne_zero))] at hle
        refine le_trans (le_of_eq ?_) hle
        apply Finset.sum_congr rfl; intro p _; rw [Nat.cast_pow, Real.log_pow]
      have h_b_ub : ∑ p ∈ P_ZW, w p ≤ Real.log ((Z_gcd m₁ m₂ : ℝ) * W_gcd m₁ m₂) / W_tot := by
        dsimp [w]; rw [← Finset.sum_div]; gcongr
        have hdvd_ZW : ∏ p ∈ P_ZW, p ^ padicValNat p (Nat.factorial N') ∣ Z_gcd m₁ m₂ * W_gcd m₁ m₂ := by
          apply Finset.prod_primes_dvd
          · intro p hp
            have hp_m := Finset.mem_filter.mp hp
            have hp_pr := (Finset.mem_filter.mp hp_m.1).2
            haveI : Fact p.Prime := ⟨hp_pr⟩
            have h1 : padicValNat p (Nat.factorial N') ≤ padicValNat p (Nat.factorial n₁) :=
              (Nat.factorization_le_iff_dvd (Nat.factorial_pos N').ne' (Nat.factorial_pos n₁).ne').mpr
                (Nat.factorial_dvd_factorial hn1_m.1) p
            have h2 : padicValNat p (Nat.factorial n₁) ≤ padicValNat p (Z_gcd m₁ m₂ * W_gcd m₁ m₂) := by
              have h_cop_XY : Nat.Coprime (p ^ padicValNat p (Nat.factorial n₁)) (4 * (X_gcd m₁ m₂ * Y_gcd m₁ m₂)) := by
                apply Nat.Coprime.pow_left
                have hp3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp_m.1).1).1
                have hp2 : p ≠ 2 := by omega
                have hcop4 := hp_pr.coprime_iff_not_dvd.mpr (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_two).mp (hp_pr.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h))))
                have hndvd_XY : ¬ p ∣ X_gcd m₁ m₂ * Y_gcd m₁ m₂ := fun hxy =>
                  Finset.disjoint_left.mp hdisj_XZ (Finset.mem_filter.mpr ⟨hp_m.1, hxy⟩) hp
                exact hcop4.mul_right (hp_pr.coprime_iff_not_dvd.mpr hndvd_XY)
              have hfac_eq : 4 * (X_gcd m₁ m₂ * Y_gcd m₁ m₂) * (Z_gcd m₁ m₂ * W_gcd m₁ m₂) = Nat.factorial n₁ := by
                rw [← hprod]; ring
              have hpow_dvd : p ^ padicValNat p (Nat.factorial n₁) ∣ Z_gcd m₁ m₂ * W_gcd m₁ m₂ :=
                h_cop_XY.dvd_of_dvd_mul_left (hfac_eq.symm ▸ pow_padicValNat_dvd)
              have ⟨_, _, hZ_pos, hW_pos, _⟩ := prop_6_1_coprime_and_factorization (by omega) hlt hm₁ hm₂
              exact (Nat.factorization_le_iff_dvd (pow_pos hp_pr.pos _).ne' (mul_pos hZ_pos hW_pos).ne').mpr hpow_dvd p |>.trans' (by
                simp [Nat.factorization_def _ hp_pr, padicValNat_pow_eq, padicValNat_self])
            exact dvd_trans (pow_dvd_pow p h1) (dvd_trans (pow_dvd_pow p h2) pow_padicValNat_dvd)
          · intro p hp q hq hpq
            exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
              (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2).mpr hpq)
        have ⟨_, _, hZ_pos, hW_pos, _⟩ := prop_6_1_coprime_and_factorization (by omega) hlt hm₁ hm₂
        have hpos_p : 0 < ∏ p ∈ P_ZW, p ^ padicValNat p (Nat.factorial N') :=
          Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.pos _)
        have hle := Real.log_le_log (by exact_mod_cast hpos_p) (by exact_mod_cast Nat.le_of_dvd (mul_pos hZ_pos hW_pos) hdvd_ZW)
        rw [Nat.cast_prod, Real.log_prod _ _ (fun p hp => pow_ne_zero _ (by
          exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.ne_zero))] at hle
        refine le_trans (le_of_eq ?_) hle
        apply Finset.sum_congr rfl; intro p _; rw [Nat.cast_pow, Real.log_pow]
      have h_ab_sum : (∑ p ∈ P_XY, w p) + (∑ p ∈ P_ZW, w p) = 1 := by
        rw [← Finset.sum_union hdisj_XZ, ← hun_XZ, hw_sum]
      have h_bound_common : Real.log (Nat.factorial n₁ : ℝ) + 12 * Real.log (P_ratio n₁ n₂ : ℝ) + 8 - W_tot ≤
          (τ₀ / ((M : ℝ) + 1)) * W_tot := by
        have hfac_n1 : Real.log (Nat.factorial n₁ : ℝ) ≤ (N' : ℝ) * Real.log (N' : ℝ) + (N' : ℝ) ^ (1 - ε) * Real.log (2 * (N' : ℝ)) := by
          have h1 : Real.log (Nat.factorial N' : ℝ) ≤ (N' : ℝ) * Real.log (N' : ℝ) := by
            have := Real.log_le_log (by exact_mod_cast Nat.factorial_pos N') (by exact_mod_cast Nat.factorial_le_pow N')
            rwa [Nat.cast_pow, Real.log_pow] at this
          have hmul : Nat.factorial n₁ = (Nat.factorial n₁ / Nat.factorial N') * Nat.factorial N' :=
            (Nat.div_mul_cancel (Nat.factorial_dvd_factorial hn1_m.1)).symm
          have hpos_d : 0 < Nat.factorial n₁ / Nat.factorial N' := Nat.div_pos (Nat.factorial_le hn1_m.1) (Nat.factorial_pos N')
          have hlog_eq : Real.log (Nat.factorial n₁ : ℝ) =
              Real.log ((Nat.factorial n₁ / Nat.factorial N' : ℕ) : ℝ) + Real.log (Nat.factorial N' : ℝ) := by
            rw [hmul, Nat.cast_mul, Real.log_mul (by exact_mod_cast hpos_d.ne') (by exact_mod_cast (Nat.factorial_pos N').ne')]
          have h_d_le : Real.log ((Nat.factorial n₁ / Nat.factorial N' : ℕ) : ℝ) ≤ (N' : ℝ) ^ (1 - ε) * Real.log (2 * (N' : ℝ)) := by
            by_cases heq : n₁ = N'
            · subst heq; rw [Nat.div_self (Nat.factorial_pos _)]; simp; positivity
            · have hlt_N : N' < n₁ := by omega
              have hprod_eq : Nat.factorial n₁ / Nat.factorial N' = ∏ j ∈ Finset.Ioc N' n₁, j := by
                have hfac := Nat.div_mul_cancel (Nat.factorial_dvd_factorial hlt_N.le)
                have hprod' : Nat.factorial n₁ = Nat.factorial N' * ∏ j ∈ Finset.Ioc N' n₁, j := by
                  have hle : N' ≤ n₁ := hlt_N.le
                  induction n₁, hle using Nat.le_induction with
                  | base => simp
                  | succ k hk ih => rw [Nat.factorial_succ, Finset.prod_Ioc_succ_top hk, ih]; ring
                have : (Nat.factorial n₁ / Nat.factorial N') * Nat.factorial N' =
                    (∏ j ∈ Finset.Ioc N' n₁, j) * Nat.factorial N' := by rw [hfac, hprod']; ring
                exact mul_right_cancel₀ (Nat.factorial_pos N').ne' this
              have hn1_2N' : (n₁ : ℝ) ≤ 2 * (N' : ℝ) := by
                have h1' : (L : ℝ) ≤ (N' : ℝ) ^ (1 - ε) := Nat.floor_le (by positivity)
                have h2' : (N' : ℝ) ^ (1 - ε) ≤ (N' : ℝ) := by
                  calc (N' : ℝ) ^ (1 - ε) ≤ (N' : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N')) (by linarith)
                    _ = (N' : ℝ) := Real.rpow_one _
                have : (n₁ : ℝ) ≤ (N' : ℝ) + (L : ℝ) := by exact_mod_cast hn1_m.2
                linarith
              have hle_nat : ∏ j ∈ Finset.Ioc N' n₁, j ≤ (2 * N') ^ (n₁ - N') := by
                calc ∏ j ∈ Finset.Ioc N' n₁, j ≤ ∏ _j ∈ Finset.Ioc N' n₁, (2 * N') :=
                      Finset.prod_le_prod' (fun j hj => by
                        have := (Finset.mem_Ioc.mp hj).2
                        exact_mod_cast le_trans (by exact_mod_cast this) hn1_2N')
                  _ = (2 * N') ^ (Finset.Ioc N' n₁).card := Finset.prod_const _
                  _ = (2 * N') ^ (n₁ - N') := by rw [Nat.card_Ioc]
              have h2 := Real.log_le_log (by exact_mod_cast hpos_d) (by exact_mod_cast (hprod_eq ▸ hle_nat))
              rw [Nat.cast_pow, Real.log_pow] at h2
              have hsub_le : ((n₁ - N' : ℕ) : ℝ) ≤ (N' : ℝ) ^ (1 - ε) := by
                have : n₁ - N' ≤ L := by omega
                exact le_trans (by exact_mod_cast this) (Nat.floor_le (by positivity))
              have hlog2N : 0 ≤ Real.log (2 * (N' : ℝ)) := Real.log_nonneg (by linarith [show (1000 : ℝ) ≤ N' by exact_mod_cast (by omega : 1000 ≤ N')])
              exact le_trans h2 (mul_le_mul_of_nonneg_right hsub_le hlog2N)
          linarith
        have hlogP_le : 12 * Real.log (P_ratio n₁ n₂ : ℝ) ≤ 12 * (N' : ℝ) ^ (1 - ε) * Real.log (4 * (N' : ℝ)) := by
          have hn2_4N' : (n₂ : ℝ) ≤ 4 * (N' : ℝ) := by
            have h1' : (L : ℝ) ≤ (N' : ℝ) ^ (1 - ε) := Nat.floor_le (by positivity)
            have h2' : (N' : ℝ) ^ (1 - ε) ≤ (N' : ℝ) := by
              calc (N' : ℝ) ^ (1 - ε) ≤ (N' : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N')) (by linarith)
                _ = (N' : ℝ) := Real.rpow_one _
            have : (n₂ : ℝ) ≤ (N' : ℝ) + (L : ℝ) := by exact_mod_cast hn2_m.2
            linarith
          have hP_eq : P_ratio n₁ n₂ = ∏ j ∈ Finset.Ioc n₁ n₂, j := by
            have hfac := P_ratio_mul_factorial hlt
            have hprod' : Nat.factorial n₂ = Nat.factorial n₁ * ∏ j ∈ Finset.Ioc n₁ n₂, j := by
              have hle : n₁ ≤ n₂ := hlt.le
              induction n₂, hle using Nat.le_induction with
              | base => simp
              | succ k hk ih => rw [Nat.factorial_succ, Finset.prod_Ioc_succ_top hk, ih]; ring
            have : P_ratio n₁ n₂ * Nat.factorial n₁ = (∏ j ∈ Finset.Ioc n₁ n₂, j) * Nat.factorial n₁ := by rw [hfac, hprod']; ring
            exact mul_right_cancel₀ (Nat.factorial_pos n₁).ne' this
          have hle_nat : ∏ j ∈ Finset.Ioc n₁ n₂, j ≤ (4 * N') ^ (n₂ - n₁) := by
            calc ∏ j ∈ Finset.Ioc n₁ n₂, j ≤ ∏ _j ∈ Finset.Ioc n₁ n₂, (4 * N') :=
                  Finset.prod_le_prod' (fun j hj => by
                    have := (Finset.mem_Ioc.mp hj).2
                    exact_mod_cast le_trans (by exact_mod_cast this) hn2_4N')
              _ = (4 * N') ^ (Finset.Ioc n₁ n₂).card := Finset.prod_const _
              _ = (4 * N') ^ (n₂ - n₁) := by rw [Nat.card_Ioc]
          have hP_pos : 0 < P_ratio n₁ n₂ := by have := P_ratio_ge_two (by omega : 4 ≤ n₁) hlt; omega
          have h2 := Real.log_le_log (by exact_mod_cast hP_pos) (by exact_mod_cast (hP_eq ▸ hle_nat))
          rw [Nat.cast_pow, Real.log_pow] at h2
          have hsub_le : ((n₂ - n₁ : ℕ) : ℝ) ≤ (N' : ℝ) ^ (1 - ε) := by
            have : n₂ - n₁ ≤ L := by omega
            exact le_trans (by exact_mod_cast this) (Nat.floor_le (by positivity))
          have hlog4N : 0 ≤ Real.log (4 * (N' : ℝ)) := Real.log_nonneg (by linarith [show (1000 : ℝ) ≤ N' by exact_mod_cast (by omega : 1000 ≤ N')])
          have h3 : Real.log (P_ratio n₁ n₂ : ℝ) ≤ (N' : ℝ) ^ (1 - ε) * Real.log (4 * (N' : ℝ)) :=
            le_trans h2 (mul_le_mul_of_nonneg_right hsub_le hlog4N)
          linarith
        have h_e1 := hN_e1 N' (by omega)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h_e1
        have h_il_t := hN_il_tau N' (by omega)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h_il_t
        have hlog4N : Real.log (4 * (N' : ℝ)) ≤ 2 * Real.log (N' : ℝ) := by
          rw [Real.log_mul (by norm_num) (by positivity)]
          have : Real.log 4 ≤ Real.log (N' : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 4 ≤ N'))
          linarith
        have hlog2N : Real.log (2 * (N' : ℝ)) ≤ 2 * Real.log (N' : ℝ) := by
          rw [Real.log_mul (by norm_num) (by positivity)]
          have : Real.log 2 ≤ Real.log (N' : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ N'))
          linarith
        have hpow_eq : (N' : ℝ) ^ (1 - ε) = (N' : ℝ) * (N' : ℝ) ^ (-ε) := by
          rw [← Real.rpow_one_add' (by positivity) (by linarith : 1 + -ε ≠ 0)]; ring_nf
        have h_term1 : (N' : ℝ) ^ (1 - ε) * Real.log (2 * (N' : ℝ)) +
            12 * (N' : ℝ) ^ (1 - ε) * Real.log (4 * (N' : ℝ)) ≤
            26 * (N' : ℝ) ^ (-ε) * (N' : ℝ) * Real.log (N' : ℝ) := by
          rw [hpow_eq]; gcongr <;> nlinarith
        have hW_tight : (N' : ℝ) * Real.log (N' : ℝ) - W_tot ≤
            (τ₀ / (50 * ((M : ℝ) + 1))) * (N' : ℝ) * Real.log (N' : ℝ) := by
          have h1 := (abs_le.mp hSodd_bd_tight).1; have h2 := (abs_le.mp hSeven_bd_tight).1
          dsimp [W_tot]; linarith
        have h8_le : (8 : ℝ) ≤ (τ₀ / (10 * ((M : ℝ) + 1))) * (N' : ℝ) * Real.log (N' : ℝ) := by
          have h1 := (div_lt_iff₀ hlogN'_pos).mp h_il_t
          nlinarith [show (8 : ℝ) ≤ (N' : ℝ) by exact_mod_cast (by omega : 8 ≤ N')]
        have h26_le : 26 * (N' : ℝ) ^ (-ε) * (N' : ℝ) * Real.log (N' : ℝ) ≤
            (τ₀ / (3 * ((M : ℝ) + 1))) * (N' : ℝ) * Real.log (N' : ℝ) := by
          have : 26 * (N' : ℝ) ^ (-ε) ≤ τ₀ / (3 * ((M : ℝ) + 1)) := by nlinarith
          nlinarith [show 0 ≤ (N' : ℝ) * Real.log (N' : ℝ) by positivity]
        have hW_half : (1 / 2 : ℝ) * (N' : ℝ) * Real.log (N' : ℝ) ≤ W_tot := by
          nlinarith [hτ₀_lt, show 0 ≤ (N' : ℝ) * Real.log (N' : ℝ) by positivity]
        nlinarith [show 0 ≤ τ₀ / ((M : ℝ) + 1) by positivity]
      rw [hsum_XZ, abs_le]
      have h1 : (∑ p ∈ P_XY, w p) - (∑ p ∈ P_ZW, w p) = 2 * (∑ p ∈ P_XY, w p) - 1 := by linarith
      have h2 : (∑ p ∈ P_XY, w p) - (∑ p ∈ P_ZW, w p) = 1 - 2 * (∑ p ∈ P_ZW, w p) := by linarith
      constructor
      · rw [h2]; have := (abs_le.mp hZW_XY.1).2; rw [le_div_iff₀ hW_tot_pos] at h_b_ub; linarith
      · rw [h1]; have := (abs_le.mp hZW_XY.2).2; rw [le_div_iff₀ hW_tot_pos] at h_a_ub; linarith
    let sgn : ∀ n, n ∈ S_pol → ℝ := fun n hn =>
      if 0 ≤ ∑ p ∈ P_base, w p * u n hn p * v_I p then 1 else -1
    let X_vec : ℕ → ℝ := fun p => ∑ hn ∈ S_pol.attach, sgn hn.1 hn.2 * u hn.1 hn.2 p
    have h_cs : (∑ hn ∈ S_pol.attach, |∑ p ∈ P_base, w p * u hn.1 hn.2 p * v_I p|) ^ 2 ≤
        (∑ p ∈ P_base, w p * (X_vec p) ^ 2) * (∑ p ∈ P_base, w p * (v_I p) ^ 2) := by
      have h_lhs_eq : ∑ hn ∈ S_pol.attach, |∑ p ∈ P_base, w p * u hn.1 hn.2 p * v_I p| =
          ∑ p ∈ P_base, (Real.sqrt (w p) * X_vec p) * (Real.sqrt (w p) * v_I p) := by
        have h1 : ∀ hn ∈ S_pol.attach, |∑ p ∈ P_base, w p * u hn.1 hn.2 p * v_I p| =
            sgn hn.1 hn.2 * ∑ p ∈ P_base, w p * u hn.1 hn.2 p * v_I p := by
          intro hn _; dsimp [sgn]; split_ifs with h
          · rw [one_mul, abs_of_nonneg h]
          · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]
        rw [Finset.sum_congr rfl h1]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro p _
        dsimp [X_vec]; rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro hn _
        have hsq : Real.sqrt (w p) * Real.sqrt (w p) = w p := Real.mul_self_sqrt (hw_nn p)
        calc sgn hn.1 hn.2 * (w p * u hn.1 hn.2 p * v_I p)
            = (w p) * (sgn hn.1 hn.2 * u hn.1 hn.2 p) * v_I p := by ring
          _ = (Real.sqrt (w p) * Real.sqrt (w p)) * (sgn hn.1 hn.2 * u hn.1 hn.2 p) * v_I p := by rw [hsq]
          _ = Real.sqrt (w p) * (sgn hn.1 hn.2 * u hn.1 hn.2 p) * (Real.sqrt (w p) * v_I p) := by ring
      rw [h_lhs_eq]
      have h_sq1 : ∑ p ∈ P_base, (Real.sqrt (w p) * X_vec p) ^ 2 = ∑ p ∈ P_base, w p * (X_vec p) ^ 2 := by
        apply Finset.sum_congr rfl; intro p _; rw [mul_pow, Real.sq_sqrt (hw_nn p)]
      have h_sq2 : ∑ p ∈ P_base, (Real.sqrt (w p) * v_I p) ^ 2 = ∑ p ∈ P_base, w p * (v_I p) ^ 2 := by
        apply Finset.sum_congr rfl; intro p _; rw [mul_pow, Real.sq_sqrt (hw_nn p)]
      rw [← h_sq1, ← h_sq2]
      exact Finset.sum_mul_sq_le_sq_mul_sq P_base (fun p => Real.sqrt (w p) * X_vec p) (fun p => Real.sqrt (w p) * v_I p)
    have h_X_norm : ∑ p ∈ P_base, w p * (X_vec p) ^ 2 ≤
        (t : ℝ) + (t : ℝ) * ((t : ℝ) - 1) * (τ₀ / ((M : ℝ) + 1)) := by
      have h_exp : ∑ p ∈ P_base, w p * (X_vec p) ^ 2 =
          ∑ hn₁ ∈ S_pol.attach, ∑ hn₂ ∈ S_pol.attach,
            sgn hn₁.1 hn₁.2 * sgn hn₂.1 hn₂.2 * ∑ p ∈ P_base, w p * u hn₁.1 hn₁.2 p * u hn₂.1 hn₂.2 p := by
        dsimp [X_vec]
        have h1 : ∀ p ∈ P_base, w p * (∑ hn ∈ S_pol.attach, sgn hn.1 hn.2 * u hn.1 hn.2 p) ^ 2 =
            ∑ hn₁ ∈ S_pol.attach, ∑ hn₂ ∈ S_pol.attach,
              sgn hn₁.1 hn₁.2 * sgn hn₂.1 hn₂.2 * (w p * u hn₁.1 hn₁.2 p * u hn₂.1 hn₂.2 p) := by
          intro p _; rw [sq, Finset.sum_mul]; simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro hn₁ _
          apply Finset.sum_congr rfl; intro hn₂ _; ring
        rw [Finset.sum_congr rfl h1, Finset.sum_comm]
        apply Finset.sum_congr rfl; intro hn₁ _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro hn₂ _
        rw [← Finset.mul_sum]
      rw [h_exp]
      have h_diag : ∑ hn₁ ∈ S_pol.attach,
          (if hn₁ = hn₁ then sgn hn₁.1 hn₁.2 * sgn hn₁.1 hn₁.2 * ∑ p ∈ P_base, w p * u hn₁.1 hn₁.2 p * u hn₁.1 hn₁.2 p else 0) =
          (t : ℝ) := by
        have h1 : ∀ hn ∈ S_pol.attach,
            sgn hn.1 hn.2 * sgn hn.1 hn.2 * ∑ p ∈ P_base, w p * u hn.1 hn.2 p * u hn.1 hn.2 p = 1 := by
          intro hn _
          have hs : sgn hn.1 hn.2 * sgn hn.1 hn.2 = 1 := by dsimp [sgn]; split_ifs <;> ring
          have hu : ∑ p ∈ P_base, w p * u hn.1 hn.2 p * u hn.1 hn.2 p = 1 := by
            have := hu_norm hn.1 hn.2; simpa [sq, mul_assoc] using this
          rw [hs, hu, mul_one]
        simp only [↓reduceIte]
        rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_attach, nsmul_eq_mul, mul_one]
      have h_off : ∀ hn₁ ∈ S_pol.attach, ∀ hn₂ ∈ S_pol.attach, hn₁ ≠ hn₂ →
          sgn hn₁.1 hn₁.2 * sgn hn₂.1 hn₂.2 * ∑ p ∈ P_base, w p * u hn₁.1 hn₁.2 p * u hn₂.1 hn₂.2 p ≤
            τ₀ / ((M : ℝ) + 1) := by
        intro hn₁ _ hn₂ _ hne
        have hs1 : |sgn hn₁.1 hn₁.2| = 1 := by dsimp [sgn]; split_ifs <;> norm_num
        have hs2 : |sgn hn₂.1 hn₂.2| = 1 := by dsimp [sgn]; split_ifs <;> norm_num
        have hne_val : hn₁.1 ≠ hn₂.1 := fun h => hne (Subtype.ext h)
        have h_abs : |∑ p ∈ P_base, w p * u hn₁.1 hn₁.2 p * u hn₂.1 hn₂.2 p| ≤ τ₀ / ((M : ℝ) + 1) := by
          rcases lt_or_gt_of_ne hne_val with hlt | hgt
          · exact h_uu_ub hn₁.1 hn₁.2 hn₂.1 hn₂.2 hlt
          · rw [show (∑ p ∈ P_base, w p * u hn₁.1 hn₁.2 p * u hn₂.1 hn₂.2 p) =
              ∑ p ∈ P_base, w p * u hn₂.1 hn₂.2 p * u hn₁.1 hn₁.2 p by
              apply Finset.sum_congr rfl; intro p _; ring]
            exact h_uu_ub hn₂.1 hn₂.2 hn₁.1 hn₁.2 hgt
        calc sgn hn₁.1 hn₁.2 * sgn hn₂.1 hn₂.2 * _ ≤ |sgn hn₁.1 hn₁.2 * sgn hn₂.1 hn₂.2 * _| := le_abs_self _
          _ = |sgn hn₁.1 hn₁.2| * |sgn hn₂.1 hn₂.2| * |_| := by rw [abs_mul, abs_mul]
          _ ≤ 1 * 1 * (τ₀ / ((M : ℝ) + 1)) := by rw [hs1, hs2]; gcongr
          _ = τ₀ / ((M : ℝ) + 1) := by ring
      have h_split : ∑ hn₁ ∈ S_pol.attach, ∑ hn₂ ∈ S_pol.attach,
          sgn hn₁.1 hn₁.2 * sgn hn₂.1 hn₂.2 * ∑ p ∈ P_base, w p * u hn₁.1 hn₁.2 p * u hn₂.1 hn₂.2 p =
          (∑ hn₁ ∈ S_pol.attach, sgn hn₁.1 hn₁.2 * sgn hn₁.1 hn₁.2 * ∑ p ∈ P_base, w p * u hn₁.1 hn₁.2 p * u hn₁.1 hn₁.2 p) +
          (∑ hn₁ ∈ S_pol.attach, ∑ hn₂ ∈ S_pol.attach.erase hn₁,
            sgn hn₁.1 hn₁.2 * sgn hn₂.1 hn₂.2 * ∑ p ∈ P_base, w p * u hn₁.1 hn₁.2 p * u hn₂.1 hn₂.2 p) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro hn₁ h1
        rw [Finset.add_sum_erase _ _ h1]
      rw [h_split]
      have h_diag_eq : (∑ hn₁ ∈ S_pol.attach, sgn hn₁.1 hn₁.2 * sgn hn₁.1 hn₁.2 * ∑ p ∈ P_base, w p * u hn₁.1 hn₁.2 p * u hn₁.1 hn₁.2 p) = (t : ℝ) := by
        simpa using h_diag
      have h_off_le : (∑ hn₁ ∈ S_pol.attach, ∑ hn₂ ∈ S_pol.attach.erase hn₁,
          sgn hn₁.1 hn₁.2 * sgn hn₂.1 hn₂.2 * ∑ p ∈ P_base, w p * u hn₁.1 hn₁.2 p * u hn₂.1 hn₂.2 p) ≤
          (t : ℝ) * ((t : ℝ) - 1) * (τ₀ / ((M : ℝ) + 1)) := by
        have h1 : ∀ hn₁ ∈ S_pol.attach, ∑ hn₂ ∈ S_pol.attach.erase hn₁,
            sgn hn₁.1 hn₁.2 * sgn hn₂.1 hn₂.2 * ∑ p ∈ P_base, w p * u hn₁.1 hn₁.2 p * u hn₂.1 hn₂.2 p ≤
            ((t : ℝ) - 1) * (τ₀ / ((M : ℝ) + 1)) := by
          intro hn₁ h1
          have hcard : ((S_pol.attach.erase hn₁).card : ℝ) = (t : ℝ) - 1 := by
            rw [Finset.card_erase_of_mem h1, Finset.card_attach]
            have : 1 ≤ t := by omega
            zify [this]; ring
          calc ∑ hn₂ ∈ S_pol.attach.erase hn₁, _ ≤ ∑ _hn₂ ∈ S_pol.attach.erase hn₁, (τ₀ / ((M : ℝ) + 1)) :=
                Finset.sum_le_sum (fun hn₂ h2 => h_off hn₁ h1 hn₂ (Finset.mem_of_mem_erase h2) (Finset.ne_of_mem_erase h2).symm)
            _ = ((t : ℝ) - 1) * (τ₀ / ((M : ℝ) + 1)) := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
        calc ∑ hn₁ ∈ S_pol.attach, _ ≤ ∑ _hn₁ ∈ S_pol.attach, ((t : ℝ) - 1) * (τ₀ / ((M : ℝ) + 1)) := Finset.sum_le_sum h1
          _ = (t : ℝ) * ((t : ℝ) - 1) * (τ₀ / ((M : ℝ) + 1)) := by
              rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]; ring
      linarith
    have h_lhs_lb : (t : ℝ) ^ 2 * (η ^ 2 * ε * (1 - 20 * τ₀)) ≤
        (∑ hn ∈ S_pol.attach, |∑ p ∈ P_base, w p * u hn.1 hn.2 p * v_I p|) ^ 2 := by
      have h1 : (t : ℝ) * Real.sqrt (η ^ 2 * ε * (1 - 20 * τ₀)) ≤
          ∑ hn ∈ S_pol.attach, |∑ p ∈ P_base, w p * u hn.1 hn.2 p * v_I p| := by
        calc (t : ℝ) * Real.sqrt (η ^ 2 * ε * (1 - 20 * τ₀))
            = ∑ _hn ∈ S_pol.attach, Real.sqrt (η ^ 2 * ε * (1 - 20 * τ₀)) := by
              rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
          _ ≤ ∑ hn ∈ S_pol.attach, |∑ p ∈ P_base, w p * u hn.1 hn.2 p * v_I p| :=
              Finset.sum_le_sum (fun hn _ => h_uv_lb hn.1 hn.2)
      have h2 := pow_le_pow_left₀ (by positivity) h1 2
      rw [mul_pow, Real.sq_sqrt (by nlinarith [hτ₀_lt])] at h2
      exact h2
    have ht_pos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
    have h_div_t : (t : ℝ) * (η ^ 2 * ε * (1 - 20 * τ₀) - τ₀) ≤ 1 := by
      have h1 : (t : ℝ) ^ 2 * (η ^ 2 * ε * (1 - 20 * τ₀)) ≤
          (t : ℝ) + (t : ℝ) ^ 2 * τ₀ := by
        have h_tau : (t : ℝ) * ((t : ℝ) - 1) * (τ₀ / ((M : ℝ) + 1)) ≤ (t : ℝ) ^ 2 * τ₀ := by
          have : ((t : ℝ) - 1) / ((M : ℝ) + 1) ≤ (t : ℝ) := by
            rw [div_le_iff₀ (by positivity)]
            have : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ M by positivity]
            nlinarith
          calc (t : ℝ) * ((t : ℝ) - 1) * (τ₀ / ((M : ℝ) + 1))
              = (t : ℝ) * (((t : ℝ) - 1) / ((M : ℝ) + 1)) * τ₀ := by ring
            _ ≤ (t : ℝ) * (t : ℝ) * τ₀ := by gcongr
            _ = (t : ℝ) ^ 2 * τ₀ := by ring
        linarith [h_lhs_lb, h_cs, hv_I_norm, h_X_norm]
      have h2 : (t : ℝ) * ((t : ℝ) * (η ^ 2 * ε * (1 - 20 * τ₀) - τ₀)) ≤ (t : ℝ) * 1 := by
        linarith
      exact le_of_mul_le_mul_left h2 ht_pos
    have hM_gt : 1 + η ^ 2 * ε < ((M : ℝ) + 1) * (η ^ 2 * ε) := by
      have hfl : (η ^ 2 * ε)⁻¹ < (M : ℝ) := by
        dsimp [M]; exact Nat.lt_floor_add_one _
      calc 1 + η ^ 2 * ε = ((η ^ 2 * ε)⁻¹ + 1) * (η ^ 2 * ε) := by
            field_simp [(by positivity : η ^ 2 * ε ≠ 0)]
        _ < ((M : ℝ) + 1) * (η ^ 2 * ε) := by gcongr
    have ht_mul : 1 + η ^ 2 * ε < (t : ℝ) * (η ^ 2 * ε) := by
      have : ((M : ℝ) + 1) ≤ (t : ℝ) := by exact_mod_cast ht_ge
      calc 1 + η ^ 2 * ε < ((M : ℝ) + 1) * (η ^ 2 * ε) := hM_gt
        _ ≤ (t : ℝ) * (η ^ 2 * ε) := by gcongr
    have h_contra : 1 < (t : ℝ) * (η ^ 2 * ε * (1 - 20 * τ₀) - τ₀) := by
      have h_coeff : η ^ 2 * ε * (1 - 20 * τ₀) - τ₀ ≥ (η ^ 2 * ε) * (1 - 21 / (1000 * (1 + η ^ 2 * ε))) := by
        dsimp [τ₀]
        have h1 : 20 * (η ^ 2 * ε) * (η ^ 2 * ε) / (1000 * (1 + η ^ 2 * ε)) ≤
            20 * (η ^ 2 * ε) / (1000 * (1 + η ^ 2 * ε)) := by
          gcongr
          have : η ^ 2 * ε ≤ 1 := by nlinarith
          nlinarith
        linarith
      have h_prod : (1 + η ^ 2 * ε) * (1 - 21 / (1000 * (1 + η ^ 2 * ε))) ≥ 1 := by
        have h1 : 1 + η ^ 2 * ε > 0 := by positivity
        field_simp [h1.ne']
        nlinarith [show 0 < η ^ 2 * ε by positivity]
      calc 1 ≤ (1 + η ^ 2 * ε) * (1 - 21 / (1000 * (1 + η ^ 2 * ε))) := h_prod
        _ < ((t : ℝ) * (η ^ 2 * ε)) * (1 - 21 / (1000 * (1 + η ^ 2 * ε))) := by
            gcongr; have : 0 < 1 - 21 / (1000 * (1 + η ^ 2 * ε)) := by
              rw [sub_pos, div_lt_one (by positivity)]; nlinarith [show 0 < η ^ 2 * ε by positivity]
            exact this
        _ = (t : ℝ) * ((η ^ 2 * ε) * (1 - 21 / (1000 * (1 + η ^ 2 * ε)))) := by ring
        _ ≤ (t : ℝ) * (η ^ 2 * ε * (1 - 20 * τ₀) - τ₀) := by gcongr
    linarith
  refine ⟨N₀, by omega, h_int_bd, ?_⟩
  classical
  have h_int_bd' : ∀ N' : ℕ, N₀ ≤ N' →
      ((Finset.Icc N' (N' + Nat.floor ((N' : ℝ) ^ (1 - ε)))).filter (PolBad ε η)).card ≤ M := by
    intro N' hN'
    convert h_int_bd N' hN' using 2
  have h2e_gt : 1 < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε0
  let C_pol : ℝ := (N₀ : ℝ) + 8 * (2 : ℝ) ^ ε / (ε * ((2 : ℝ) ^ ε - 1))
  refine ⟨C_pol, by positivity, fun N hN => ?_⟩
  change (((Finset.Icc 4 N).filter (PolBad ε η)).card : ℝ) ≤ _
  let S_all := (Finset.Icc 4 N).filter (PolBad ε η)
  let S_low := S_all.filter (fun n => n < N₀)
  let S_hi := S_all.filter (fun n => N₀ ≤ n)
  have hS_split : S_all.card ≤ S_low.card + S_hi.card := by
    have : S_all ⊆ S_low ∪ S_hi := by
      intro n hn; simp only [Finset.mem_union, Finset.mem_filter, S_low, S_hi]
      by_cases h : n < N₀; exact Or.inl ⟨hn, h⟩; exact Or.inr ⟨hn, le_of_not_gt h⟩
    exact le_trans (Finset.card_le_card this) (Finset.card_union_le _ _)
  have hS_low : (S_low.card : ℝ) ≤ (N₀ : ℝ) := by
    have hsub : S_low ⊆ Finset.Icc 1 N₀ := by
      intro n hn; simp only [S_low, S_all, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      exact ⟨by omega, by omega⟩
    exact_mod_cast le_trans (Finset.card_le_card hsub) (by simp)
  have hS_hi : (S_hi.card : ℝ) ≤ (4 * (M : ℝ) * (2 : ℝ) ^ ε / ((2 : ℝ) ^ ε - 1)) * (N : ℝ) ^ ε := by
    let K := Nat.log 2 N
    have hsub_hi : S_hi ⊆ (Finset.range (K + 1)).biUnion
        (fun k => S_hi.filter (fun n => 2 ^ k ≤ n ∧ n ≤ 2 ^ (k + 1) - 1)) := by
      intro n hn
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      have hn_mem := Finset.mem_filter.mp hn
      have hn1 : 4 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn_mem.1).1).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn_mem.1).1).2
      refine ⟨Nat.log 2 n, Nat.lt_succ_of_le (Nat.log_mono_right hnN), hn, ?_, ?_⟩
      · exact Nat.pow_log_le_self 2 (by omega)
      · exact Nat.le_sub_one_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n)
    have hcard_hi : S_hi.card ≤ ∑ k ∈ Finset.range (K + 1),
        (S_hi.filter (fun n => 2 ^ k ≤ n ∧ n ≤ 2 ^ (k + 1) - 1)).card :=
      le_trans (Finset.card_le_card hsub_hi) Finset.card_biUnion_le
    have hblk_card : ∀ k ∈ Finset.range (K + 1),
        ((S_hi.filter (fun n => 2 ^ k ≤ n ∧ n ≤ 2 ^ (k + 1) - 1)).card : ℝ) ≤
          2 * (M : ℝ) * ((2 : ℝ) ^ ε) ^ k := by
      intro k _
      let B_k := S_hi.filter (fun n => 2 ^ k ≤ n ∧ n ≤ 2 ^ (k + 1) - 1)
      by_cases hne : 2 ^ (k + 1) - 1 < N₀
      · have hB_empty : B_k = ∅ := by
          ext n; simp only [B_k, S_hi, Finset.mem_filter, Finset.notMem_empty, iff_false]
          intro h; omega
        change (B_k.card : ℝ) ≤ 2 * (M : ℝ) * ((2 : ℝ) ^ ε) ^ k
        rw [hB_empty, Finset.card_empty, Nat.cast_zero]; positivity
      · push Not at hne
        let a_k := max N₀ (2 ^ k)
        let L_k := Nat.floor ((a_k : ℝ) ^ (1 - ε))
        let J_k := 2 ^ k / (L_k + 1) + 1
        have hB_sub : B_k ⊆ (Finset.range J_k).biUnion (fun j =>
            (Finset.Icc (a_k + j * (L_k + 1)) (a_k + j * (L_k + 1) + L_k)).filter (PolBad ε η)) := by
          intro n hn
          simp only [B_k, S_hi, S_all, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Icc] at hn ⊢
          have hna : a_k ≤ n := max_le hn.1.2 hn.2.1
          have hdiff : n - a_k < 2 ^ k := by
            have : 2 ^ k ≤ a_k := le_max_right _ _
            have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
            omega
          refine ⟨(n - a_k) / (L_k + 1), ?_, ⟨?_, ?_⟩, hn.1.1.2⟩
          · have h1 : (n - a_k) / (L_k + 1) ≤ (2 ^ k) / (L_k + 1) := Nat.div_le_div_right hdiff.le
            omega
          · have := Nat.div_mul_le_self (n - a_k) (L_k + 1)
            omega
          · have hlt_mod := Nat.mod_lt (n - a_k) (Nat.succ_pos L_k)
            have hdiv_mod := Nat.div_add_mod (n - a_k) (L_k + 1)
            rw [mul_comm] at hdiv_mod
            omega
        have hB_card_le : B_k.card ≤ J_k * M := by
          calc B_k.card ≤ ((Finset.range J_k).biUnion (fun j =>
                (Finset.Icc (a_k + j * (L_k + 1)) (a_k + j * (L_k + 1) + L_k)).filter (PolBad ε η))).card :=
                  Finset.card_le_card hB_sub
            _ ≤ ∑ j ∈ Finset.range J_k,
                  ((Finset.Icc (a_k + j * (L_k + 1)) (a_k + j * (L_k + 1) + L_k)).filter (PolBad ε η)).card :=
                  Finset.card_biUnion_le
            _ ≤ ∑ _j ∈ Finset.range J_k, M := by
                  apply Finset.sum_le_sum; intro j _
                  let N' := a_k + j * (L_k + 1)
                  have hN'_ge : N₀ ≤ N' := le_trans (le_max_left _ _) (Nat.le_add_right _ _)
                  have hLk_le : L_k ≤ Nat.floor ((N' : ℝ) ^ (1 - ε)) := by
                    apply Nat.floor_mono
                    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_add_right a_k _) (by linarith)
                  have hsub_j : (Finset.Icc N' (N' + L_k)).filter (PolBad ε η) ⊆
                      (Finset.Icc N' (N' + Nat.floor ((N' : ℝ) ^ (1 - ε)))).filter (PolBad ε η) := by
                    intro x hx; simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
                    exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩
                  exact le_trans (Finset.card_le_card hsub_j) (h_int_bd' N' hN'_ge)
            _ = J_k * M := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        have hJk_le : (J_k : ℝ) ≤ ((2 : ℝ) ^ ε) ^ k + 1 := by
          have hdiv_r : ((2 ^ k / (L_k + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ k / ((L_k : ℝ) + 1) := by
            rw [le_div_iff₀ (by positivity)]
            exact_mod_cast Nat.div_mul_le_self (2 ^ k) (L_k + 1)
          have hLk_gt : ((2 : ℝ) ^ k) ^ (1 - ε) < (L_k : ℝ) + 1 := by
            have h1 : (a_k : ℝ) ^ (1 - ε) < (L_k : ℝ) + 1 := Nat.lt_floor_add_one _
            have h2 : ((2 : ℝ) ^ k) ^ (1 - ε) ≤ (a_k : ℝ) ^ (1 - ε) :=
              Real.rpow_le_rpow (by positivity) (by exact_mod_cast le_max_right N₀ (2 ^ k)) (by linarith)
            linarith
          have hdiv_pow : (2 : ℝ) ^ k / ((L_k : ℝ) + 1) ≤ ((2 : ℝ) ^ ε) ^ k := by
            calc (2 : ℝ) ^ k / ((L_k : ℝ) + 1) ≤ (2 : ℝ) ^ k / ((2 : ℝ) ^ k) ^ (1 - ε) := by
                  gcongr; positivity
              _ = ((2 : ℝ) ^ ε) ^ k := by
                  rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num),
                    ← Real.rpow_sub (by norm_num), show (k : ℝ) - (k : ℝ) * (1 - ε) = ε * (k : ℝ) by ring,
                    Real.rpow_mul (by norm_num), Real.rpow_natCast]
          have hJk_eq : (J_k : ℝ) = ((2 ^ k / (L_k + 1) : ℕ) : ℝ) + 1 := by
            dsimp [J_k]; push_cast; ring
          linarith
        have h1_le : (1 : ℝ) ≤ ((2 : ℝ) ^ ε) ^ k := one_le_pow₀ h2e_gt.le
        have hB_r : (B_k.card : ℝ) ≤ (J_k : ℝ) * (M : ℝ) := by exact_mod_cast hB_card_le
        nlinarith [show (0 : ℝ) ≤ M by positivity]
    have hsum_geom : ∑ k ∈ Finset.range (K + 1), 2 * (M : ℝ) * ((2 : ℝ) ^ ε) ^ k =
        2 * (M : ℝ) * (((2 : ℝ) ^ ε) ^ (K + 1) - 1) / ((2 : ℝ) ^ ε - 1) := by
      have : ∑ k ∈ Finset.range (K + 1), 2 * (M : ℝ) * ((2 : ℝ) ^ ε) ^ k =
          (2 * (M : ℝ)) * ∑ k ∈ Finset.range (K + 1), ((2 : ℝ) ^ ε) ^ k := by
        rw [Finset.mul_sum]
      rw [this, geom_sum_eq h2e_gt.ne']; ring
    have hK_pow : ((2 : ℝ) ^ ε) ^ (K + 1) ≤ (2 : ℝ) ^ ε * (N : ℝ) ^ ε := by
      rw [pow_succ', ← Real.rpow_natCast ((2 : ℝ) ^ ε) K, ← Real.rpow_mul (by positivity),
        mul_comm ε (K : ℝ), Real.rpow_mul (by positivity), Real.rpow_natCast]
      gcongr
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have hcard_hi_r : (S_hi.card : ℝ) ≤ ∑ k ∈ Finset.range (K + 1),
        ((S_hi.filter (fun n => 2 ^ k ≤ n ∧ n ≤ 2 ^ (k + 1) - 1)).card : ℝ) := by
      exact_mod_cast hcard_hi
    calc (S_hi.card : ℝ)
        ≤ ∑ k ∈ Finset.range (K + 1), 2 * (M : ℝ) * ((2 : ℝ) ^ ε) ^ k := le_trans hcard_hi_r (Finset.sum_le_sum hblk_card)
      _ = 2 * (M : ℝ) * (((2 : ℝ) ^ ε) ^ (K + 1) - 1) / ((2 : ℝ) ^ ε - 1) := hsum_geom
      _ ≤ 2 * (M : ℝ) * ((2 : ℝ) ^ ε * (N : ℝ) ^ ε) / ((2 : ℝ) ^ ε - 1) := by
          gcongr; linarith
      _ ≤ (4 * (M : ℝ) * (2 : ℝ) ^ ε / ((2 : ℝ) ^ ε - 1)) * (N : ℝ) ^ ε := by
          rw [div_mul_eq_mul_div]
          have h_num : 2 * (M : ℝ) * ((2 : ℝ) ^ ε * (N : ℝ) ^ ε) ≤
              4 * (M : ℝ) * (2 : ℝ) ^ ε * (N : ℝ) ^ ε := by
            nlinarith [show 0 ≤ (M : ℝ) * ((2 : ℝ) ^ ε * (N : ℝ) ^ ε) by positivity]
          gcongr
  have hM_le : (M : ℝ) ≤ 2 / (η ^ 2 * ε) := by
    have h1 : (M : ℝ) ≤ (η ^ 2 * ε)⁻¹ + 1 := by
      have : (Nat.floor ((η ^ 2 * ε)⁻¹) : ℝ) ≤ (η ^ 2 * ε)⁻¹ := Nat.floor_le (by positivity)
      dsimp [M]; push_cast; linarith
    have h2 : (1 : ℝ) ≤ (η ^ 2 * ε)⁻¹ := by
      rw [le_inv_comm₀ (by positivity) (by norm_num)]; nlinarith
    linarith [show (η ^ 2 * ε)⁻¹ = 1 / (η ^ 2 * ε) by rw [one_div]]
  have h_coeff : 4 * (M : ℝ) * (2 : ℝ) ^ ε / ((2 : ℝ) ^ ε - 1) ≤
      (8 * (2 : ℝ) ^ ε / (ε * ((2 : ℝ) ^ ε - 1))) * η ^ (-2 : ℤ) := by
    have hη_eq : η ^ (-2 : ℤ) = (η ^ 2)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [hη_eq]
    calc 4 * (M : ℝ) * (2 : ℝ) ^ ε / ((2 : ℝ) ^ ε - 1)
        ≤ 4 * (2 / (η ^ 2 * ε)) * (2 : ℝ) ^ ε / ((2 : ℝ) ^ ε - 1) := by gcongr
      _ = (8 * (2 : ℝ) ^ ε / (ε * ((2 : ℝ) ^ ε - 1))) * (η ^ 2)⁻¹ := by
          field_simp [(by positivity : η ≠ 0), (by positivity : ε ≠ 0), (by linarith : (2 : ℝ) ^ ε - 1 ≠ 0)]
  have h1_le_N : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast hN) hε0.le
  have h1_le_eta : (1 : ℝ) ≤ η ^ (-2 : ℤ) := by
    rw [zpow_neg, zpow_natCast, le_inv_comm₀ (by positivity) (by norm_num)]; nlinarith
  have hS_all_r : (S_all.card : ℝ) ≤ (S_low.card : ℝ) + (S_hi.card : ℝ) := by exact_mod_cast hS_split
  calc (S_all.card : ℝ)
      ≤ (N₀ : ℝ) + (8 * (2 : ℝ) ^ ε / (ε * ((2 : ℝ) ^ ε - 1))) * η ^ (-2 : ℤ) * (N : ℝ) ^ ε := by
        have : (4 * (M : ℝ) * (2 : ℝ) ^ ε / ((2 : ℝ) ^ ε - 1)) * (N : ℝ) ^ ε ≤
            (8 * (2 : ℝ) ^ ε / (ε * ((2 : ℝ) ^ ε - 1))) * η ^ (-2 : ℤ) * (N : ℝ) ^ ε := by gcongr
        linarith
    _ ≤ C_pol * η ^ (-2 : ℤ) * (N : ℝ) ^ ε := by
        dsimp [C_pol]
        have : (N₀ : ℝ) ≤ (N₀ : ℝ) * η ^ (-2 : ℤ) * (N : ℝ) ^ ε := by
          nlinarith [show (1 : ℝ) ≤ η ^ (-2 : ℤ) * (N : ℝ) ^ ε by nlinarith]
        linarith

end GrasGreenbergBrocard
