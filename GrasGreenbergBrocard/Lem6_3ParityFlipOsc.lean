import GrasGreenbergBrocard.Prop6_1FourGCD
import GrasGreenbergBrocard.ValuationParityThmHelpers

open scoped BigOperators
open Real Finset Filter

namespace GrasGreenbergBrocard

set_option maxHeartbeats 2000000

lemma val_factorial_le_two_div {n p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
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
    (C_exp : ℝ) (hC_exp : 0 ≤ C_exp) (R_exp : ℕ)
    (hExp : ∀ (h : ℤ), h ≠ 0 → |h| ≤ 2 * (H : ℤ) + 1 →
      ‖∑ p ∈ I, (Real.log (p : ℝ) : ℂ) * eExp ((h : ℝ) * (n : ℝ) / (2 * (p : ℝ)))‖ ≤
        C_exp * P * (Real.log (n : ℝ)) ^ (-((R_exp : ℝ) + 2))) :
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
  -- Now swap the sum over p and h for the h ≠ 0 part
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


lemma lem_6_3_osc_bound
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (ε : ℝ) (hε : 0 < ε)
    (C₂ : ℝ) (hC₂ : 0 < C₂) (N_exp : ℕ)
    (hExp1 : ∀ (b : ℕ), N_exp ≤ b →
      ∀ (P : ℝ) (I : Finset ℕ) (hm1 : ℤ) (w : ℝ → ℝ) (W₀ : ℝ),
        (b : ℝ) ^ δ ≤ P →
        P ≤ (b : ℝ) / (Real.log (b : ℝ)) ^ 12 →
        (∀ p ∈ I, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
        hm1 ≠ 0 →
        |hm1| ≤ 2 * (Nat.floor ((Real.log (b : ℝ)) ^ (Nat.floor (1 / δ) + 2)) : ℤ) + 1 →
        (2 : ℝ) ^ (-(Nat.floor (1 / δ) : ℤ)) * (Real.log (b : ℝ)) ^ (6 * Nat.floor (1 / δ) + 30) ≤ (b : ℝ) / P →
        (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) →
        0 ≤ W₀ →
        ‖∑ p ∈ I, (w (p : ℝ) * Real.log (p : ℝ) : ℂ) * eExp ((hm1 : ℝ) * (b : ℝ) / (2 * (p : ℝ)))‖ ≤
          C₂ * W₀ * P * (Real.log (b : ℝ)) ^ (-((Nat.floor (1 / δ) : ℝ) + 2)))
    (hR_ge4 : 4 ≤ Nat.floor (1 / δ))
    (N₅ N_exp_d N_osc_fin : ℕ)
    (hN₅ : ∀ b : ℕ, N₅ ≤ b → dist (1 / Real.log (b : ℝ)) 0 < δ / 20)
    (hN_exp_d : ∀ b : ℕ, N_exp_d ≤ b → max (N_exp : ℝ) 100 ≤ (b : ℝ) ^ δ)
    (hN_osc_fin : ∀ b : ℕ, N_osc_fin ≤ b →
      dist ((1000 * (((Nat.floor (1 / δ) : ℝ) + 4) ^ 2 + 1) * (C₂ + 1) * ((δ / 2) ^ (-(Nat.floor (1 / δ) : ℤ) - 2) + 1)) *
        (Real.log (Real.log (b : ℝ)) + 1) ^ 2 / (Real.log (b : ℝ)) ^ 2) 0 < ε / 100)
    (n₁ n₂ : ℕ) (hn₁_ge_N5 : N₅ ≤ n₁) (hn₁_ge_Nexpd : N_exp_d ≤ n₁) (hn₁_ge_Nosc : N_osc_fin ≤ n₁)
    (hn₁_ge_Nexp : N_exp ≤ n₁) (hn₁_ge_1000 : 1000 ≤ n₁) (hlog_ge3 : 3 ≤ (Real.log (n₁ : ℝ)) ^ 2) (hlt : n₁ < n₂) (h_lt_n₁ : n₂ - n₁ < n₁)
    (hn₁_pos : (0 : ℝ) < n₁) (hlog_n₁_pos : 0 < Real.log (n₁ : ℝ))
    (hh_gt : (n₁ : ℝ) ^ δ < ((n₂ - n₁ : ℕ) : ℝ))
    (hy₁_gt : (n₁ : ℝ) ^ δ < ((n₂ - n₁ : ℕ) : ℝ) / (Real.log (n₁ : ℝ)) ^ (6 * Nat.floor (1 / δ) + 30 + 2))
    (hy₁_le_n₁ : ((n₂ - n₁ : ℕ) : ℝ) / (Real.log (n₁ : ℝ)) ^ (6 * Nat.floor (1 / δ) + 30 + 2) ≤ (n₁ : ℝ))
    (hn₁_delta_ge3 : 3 ≤ (n₁ : ℝ) ^ δ) :
    let h := n₂ - n₁
    let y₁ := (h : ℝ) / (Real.log (n₁ : ℝ)) ^ (6 * Nat.floor (1 / δ) + 30 + 2)
    let I_osc := ((Finset.Icc 3 n₁).filter Nat.Prime).filter (fun p : ℕ => (n₁ : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ≤ y₁)
    |∑ p ∈ I_osc,
      ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
        ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ))| ≤
      (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
  let R := Nat.floor (1 / δ)
  let A_R := 6 * R + 30
  let C_osc_const : ℝ := 1000 * (((R : ℝ) + 4) ^ 2 + 1) * (C₂ + 1) * ((δ / 2) ^ (-(R : ℤ) - 2) + 1)
  let h := n₂ - n₁
  let y₁ : ℝ := (h : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2)
  let I_osc := ((Finset.Icc 3 n₁).filter Nat.Prime).filter (fun p : ℕ => (n₁ : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ≤ y₁)
  -- Dyadic partition of I_osc on ((n₁ : ℝ)^δ, y₁]
  have hI_mem : ∀ p ∈ I_osc, (n₁ : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ≤ y₁ := by
    intro p hp; exact (Finset.mem_filter.mp hp).2
  obtain ⟨hpart_osc, hdisj_osc⟩ :=
    dyadic_partition_finset (by linarith : 1 ≤ (n₁ : ℝ) ^ δ) hy₁_gt.le I_osc hI_mem
  -- Choose H = Nat.floor (((δ / 2) * Real.log n₁) ^ (R + 2))
  let H := Nat.floor (((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2))
  have hH_ge1 : 1 ≤ H := by
    have h5 := hN₅ n₁ (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h5
    have h10 : 10 ≤ (δ / 2) * Real.log (n₁ : ℝ) := by
      have := (div_lt_iff₀ hlog_n₁_pos).mp h5; linarith
    exact Nat.le_floor (one_le_pow_of_one_le₀ (by linarith) _)
  obtain ⟨c_tilde, b_tilde, h_supp, h_ctilde_b, h_btilde0, h_btilde_b, h_vaaler_pw, h_L1⟩ :=
    vaaler_parity_approx H hH_ge1
  -- Bound on each dyadic block I_k
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
      -- Since n₁ < n₂ < 2 n₁ and P ≤ y₁ ≤ h / (log n₁)^{A_R + 2} ≤ n₁ / (log n₁)^{A_R + 2}
      -- Wait: n₂ / (log n₂)^{12} vs n₁ / (log n₁)^{12}: for n₁ ≥ 1000, log n₂ ≤ 2 log n₁, so
      -- n₁ / (log n₁)^{A_R + 2} ≤ n₁ / (2 log n₁)^{12} ≤ n₂ / (log n₂)^{12} since A_R + 2 ≥ 56!
      have hlog_n2_le : Real.log (n₂ : ℝ) ≤ 2 * Real.log (n₁ : ℝ) := by
        have hn2_lt : (n₂ : ℝ) < 2 * (n₁ : ℝ) := by exact_mod_cast (by omega : n₂ < 2 * n₁)
        have h1 := Real.log_le_log (by positivity) hn2_lt.le
        rw [Real.log_mul (by norm_num) hn₁_pos.ne'] at h1
        have : Real.log 2 ≤ Real.log (n₁ : ℝ) := Real.log_le_log (by norm_num) (by linarith)
        linarith
      have hpow_le : (Real.log (n₂ : ℝ)) ^ 12 ≤ (2 * Real.log (n₁ : ℝ)) ^ 12 :=
        pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n₂))) hlog_n2_le 12
      have hlog2 : 2 ≤ Real.log (n₁ : ℝ) := by
        have h5 := hN₅ n₁ (by omega)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h5
        have := (div_lt_iff₀ hlog_n₁_pos).mp h5
        nlinarith only [this, hδ1, hδ0, hlog_n₁_pos]
      have h2_12 : (2 : ℝ) ^ 12 ≤ (Real.log (n₁ : ℝ)) ^ 12 :=
        pow_le_pow_left₀ (by norm_num) hlog2 12
      have hpow_ar : (2 * Real.log (n₁ : ℝ)) ^ 12 ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 2) := by
        rw [mul_pow]
        calc (2 : ℝ) ^ 12 * (Real.log (n₁ : ℝ)) ^ 12
            ≤ (Real.log (n₁ : ℝ)) ^ 12 * (Real.log (n₁ : ℝ)) ^ 12 := by gcongr
          _ = (Real.log (n₁ : ℝ)) ^ 24 := by ring
          _ ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 2) := pow_le_pow_right₀ (by linarith) (by omega)
      have hy1_le : y₁ ≤ (n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2) := by
        dsimp [y₁]; exact div_le_div_of_nonneg_right (by exact_mod_cast le_of_lt h_lt_n₁) (by positivity)
      have hn1_le_n2 : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast le_of_lt hlt
      have hlog_n2_pow_pos : 0 < (Real.log (n₂ : ℝ)) ^ 12 :=
        pow_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < n₂))) 12
      exact le_trans hP_lt_y₁.le (le_trans hy1_le (div_le_div₀ (by positivity) hn1_le_n2 hlog_n2_pow_pos
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
      have hm_pos : (0 : ℝ) < m := by
        by_contra h0; push_neg at h0
        have hm0 : m = 0 := by exact_mod_cast (by linarith : (m : ℝ) ≤ 0)
        subst hm0; simp at hPm; linarith
      have hP_m_lb : (m : ℝ) ^ δ ≤ P :=
        le_trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hm_le) hδ0.le) hP_lb
      exact hExp1 m hm_N P I_k hm1 w W₀ hP_m_lb hPm hI_k hm1_nz hm1_bd hTm hw hW₀
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
            have h1 : (Real.log (h : ℝ)) ^ (-((R : ℝ) + 2)) ≤ (δ * Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hlogh_lb (by linarith)
            rw [Real.mul_rpow hδ0.le hlog_n₁_pos.le] at h1
            have hdz : δ ^ (-((R : ℝ) + 2)) = δ ^ (-(R : ℤ) - 2) := by
              rw [show (-((R : ℝ) + 2)) = ((-(R : ℤ) - 2 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
            linarith
          simp only [← Complex.ofReal_mul] at h_res
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
              unfold eExp; rw [← Complex.exp_add]; congr 1; rw [hn2_eq]; push_cast; ring
            have h_cis : eExp ((h₂ : ℝ) * (h : ℝ) / (2 * (p : ℝ))) =
                (Real.cos (2 * Real.pi * ((h₂ : ℝ) * (h : ℝ) / (2 * (p : ℝ)))) : ℂ) +
                Complex.I * (Real.sin (2 * Real.pi * ((h₂ : ℝ) * (h : ℝ) / (2 * (p : ℝ)))) : ℂ) := by
              unfold eExp
              rw [show (2 * Real.pi * Complex.I * (((h₂ : ℝ) * (h : ℝ) / (2 * (p : ℝ))) : ℝ) : ℂ) =
                  ((2 * Real.pi * ((h₂ : ℝ) * (h : ℝ) / (2 * (p : ℝ))) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                Complex.exp_mul_I]
              push_cast; ring
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
            simp only [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
        _ ≤ ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ 2 *
              (6 * C₂ * P * (δ ^ (-(R : ℤ) - 2) + 1) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) := by
            rw [← sq]
            have h_sum_c_nn : 0 ≤ ∑ h ∈ S_H, ‖c_tilde h‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h_sum_c_nn h_L1 2) (by positivity)
    let L₁ : ℝ := (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)
    have hL1_ge1 : 1 ≤ L₁ := by
      dsimp [L₁]
      have hpi4 : 1 ≤ 4 / Real.pi := by rw [one_le_div Real.pi_pos]; linarith [Real.pi_lt_four]
      have hlog1 : 0 ≤ Real.log (2 * (H : ℝ) + 1) := Real.log_nonneg (by linarith [show (0 : ℝ) ≤ H by positivity])
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
                rw [show (2 * Real.pi * Complex.I * (((h : ℝ) * ((n₁ : ℝ) / (p : ℝ)) / 2) : ℝ) : ℂ) =
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
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul]
        have h1' : ‖(((-1 : ℝ) ^ Int.floor ((n₁ : ℝ) / (p : ℝ)) : ℝ) : ℂ) - Psi_tilde ((n₁ : ℝ) / (p : ℝ))‖ ≤
            (B_tilde ((n₁ : ℝ) / (p : ℝ))).re := by
          dsimp only [Psi_tilde, B_tilde, S_H]; simpa [Complex.ofReal_zpow] using h1
        have h2' : ‖(((-1 : ℝ) ^ Int.floor ((n₂ : ℝ) / (p : ℝ)) : ℝ) : ℂ) - Psi_tilde ((n₂ : ℝ) / (p : ℝ))‖ ≤
            (B_tilde ((n₂ : ℝ) / (p : ℝ))).re := by
          dsimp only [Psi_tilde, B_tilde, S_H]; simpa [Complex.ofReal_zpow] using h2
        have hmul1 : ‖(((-1 : ℝ) ^ Int.floor ((n₁ : ℝ) / (p : ℝ)) : ℝ) : ℂ) - Psi_tilde ((n₁ : ℝ) / (p : ℝ))‖ *
            ‖(((-1 : ℝ) ^ Int.floor ((n₂ : ℝ) / (p : ℝ)) : ℝ) : ℂ)‖ ≤ (B_tilde ((n₁ : ℝ) / (p : ℝ))).re * 1 :=
          mul_le_mul h1' ha2_bd (norm_nonneg _) hB1_nn
        have hmul2 : ‖Psi_tilde ((n₁ : ℝ) / (p : ℝ))‖ *
            ‖(((-1 : ℝ) ^ Int.floor ((n₂ : ℝ) / (p : ℝ)) : ℝ) : ℂ) - Psi_tilde ((n₂ : ℝ) / (p : ℝ))‖ ≤
            L₁ * (B_tilde ((n₂ : ℝ) / (p : ℝ))).re :=
          mul_le_mul hb1_bd h2' (norm_nonneg _) (by positivity)
        nlinarith [hB1_nn, hL1_ge1]
      have hB_split : ∀ x : ℝ, (B_tilde x).re =
          (b_tilde 0 + ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
            b_tilde h * eExp ((h : ℝ) * x / 2)).re := by
        intro x
        dsimp [B_tilde]
        have h0mem : (0 : ℤ) ∈ Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1) := by
          simp; omega
        rw [← Finset.add_sum_erase _ _ h0mem]
        have he0 : b_tilde 0 * eExp ((0 : ℝ) * x / 2) = b_tilde 0 := by
          unfold eExp; simp
        have herase : (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).erase 0 =
            (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0) := by
          ext a; simp [Finset.mem_erase, Finset.mem_filter, and_comm]
        rw [Int.cast_zero, he0, herase]
        simp only [Complex.add_re, ne_eq]
      have hB1_sum : ∑ p ∈ I_k, Real.log (p : ℝ) * (B_tilde ((n₁ : ℝ) / (p : ℝ))).re ≤
          (4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) +
            12 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by
        simp_rw [hB_split]
        refine vaaler_btilde_dyadic_sum_bound H hH_ge1 b_tilde h_btilde0 h_btilde_b n₁ (by omega) P hP_pos I_k hI_k
          C₂ hC₂.le R (fun h' hh' hbd => ?_)
        have hbd' : |h'| ≤ 2 * (Nat.floor ((Real.log (n₁ : ℝ)) ^ (R + 2)) : ℤ) + 1 :=
          le_trans hbd (by linarith [hH_le_n1])
        simpa using hExp_at n₁ (by omega) (le_refl n₁) hP_le_n₁ hTm_n1 h' (fun _ => 1) 1 hh' hbd'
          (fun _ _ => by norm_num) (by norm_num)
      have hB2_sum : ∑ p ∈ I_k, Real.log (p : ℝ) * (B_tilde ((n₂ : ℝ) / (p : ℝ))).re ≤
          (4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) +
            24 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by
        simp_rw [hB_split]
        have hrpow_n2 : (Real.log (n₂ : ℝ)) ^ (-((R : ℝ) + 2)) ≤ (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) :=
          Real.rpow_le_rpow_of_nonpos hlog_n₁_pos
            (Real.log_le_log hn₁_pos (by exact_mod_cast le_of_lt hlt)) (by linarith)
        let C_n2 : ℝ := 2 * C₂ * ((Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) / (Real.log (n₂ : ℝ)) ^ (-((R : ℝ) + 2)))
        have h_n2_rpow_pos : 0 < (Real.log (n₂ : ℝ)) ^ (-((R : ℝ) + 2)) :=
          Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < n₂))) _
        have h_v : ∑ p ∈ I_k, Real.log (p : ℝ) *
              (b_tilde 0 + ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                b_tilde h * eExp ((h : ℝ) * ((n₂ : ℝ) / (p : ℝ)) / 2)).re ≤
            (4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) +
              12 * C_n2 * P * (Real.log (n₂ : ℝ)) ^ (-((R : ℝ) + 2)) := by
          refine vaaler_btilde_dyadic_sum_bound H hH_ge1 b_tilde h_btilde0 h_btilde_b n₂ (by omega) P hP_pos I_k hI_k
            C_n2 (by positivity) R (fun h' hh' hbd => ?_)
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
              unfold eExp; rw [← Complex.exp_add]; congr 1; rw [hn2_eq]; push_cast; ring
            have h_cis : eExp ((h' : ℝ) * (h : ℝ) / (2 * (p : ℝ))) =
                (Real.cos (2 * Real.pi * ((h' : ℝ) * (h : ℝ) / (2 * (p : ℝ)))) : ℂ) +
                Complex.I * (Real.sin (2 * Real.pi * ((h' : ℝ) * (h : ℝ) / (2 * (p : ℝ)))) : ℂ) := by
              unfold eExp
              rw [show (2 * Real.pi * Complex.I * ((h' : ℝ) * (h : ℝ) / (2 * (p : ℝ)) : ℝ) : ℂ) =
                  ((2 * Real.pi * ((h' : ℝ) * (h : ℝ) / (2 * (p : ℝ))) : ℝ) : ℂ) * Complex.I by push_cast; ring,
                Complex.exp_mul_I]
              push_cast; ring
            rw [h_e, h_cis]; dsimp [w_cos, w_sin]; push_cast; ring
          rw [h_sp]
          calc ‖_ + Complex.I * _‖ ≤ ‖_‖ + ‖Complex.I * _‖ := norm_add_le _ _
            _ = ‖_‖ + ‖_‖ := by rw [norm_mul, Complex.norm_I, one_mul]
            _ ≤ C₂ * 1 * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) +
                C₂ * 1 * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := add_le_add h_cs h_sn
            _ = C_n2 * P * (Real.log (n₂ : ℝ)) ^ (-((R : ℝ) + 2)) := by
                dsimp [C_n2]; field_simp [h_n2_rpow_pos.ne']; ring
        refine le_trans h_v (le_of_eq ?_)
        dsimp [C_n2]; field_simp [h_n2_rpow_pos.ne']; ring
      have h_err_sum1 : ‖errC‖ ≤ ∑ p ∈ I_k, 3 * Real.log (p : ℝ) *
            (L₁ * (B_tilde ((n₁ : ℝ) / (p : ℝ))).re + L₁ * (B_tilde ((n₂ : ℝ) / (p : ℝ))).re) := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have hp_mem := hI_k p hp
        have hw3 : |w_base (p : ℝ)| ≤ 3 := hw_base_bd (p : ℝ) ⟨hp_mem.2.1.le, hp_mem.2.2⟩
        have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_mem.1.pos)
        rw [abs_of_nonneg hlog_nn]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hw3 hlog_nn) (hpw_bd p hp) (norm_nonneg _) (by positivity)
      have h_err_sum2 : (∑ p ∈ I_k, 3 * Real.log (p : ℝ) *
            (L₁ * (B_tilde ((n₁ : ℝ) / (p : ℝ))).re + L₁ * (B_tilde ((n₂ : ℝ) / (p : ℝ))).re)) =
          3 * L₁ * ((∑ p ∈ I_k, Real.log (p : ℝ) * (B_tilde ((n₁ : ℝ) / (p : ℝ))).re) +
            (∑ p ∈ I_k, Real.log (p : ℝ) * (B_tilde ((n₂ : ℝ) / (p : ℝ))).re)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
      exact le_trans (le_trans h_err_sum1 (le_of_eq h_err_sum2))
        (mul_le_mul_of_nonneg_left (add_le_add hB1_sum hB2_sum) (by positivity))
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
      have hlog_nn : 0 ≤ Real.log (2 * (H : ℝ) + 1) := Real.log_nonneg (by linarith [show (0 : ℝ) ≤ H by positivity])
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
        rw [mul_pow]; norm_cast
      have hpow_pos : 0 < ((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2) := by positivity
      calc (4 * P * Real.log (2 * P)) / ((H : ℝ) + 1)
          ≤ (4 * P * (2 * Real.log (n₁ : ℝ))) / (((δ / 2) * Real.log (n₁ : ℝ)) ^ (R + 2)) := by gcongr
        _ = 8 * P * ((δ / 2) ^ (-(R : ℤ) - 2)) * ((Real.log (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ (R + 2)) := by
            rw [mul_pow, zpow_sub₀ (by positivity : (0 : ℝ) < δ / 2).ne', zpow_neg, zpow_natCast, zpow_two]; ring
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
      rw [zpow_sub₀ hδ0.ne', zpow_sub₀ (by positivity : (0 : ℝ) < δ / 2).ne', zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      have h1 : (δ / 2) ^ R ≤ δ ^ R := pow_le_pow_left₀ (by positivity) (by linarith) R
      have h2 : (δ / 2) ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      have h1_inv : (δ ^ R)⁻¹ ≤ ((δ / 2) ^ R)⁻¹ := inv_anti₀ (by positivity) h1
      exact div_le_div₀ (by positivity) h1_inv (by positivity) h2
    have h_n1P_main : ((n₁ : ℝ) / P) * ‖mainC‖ ≤
        (C_osc_const / 2) * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
      have h1 := mul_le_mul_of_nonneg_left h_mainC_bd (by positivity : 0 ≤ (n₁ : ℝ) / P)
      have hL1_sq : L₁ ^ 2 ≤ 4 * ((R : ℝ) + 4) ^ 2 * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 := by
        calc L₁ ^ 2 ≤ (2 * ((R : ℝ) + 4) * (Real.log (Real.log (n₁ : ℝ)) + 1)) ^ 2 :=
              pow_le_pow_left₀ (by positivity) hL1_ub 2
          _ = 4 * ((R : ℝ) + 4) ^ 2 * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 := by ring
      have hpow_le5 : (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) ≤ 1 / (Real.log (n₁ : ℝ)) ^ 5 :=
        le_trans hrpow_cmp hrpow_R1
      calc ((n₁ : ℝ) / P) * ‖mainC‖
          ≤ ((n₁ : ℝ) / P) * (L₁ ^ 2 * (6 * C₂ * P * (δ ^ (-(R : ℤ) - 2) + 1) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)))) := h1
        _ ≤ ((n₁ : ℝ) / P) * ((4 * ((R : ℝ) + 4) ^ 2 * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2) *
              (6 * C₂ * P * ((δ / 2) ^ (-(R : ℤ) - 2) + 1) / (Real.log (n₁ : ℝ)) ^ 5)) := by
              have hd1 : δ ^ (-(R : ℤ) - 2) + 1 ≤ (δ / 2) ^ (-(R : ℤ) - 2) + 1 := add_le_add hd_cmp (le_refl 1)
              have h6 : 6 * C₂ * P * (δ ^ (-(R : ℤ) - 2) + 1) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) ≤
                  6 * C₂ * P * ((δ / 2) ^ (-(R : ℤ) - 2) + 1) / (Real.log (n₁ : ℝ)) ^ 5 := by
                rw [div_eq_mul_one_div]
                exact mul_le_mul (mul_le_mul_of_nonneg_left hd1 (by positivity)) hpow_le5 (by positivity) (by positivity)
              exact mul_le_mul_of_nonneg_left (mul_le_mul hL1_sq h6 (by positivity) (by positivity)) (by positivity)
        _ = 24 * ((R : ℝ) + 4) ^ 2 * C₂ * ((δ / 2) ^ (-(R : ℤ) - 2) + 1) * (n₁ : ℝ) *
              (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
              field_simp [hP_pos.ne']; ring
        _ ≤ (C_osc_const / 2) * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
              have h24_le : 24 * ((R : ℝ) + 4) ^ 2 * C₂ ≤ 24 * (((R : ℝ) + 4) ^ 2 + 1) * (C₂ + 1) := by
                nlinarith only [show 0 ≤ ((R : ℝ) + 4) ^ 2 by positivity, show 0 ≤ C₂ by positivity]
              have h24_osc : 24 * ((R : ℝ) + 4) ^ 2 * C₂ * ((δ / 2) ^ (-(R : ℤ) - 2) + 1) ≤ C_osc_const / 2 := by
                calc 24 * ((R : ℝ) + 4) ^ 2 * C₂ * ((δ / 2) ^ (-(R : ℤ) - 2) + 1)
                    ≤ 24 * (((R : ℝ) + 4) ^ 2 + 1) * (C₂ + 1) * ((δ / 2) ^ (-(R : ℤ) - 2) + 1) := by gcongr
                  _ ≤ C_osc_const / 2 := by
                      dsimp [C_osc_const]
                      have h_pos : 0 ≤ (((R : ℝ) + 4) ^ 2 + 1) * (C₂ + 1) * ((δ / 2) ^ (-(R : ℤ) - 2) + 1) := by positivity
                      linarith only [h_pos]
              gcongr
    have h_n1P_err : ((n₁ : ℝ) / P) * ‖errC‖ ≤
        (C_osc_const / 2) * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
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
        have h12 : 12 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) ≤
            12 * C₂ * P / (Real.log (n₁ : ℝ)) ^ 5 := by
          calc 12 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))
              ≤ 12 * C₂ * P * (1 / (Real.log (n₁ : ℝ)) ^ 5) := by gcongr
            _ = 12 * C₂ * P / (Real.log (n₁ : ℝ)) ^ 5 := by ring
        have h24 : 24 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) ≤
            24 * C₂ * P / (Real.log (n₁ : ℝ)) ^ 5 := by
          calc 24 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))
              ≤ 24 * C₂ * P * (1 / (Real.log (n₁ : ℝ)) ^ 5) := by gcongr
            _ = 24 * C₂ * P / (Real.log (n₁ : ℝ)) ^ 5 := by ring
        have hsum_rhs : 2 * (8 * P * (δ / 2) ^ (-(R : ℤ) - 2) / (Real.log (n₁ : ℝ)) ^ 5) +
            (12 * C₂ * P / (Real.log (n₁ : ℝ)) ^ 5 + 24 * C₂ * P / (Real.log (n₁ : ℝ)) ^ 5) =
            (16 * (δ / 2) ^ (-(R : ℤ) - 2) + 36 * C₂) * P / (Real.log (n₁ : ℝ)) ^ 5 := by ring
        linarith only [h_inv_H5, h12, h24, hsum_rhs]
      have h_inner_nn : 0 ≤ ((4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) +
          12 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) +
         ((4 * P * Real.log (2 * P)) / ((H : ℝ) + 1) +
          24 * C₂ * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) := by
        have hlog2P_nn : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by linarith only [hn₁_delta_ge3, hP_lb])
        positivity
      have h_osc_coef : 6 * ((R : ℝ) + 4) * (16 * (δ / 2) ^ (-(R : ℤ) - 2) + 36 * C₂) ≤ C_osc_const / 2 := by
        have hR4 : (R : ℝ) + 4 ≤ ((R : ℝ) + 4) ^ 2 + 1 := by nlinarith
        have h16_36 : 16 * (δ / 2) ^ (-(R : ℤ) - 2) + 36 * C₂ ≤
            36 * (C₂ + 1) * ((δ / 2) ^ (-(R : ℤ) - 2) + 1) := by
          nlinarith only [show 0 ≤ C₂ by positivity, show 0 ≤ (δ / 2) ^ (-(R : ℤ) - 2) by positivity]
        have hR4' : 6 * ((R : ℝ) + 4) ≤ 6 * (((R : ℝ) + 4) ^ 2 + 1) := by linarith only [hR4]
        calc 6 * ((R : ℝ) + 4) * (16 * (δ / 2) ^ (-(R : ℤ) - 2) + 36 * C₂)
            ≤ (6 * (((R : ℝ) + 4) ^ 2 + 1)) * (36 * (C₂ + 1) * ((δ / 2) ^ (-(R : ℤ) - 2) + 1)) := by gcongr
          _ = 216 * (((R : ℝ) + 4) ^ 2 + 1) * (C₂ + 1) * ((δ / 2) ^ (-(R : ℤ) - 2) + 1) := by ring
          _ ≤ C_osc_const / 2 := by
              dsimp [C_osc_const]
              have h_pos : 0 ≤ (((R : ℝ) + 4) ^ 2 + 1) * (C₂ + 1) * ((δ / 2) ^ (-(R : ℤ) - 2) + 1) := by positivity
              linarith only [h_pos]
      calc ((n₁ : ℝ) / P) * ‖errC‖
          ≤ ((n₁ : ℝ) / P) * (3 * (2 * ((R : ℝ) + 4) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2) *
              ((16 * (δ / 2) ^ (-(R : ℤ) - 2) + 36 * C₂) * P / (Real.log (n₁ : ℝ)) ^ 5)) := by
              refine le_trans h1 ?_
              exact mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hL1_le_sq (by norm_num))
                h_inner h_inner_nn (by positivity)) (by positivity)
        _ = 6 * ((R : ℝ) + 4) * (16 * (δ / 2) ^ (-(R : ℤ) - 2) + 36 * C₂) * (n₁ : ℝ) *
              (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
              field_simp [hP_pos.ne']; ring
        _ ≤ (C_osc_const / 2) * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
              gcongr
    -- Now compare (C_osc_const / 5) * n₁ * (loglog n₁ + 1)^2 / (log n₁)^5 with ε / (16 * (log n₁ / log 2 + 2)) * n₁ * log n₁
    have h_osc_ball : C_osc_const * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 2 < ε / 100 := by
      have := hN_osc_fin n₁ (by omega)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this; exact this
    have hlog1 : 1 ≤ Real.log (n₁ : ℝ) := by nlinarith only [hlog_n₁_pos, hlog_ge3]
    have hlog_div2 : Real.log (n₁ : ℝ) / Real.log 2 + 2 ≤ 4 * Real.log (n₁ : ℝ) := by
      have hlog2_gt : 1 / 2 ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
      have h1 : Real.log (n₁ : ℝ) / Real.log 2 ≤ 2 * Real.log (n₁ : ℝ) := by
        rw [div_le_iff₀ (Real.log_pos (by norm_num))]; nlinarith only [hlog2_gt, hlog_n₁_pos]
      linarith only [h1, hlog1]
    have h_sum_2 : ((n₁ : ℝ) / P) * ‖mainC‖ + ((n₁ : ℝ) / P) * ‖errC‖ ≤
        C_osc_const * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by
      have h_add := add_le_add h_n1P_main h_n1P_err
      have h_eq : (C_osc_const / 2) * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 +
          (C_osc_const / 2) * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 =
          C_osc_const * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := by ring
      rwa [h_eq] at h_add
    have h_coef : (1 / (Real.log (n₁ : ℝ)) ^ 4) * (ε / 100) ≤
        ε / (16 * (Real.log (n₁ : ℝ) / Real.log 2 + 2)) := by
      have hlog2 : 2 ≤ Real.log (n₁ : ℝ) := by
        have h5 := hN₅ n₁ (by omega)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h5
        have h20 : 20 ≤ δ * Real.log (n₁ : ℝ) := by
          have := (div_lt_iff₀ hlog_n₁_pos).mp h5; linarith only [this]
        nlinarith only [h20, hδ1, hδ0, hlog_n₁_pos]
      rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      have h_mul : 16 * (Real.log (n₁ : ℝ) / Real.log 2 + 2) ≤ (Real.log (n₁ : ℝ)) ^ 4 * 100 := by
        have h_4log : 16 * (Real.log (n₁ : ℝ) / Real.log 2 + 2) ≤ 64 * Real.log (n₁ : ℝ) := by
          linarith only [hlog_div2]
        have h_pow : 64 * Real.log (n₁ : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ 4 * 100 := by
          have : 64 ≤ (Real.log (n₁ : ℝ)) ^ 3 * 100 := by
            have h3 : 8 ≤ (Real.log (n₁ : ℝ)) ^ 3 := by
              calc (8 : ℝ) = 2 ^ 3 := by norm_num
                _ ≤ (Real.log (n₁ : ℝ)) ^ 3 := pow_le_pow_left₀ (by norm_num) hlog2 3
            linarith only [h3]
          nlinarith only [this, hlog_n₁_pos]
        linarith only [h_4log, h_pow]
      exact mul_le_mul_of_nonneg_left h_mul hε.le
    calc |∑ p ∈ I_k, _| ≤ ((n₁ : ℝ) / P) * (‖mainC‖ + ‖errC‖) := h_comb
      _ = ((n₁ : ℝ) / P) * ‖mainC‖ + ((n₁ : ℝ) / P) * ‖errC‖ := mul_add _ _ _
      _ ≤ C_osc_const * (n₁ : ℝ) * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 5 := h_sum_2
      _ = (1 / (Real.log (n₁ : ℝ)) ^ 4) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) *
            (C_osc_const * (Real.log (Real.log (n₁ : ℝ)) + 1) ^ 2 / (Real.log (n₁ : ℝ)) ^ 2) := by
          field_simp [hlog_n₁_pos.ne']; try ring
      _ ≤ (1 / (Real.log (n₁ : ℝ)) ^ 4) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) * (ε / 100) := by
          gcongr
      _ = ((1 / (Real.log (n₁ : ℝ)) ^ 4) * (ε / 100)) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) := by ring
      _ ≤ (ε / (16 * (Real.log (n₁ : ℝ) / Real.log 2 + 2))) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) := by
          gcongr
      _ = (ε / (16 * (Real.log (n₁ : ℝ) / Real.log 2 + 2))) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
  change |∑ p ∈ I_osc, _| ≤ (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ)
  rw [hpart_osc, Finset.sum_biUnion hdisj_osc]
  have hcard_blk : ((dyadicBlocks ((n₁ : ℝ) ^ δ) y₁).card : ℝ) ≤ Real.log (n₁ : ℝ) / Real.log 2 + 2 := by
    have h1 := dyadicBlocks_card_le (by linarith : 1 ≤ (n₁ : ℝ) ^ δ) hy₁_gt.le
    have h2 : Real.log (y₁ / (n₁ : ℝ) ^ δ) ≤ Real.log (n₁ : ℝ) := by
      apply Real.log_le_log (div_pos (lt_trans (by positivity) hy₁_gt) (by positivity))
      exact le_trans (div_le_self (lt_trans (by positivity) hy₁_gt).le (by linarith : 1 ≤ (n₁ : ℝ) ^ δ)) hy₁_le_n₁
    exact le_trans h1 (by gcongr)
  calc |∑ k ∈ dyadicBlocks ((n₁ : ℝ) ^ δ) y₁, ∑ p ∈ _, _|
      ≤ ∑ k ∈ dyadicBlocks ((n₁ : ℝ) ^ δ) y₁, |∑ p ∈ _, _| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ dyadicBlocks ((n₁ : ℝ) ^ δ) y₁,
          (ε / (16 * (Real.log (n₁ : ℝ) / Real.log 2 + 2))) * (n₁ : ℝ) * Real.log (n₁ : ℝ) :=
        Finset.sum_le_sum hblock_bound
    _ = ((dyadicBlocks ((n₁ : ℝ) ^ δ) y₁).card : ℝ) *
          ((ε / (16 * (Real.log (n₁ : ℝ) / Real.log 2 + 2))) * (n₁ : ℝ) * Real.log (n₁ : ℝ)) := by
        rw [Finset.sum_const]; try rw [nsmul_eq_mul]
    _ ≤ (Real.log (n₁ : ℝ) / Real.log 2 + 2) *
          ((ε / (16 * (Real.log (n₁ : ℝ) / Real.log 2 + 2))) * (n₁ : ℝ) * Real.log (n₁ : ℝ)) := by gcongr
    _ = (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have hne : Real.log (n₁ : ℝ) / Real.log 2 + 2 ≠ 0 := by positivity
        field_simp [hne]; try ring
    _ ≤ (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by gcongr; linarith

end GrasGreenbergBrocard
