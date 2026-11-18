import GrasGreenbergBrocard.Lem6_3ParityFlip
import GrasGreenbergBrocard.ValuationParityMod

/-!
# Section 6.4: Universal Capacity Diamond, Polarization Concentration, and Proof of Theorem 1.3(i)

This file formalizes **Theorem 6.4 (eqs. 6.8–6.9)**, **Theorem 1.3(i) (eq. 1.9)**, and the
consecutive-squares `(k_{j^2}, k_{(j+1)^2}) ≠ (2, 2)` exclusion from **Proposition 6.2(iii)**:
1. Odd-core polarization weight `θ(n) ∈ [0, 1]` and upper-band polarization weight `θ_ε(n) ∈ [0, 1]`.
2. Universal Capacity Diamond (eq. 6.8): `(1 - α)/2 - o(1) ≤ θ(n₁) + θ(n₂) ≤ (3 + α)/2 + o(1)` and
   `|θ(n₁) - θ(n₂)| ≤ (1 + α)/2 + o(1)` for `n₂ - n₁ ≤ n₁^α`.
3. **Theorem 1.3(i)**: `n₂ - n₁ > n₁^{1 - ε}` for sufficiently large `k = 2` solutions, and
   `#{1 ≤ n ≤ N : ∃ m, n! + 1 = m^2 ∧ k = 2} ≤ C_ε N^ε`.
4. Polarization concentration via Rankin's spherical cap Cauchy–Schwarz inequality.
-/

open scoped BigOperators
open Real Finset Filter

set_option maxHeartbeats 2000000

namespace GrasGreenbergBrocard

/-- Odd-core polarization weight `θ(n) = log B^{(2)}(n) / S_odd(n)` (equals `0` when `k = 2`). -/
noncomputable def theta_weight (n m : ℕ) : ℝ :=
  if 0 < S_odd n then Real.log (B_part n ((m + 1) / 2) : ℝ) / S_odd n else 0

/-- Upper-band polarization weight `θ_ε(n)` on `p ∈ (n^{1 - ε/2}, n]`. -/
noncomputable def theta_eps_weight (ε : ℝ) (n m : ℕ) : ℝ :=
  let num := ∑ p ∈ (Podd n).filter (fun p : ℕ => 3 ≤ p ∧ (n : ℝ) ^ (1 - ε / 2) < (p : ℝ) ∧
    p ∣ B_part n ((m + 1) / 2)), (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
  let den := ∑ p ∈ (Podd n).filter (fun p : ℕ => 3 ≤ p ∧ (n : ℝ) ^ (1 - ε / 2) < (p : ℝ)),
    (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
  if 0 < den then num / den else 0

lemma theta_weight_nonneg (n m : ℕ) : 0 ≤ theta_weight n m := by
  unfold theta_weight
  split_ifs with h
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast B_part_pos n ((m + 1) / 2))) h.le
  · exact le_refl 0

lemma theta_weight_le_one {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    theta_weight n m ≤ 1 := by
  unfold theta_weight
  split_ifs with h
  · rw [div_le_one h]
    have hB_dvd : B_part n ((m + 1) / 2) ∣ B_star5 n := by
      have ⟨_, _, hBprod⟩ := oddPartNat_u_eq_B_mul_Z_sq hn hm
      rw [← hBprod]; exact dvd_mul_left _ _
    have hle : (B_part n ((m + 1) / 2) : ℝ) ≤ (B_star5 n : ℝ) :=
      by exact_mod_cast Nat.le_of_dvd (B_star5_pos n) hB_dvd
    have hlog_le : Real.log (B_part n ((m + 1) / 2) : ℝ) ≤ Real.log (B_star5 n : ℝ) :=
      Real.log_le_log (by exact_mod_cast B_part_pos n ((m + 1) / 2)) hle
    -- And 2 * log(B_star5 n) ≤ S_odd n? Wait: B_star5 = ∏_{p ∈ Podd n, p ≥ 3} p^{v_p(n!)},
    -- NO! B_star5 = ∏_{p ∈ Podd n, p ≥ 3} p^{(v_p(n!) - 1)/2} ? No, let's check B_star5 in Thm5_2EffectiveCores!
    -- Wait: A_star5 * B_star5 = oddPartNat(n!) / ..., so log(B_star5) = S_odd n?
    -- Actually, let's check: B_part n u ≤ ∏_{p ∈ Podd n, p ≥ 3} p^{v_p(n!)} so log(B_part n u) ≤ S_odd n!
    have hB_dvd_prod : B_part n ((m + 1) / 2) ∣
        ∏ p ∈ (Podd n).filter (fun p => 3 ≤ p), p ^ padicValNat p (Nat.factorial n) := by
      unfold B_part
      have hsub : ((Podd n).filter (fun p => 3 ≤ p ∧ p ∣ (m + 1) / 2)) ⊆
          (Podd n).filter (fun p => 3 ≤ p) :=
        fun p hp => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩
      exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
    have hpos_prod : 0 < ∏ p ∈ (Podd n).filter (fun p => 3 ≤ p), p ^ padicValNat p (Nat.factorial n) := by
      apply Finset.prod_pos; intro p hp
      simp only [Podd, Finset.mem_filter, Finset.mem_Icc] at hp
      exact pow_pos (by omega : 0 < p) _
    have hle_prod := Real.log_le_log (by exact_mod_cast B_part_pos n ((m + 1) / 2))
      (by exact_mod_cast Nat.le_of_dvd hpos_prod hB_dvd_prod)
    rw [Nat.cast_prod, Real.log_prod _ _ (fun p hp => by
      simp only [Podd, Finset.mem_filter, Finset.mem_Icc] at hp
      exact pow_ne_zero _ (by exact_mod_cast (by omega : p ≠ 0)))] at hle_prod
    refine le_trans hle_prod (le_of_eq ?_)
    unfold S_odd
    apply Finset.sum_congr rfl; intro p _; rw [Nat.cast_pow, Real.log_pow]
  · norm_num

lemma theta_weight_eq_zero_of_k2 {n m X₁ Y₁ : ℕ} (hn : 4 ≤ n) (hn6 : n ≠ 6)
    (hm : Nat.factorial n + 1 = m ^ 2) (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk2 : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2) :
    theta_weight n m = 0 := by
  have hB_val : B_sol m = X₁ ^ 2 := by
    have h1 : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) =
        ((X₁ : ℝ) ^ 2 + (q_n n : ℝ) * (Y₁ : ℝ) ^ 2) +
        (2 * (X₁ : ℝ) * (Y₁ : ℝ)) * Real.sqrt (q_n n : ℝ) := by
      rw [hk2]; unfold pellUnit; push_cast; ring_nf; rw [Real.sq_sqrt (by positivity)]
    have hq_nsq : ¬ IsSquare (q_n n) := by
      intro ⟨r, hr⟩
      have hq2 : 2 ≤ q_n n := q_n_ge_two (by omega)
      have hr2 : 2 ≤ r := by nlinarith
      obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd (by omega : r ≠ 1)
      exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp
        (by rw [hr]; exact mul_dvd_mul hpr hpr)
    have hirr : Irrational (Real.sqrt (q_n n : ℝ)) := irrational_sqrt_natCast_iff.mpr hq_nsq
    have hm_nat : m = X₁ ^ 2 + q_n n * Y₁ ^ 2 := by
      have hdiff : ((m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2) : ℤ) =
          ((2 * (X₁ : ℤ) * (Y₁ : ℤ) - (s_n n : ℤ)) : ℤ) * Real.sqrt (q_n n : ℝ) := by
        push_cast; linarith
      by_contra hne
      have hne_z : ((m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2)) ≠ 0 := by
        intro h0; apply hne; exact_mod_cast sub_eq_zero.mp h0
      have hco_nz : (2 * (X₁ : ℝ) * (Y₁ : ℝ) - (s_n n : ℝ)) ≠ 0 := by
        intro h0
        have hdiff' : ((m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2) : ℤ) =
            (2 * (X₁ : ℝ) * (Y₁ : ℝ) - (s_n n : ℝ)) * Real.sqrt (q_n n : ℝ) := by
          push_cast at hdiff ⊢; exact hdiff
        rw [h0, zero_mul] at hdiff'
        exact hne_z (by exact_mod_cast hdiff')
      let a_z : ℤ := (m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2)
      let b_z : ℤ := 2 * (X₁ : ℤ) * (Y₁ : ℤ) - (s_n n : ℤ)
      have hrat : Real.sqrt (q_n n : ℝ) = (a_z : ℝ) / (b_z : ℝ) := by
        have hco_z : (b_z : ℝ) ≠ 0 := by push_cast [b_z]; exact hco_nz
        rw [eq_div_iff hco_z]
        push_cast [a_z, b_z] at hdiff ⊢; linarith [hdiff]
      exact hirr ⟨(a_z : ℚ) / (b_z : ℚ), by push_cast; exact hrat.symm⟩
    have hpell := hfund.2.2.1
    have hm_add : m + 1 = 2 * X₁ ^ 2 := by
      zify [show 1 ≤ X₁ ^ 2 by nlinarith [hfund.1]] at hpell ⊢; linarith
    change (m + 1) / 2 = X₁ ^ 2; omega
  have hB_eq1 : B_part n ((m + 1) / 2) = 1 := by
    unfold B_part
    apply Finset.prod_eq_one; intro p hp
    simp only [Finset.mem_filter] at hp
    have hp_pr := hp.1.1.1
    have hp_odd : ¬ 2 ∣ padicValNat p (Nat.factorial n) := hp.1.1.2
    have hp_dvd_B : p ∣ B_sol m := by
      have : p ∣ (m + 1) / 2 := hp.2
      exact this
    have hp_dvd_X1 : p ∣ X₁ := by
      rw [hB_val] at hp_dvd_B
      exact hp_pr.dvd_of_dvd_pow hp_dvd_B
    have hp_ndvd_q : ¬ p ∣ q_n n := by
      intro hq
      have hpell := hfund.2.2.1
      have h1 : p ∣ X₁ ^ 2 := dvd_pow hp_dvd_X1 (by norm_num)
      have h2 : p ∣ q_n n * Y₁ ^ 2 := dvd_mul_of_dvd_left hq _
      have h3 : p ∣ 1 := by
        have : X₁ ^ 2 = q_n n * Y₁ ^ 2 + 1 := hpell
        exact (Nat.dvd_add_right h2).mp (this ▸ h1)
      exact hp_pr.not_dvd_one h3
    exact False.elim (hp_ndvd_q ((p_dvd_q_n_iff n p hp_pr).mpr hp_odd))
  unfold theta_weight
  rw [hB_eq1]; simp

/-- **Eq. (6.9)**: `log(Z * W)` and `log(X * Y)` are each `(1/2) log(n₁!) + O(log P + 1)`. -/
lemma log_ZW_and_XY_bounds {n₁ n₂ m₁ m₂ : ℕ} (hn₁ : 4 ≤ n₁) (hlt : n₁ < n₂)
    (hm₁ : Nat.factorial n₁ + 1 = m₁ ^ 2) (hm₂ : Nat.factorial n₂ + 1 = m₂ ^ 2) :
    let P := P_ratio n₁ n₂
    let X := X_gcd m₁ m₂; let Y := Y_gcd m₁ m₂
    let Z := Z_gcd m₁ m₂; let W := W_gcd m₁ m₂
    |Real.log ((Z : ℝ) * W) - (1 / 2 : ℝ) * Real.log (Nat.factorial n₁ : ℝ)| ≤
      6 * Real.log (P : ℝ) + 4 ∧
    |Real.log ((X : ℝ) * Y) - (1 / 2 : ℝ) * Real.log (Nat.factorial n₁ : ℝ)| ≤
      6 * Real.log (P : ℝ) + 4 := by
  obtain ⟨⟨a, b, c, d⟩, ⟨ha, hb, hc, hd, hab, hcd, _, _, _, _, _, h4sq⟩, _⟩ :=
    prop_6_1_part1_sl2_and_four_squares hn₁ hlt hm₁ hm₂
  rcases h4sq with ⟨hXsq, hYsq, hZsq, hWsq⟩
  have ⟨hX_pos, hY_pos, hZ_pos, hW_pos, _⟩ :=
    prop_6_1_coprime_and_factorization hn₁ hlt hm₁ hm₂
  set P := P_ratio n₁ n₂
  set X := X_gcd m₁ m₂; set Y := Y_gcd m₁ m₂
  set Z := Z_gcd m₁ m₂; set W := W_gcd m₁ m₂
  have hP_ge : 2 ≤ P := P_ratio_ge_two hn₁ hlt
  have ha_le : a ≤ P := by nlinarith
  have hb_le : b ≤ P := by nlinarith
  have hc_le : c ≤ P := by nlinarith
  have hd_le : d ≤ P := by nlinarith
  have hfac_pos : (0 : ℝ) < Nat.factorial n₁ := by exact_mod_cast Nat.factorial_pos n₁
  have hm1_gt : Real.sqrt (Nat.factorial n₁ : ℝ) < m₁ := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg m₁)]
    exact Real.sqrt_lt_sqrt (by positivity) (by
      have : (Nat.factorial n₁ : ℝ) + 1 = (m₁ : ℝ) ^ 2 := by exact_mod_cast hm₁
      linarith)
  have hm1_le : (m₁ : ℝ) ≤ 2 * Real.sqrt (Nat.factorial n₁ : ℝ) := by
    have hfac1 : 1 ≤ Nat.factorial n₁ := Nat.factorial_pos n₁
    have hsq : (m₁ : ℝ) ^ 2 ≤ (2 * Real.sqrt (Nat.factorial n₁ : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have : (m₁ : ℝ) ^ 2 = (Nat.factorial n₁ : ℝ) + 1 := by exact_mod_cast hm₁
      have : (1 : ℝ) ≤ Nat.factorial n₁ := by exact_mod_cast hfac1
      linarith
    nlinarith [Real.sqrt_nonneg (Nat.factorial n₁ : ℝ)]
  have hm2_le : (m₂ : ℝ) ≤ Real.sqrt (P : ℝ) * (m₁ : ℝ) := by
    have hsq : (m₂ : ℝ) ^ 2 ≤ (Real.sqrt (P : ℝ) * (m₁ : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have h1 : (m₂ : ℝ) ^ 2 = (P : ℝ) * (m₁ : ℝ) ^ 2 - ((P : ℝ) - 1) := by
        have hfac : (P : ℝ) * (Nat.factorial n₁ : ℝ) = Nat.factorial n₂ := by
          exact_mod_cast P_ratio_mul_factorial hlt
        have hm1r : (Nat.factorial n₁ : ℝ) + 1 = (m₁ : ℝ) ^ 2 := by exact_mod_cast hm₁
        have hm2r : (Nat.factorial n₂ : ℝ) + 1 = (m₂ : ℝ) ^ 2 := by exact_mod_cast hm₂
        linarith
      have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
      linarith
    nlinarith [Real.sqrt_nonneg (P : ℝ)]
  have hsqrtP_le : Real.sqrt (P : ℝ) ≤ (3 / 4 : ℝ) * (P : ℝ) := by
    have hsq : Real.sqrt (P : ℝ) ^ 2 ≤ ((3 / 4 : ℝ) * (P : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
      have hP2 : (2 : ℝ) ≤ P := by exact_mod_cast hP_ge
      nlinarith
    nlinarith [Real.sqrt_nonneg (P : ℝ)]
  have hfac24 : 24 ≤ Nat.factorial n₁ := by
    calc 24 = Nat.factorial 4 := by norm_num [Nat.factorial]
      _ ≤ Nat.factorial n₁ := Nat.factorial_le hn₁
  have hsqrt_ge4 : 4 ≤ Real.sqrt (Nat.factorial n₁ : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 16 ≤ Nat.factorial n₁))
  -- Bounds for P m₁ - m₂ - (P - 1) and P m₁ + m₂ + (P - 1):
  have h_lo : (1 / 8 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) ≤
      (P : ℝ) * m₁ - m₂ - ((P : ℝ) - 1) := by
    have h1 : (P : ℝ) * m₁ - m₂ ≥ (1 / 4 : ℝ) * (P : ℝ) * (m₁ : ℝ) := by
      have : m₂ ≤ (3 / 4 : ℝ) * (P : ℝ) * (m₁ : ℝ) := by nlinarith
      linarith
    have h2 : (P : ℝ) - 1 ≤ (1 / 4 : ℝ) * (P : ℝ) * (Real.sqrt (Nat.factorial n₁ : ℝ) / 1) := by
      nlinarith [show (0 : ℝ) ≤ P by positivity]
    nlinarith
  have hsqrtP_le' : Real.sqrt (P : ℝ) ≤ (18 / 25 : ℝ) * (P : ℝ) := by
    have hsq : Real.sqrt (P : ℝ) ^ 2 ≤ ((18 / 25 : ℝ) * (P : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
      have hP2 : (2 : ℝ) ≤ P := by exact_mod_cast hP_ge
      nlinarith
    nlinarith [Real.sqrt_nonneg (P : ℝ)]
  have h_lo' : (1 / 20 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) ≤
      (P : ℝ) * m₁ - m₂ - ((P : ℝ) - 1) := by
    have h1 : (P : ℝ) * m₁ - m₂ ≥ (7 / 25 : ℝ) * (P : ℝ) * (m₁ : ℝ) := by
      have : (m₂ : ℝ) ≤ (18 / 25 : ℝ) * (P : ℝ) * (m₁ : ℝ) := by nlinarith
      linarith
    have h2 : (P : ℝ) - 1 ≤ (23 / 100 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
      have hsq : (1 : ℝ) ^ 2 ≤ ((23 / 100 : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have : (24 : ℝ) ≤ Nat.factorial n₁ := by exact_mod_cast hfac24
        linarith
      have h1le : 1 ≤ (23 / 100 : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by nlinarith
      nlinarith [show (0 : ℝ) ≤ P by positivity]
    nlinarith
  have h_hi' : (P : ℝ) * m₁ + m₂ + ((P : ℝ) - 1) ≤
      5 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
    have h1 : (m₂ : ℝ) ≤ 2 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by nlinarith
    have h2 : (P : ℝ) - 1 ≤ (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by nlinarith
    nlinarith
  have hbound_pair : ∀ (U V k : ℕ), 1 ≤ k → k ≤ 4 * P ^ 4 → 0 < U → 0 < V →
      ((1 / 20 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ)) ^ 2 ≤ (k : ℝ) * ((U : ℝ) * V) ^ 2 →
      (k : ℝ) * ((U : ℝ) * V) ^ 2 ≤ (5 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ)) ^ 2 →
      |Real.log ((U : ℝ) * V) - (1 / 2 : ℝ) * Real.log (Nat.factorial n₁ : ℝ)| ≤
        6 * Real.log (P : ℝ) + 4 := by
    intro U V k hk1 hk_ub hU_pos hV_pos hlb hub
    have hsqrt_pos : 0 < Real.sqrt (Nat.factorial n₁ : ℝ) := Real.sqrt_pos.mpr hfac_pos
    have hP_pos : (0 : ℝ) < P := by positivity
    have hUV_pos : (0 : ℝ) < (U : ℝ) * V := by positivity
    have hUV_ub : (U : ℝ) * V ≤ 5 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
      have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hsq : ((U : ℝ) * V) ^ 2 ≤ (5 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ)) ^ 2 :=
        le_trans (le_mul_of_one_le_left (by positivity) hk1r) hub
      nlinarith
    have hUV_lb : Real.sqrt (Nat.factorial n₁ : ℝ) / (40 * (P : ℝ)) ≤ (U : ℝ) * V := by
      have hk_r : (k : ℝ) ≤ 4 * (P : ℝ) ^ 4 := by exact_mod_cast hk_ub
      have hsq : (Real.sqrt (Nat.factorial n₁ : ℝ) / (40 * (P : ℝ))) ^ 2 ≤ ((U : ℝ) * V) ^ 2 := by
        calc (Real.sqrt (Nat.factorial n₁ : ℝ) / (40 * (P : ℝ))) ^ 2
            = ((1 / 20 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ)) ^ 2 / (4 * (P : ℝ) ^ 4) := by
              field_simp; ring
          _ ≤ ((1 / 20 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ)) ^ 2 / (k : ℝ) := by
              gcongr
          _ ≤ ((U : ℝ) * V) ^ 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
      nlinarith
    have hlog_sqrt : Real.log (Real.sqrt (Nat.factorial n₁ : ℝ)) =
        (1 / 2 : ℝ) * Real.log (Nat.factorial n₁ : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.log_rpow hfac_pos]; ring
    have h1 := Real.log_le_log hUV_pos hUV_ub
    rw [Real.log_mul (by positivity) hsqrt_pos.ne', Real.log_mul (by norm_num) hP_pos.ne', hlog_sqrt] at h1
    have h2 := Real.log_le_log (by positivity) hUV_lb
    rw [Real.log_div hsqrt_pos.ne' (by positivity), Real.log_mul (by norm_num) hP_pos.ne', hlog_sqrt] at h2
    have hlog5 : Real.log 5 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5); linarith
    have hlog40 : Real.log 40 ≤ 4 := by
      have : Real.log 40 ≤ Real.log (Real.exp 4) := by
        apply Real.log_le_log (by norm_num)
        have := Real.exp_one_gt_d9
        calc (40 : ℝ) ≤ 2.71 ^ 4 := by norm_num
          _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
          _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
      rwa [Real.log_exp] at this
    have hlogP_nn : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ P))
    rw [abs_le]; constructor <;> linarith
  constructor
  · refine hbound_pair Z W (4 * b ^ 2 * c * d) (by positivity) (by nlinarith) hZ_pos hW_pos ?_ ?_
    · have hZW_eq : ((4 * b ^ 2 * c * d : ℕ) : ℝ) * ((Z : ℝ) * W) ^ 2 =
          ((P : ℝ) * m₁ + m₂ - ((P : ℝ) - 1)) * ((P : ℝ) * m₁ + m₂ + ((P : ℝ) - 1)) := by
        have hZ' : 2 * (b : ℝ) * d * (Z : ℝ) ^ 2 = (P : ℝ) * m₁ + m₂ - ((P : ℝ) - 1) := by exact_mod_cast hZsq
        have hW' : 2 * (b : ℝ) * c * (W : ℝ) ^ 2 = (P : ℝ) * m₁ + m₂ + ((P : ℝ) - 1) := by exact_mod_cast hWsq
        calc ((4 * b ^ 2 * c * d : ℕ) : ℝ) * ((Z : ℝ) * W) ^ 2
            = (2 * (b : ℝ) * d * (Z : ℝ) ^ 2) * (2 * (b : ℝ) * c * (W : ℝ) ^ 2) := by push_cast; ring
          _ = _ := by rw [hZ', hW']
      rw [hZW_eq]
      have h1 : (1 / 20 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) ≤
          (P : ℝ) * m₁ + m₂ - ((P : ℝ) - 1) := by linarith
      have h2 : (1 / 20 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) ≤
          (P : ℝ) * m₁ + m₂ + ((P : ℝ) - 1) := by linarith
      rw [sq]; exact mul_le_mul h1 h2 (by positivity) (by positivity)
    · have hZW_eq : ((4 * b ^ 2 * c * d : ℕ) : ℝ) * ((Z : ℝ) * W) ^ 2 =
          ((P : ℝ) * m₁ + m₂ - ((P : ℝ) - 1)) * ((P : ℝ) * m₁ + m₂ + ((P : ℝ) - 1)) := by
        have hZ' : 2 * (b : ℝ) * d * (Z : ℝ) ^ 2 = (P : ℝ) * m₁ + m₂ - ((P : ℝ) - 1) := by exact_mod_cast hZsq
        have hW' : 2 * (b : ℝ) * c * (W : ℝ) ^ 2 = (P : ℝ) * m₁ + m₂ + ((P : ℝ) - 1) := by exact_mod_cast hWsq
        calc ((4 * b ^ 2 * c * d : ℕ) : ℝ) * ((Z : ℝ) * W) ^ 2
            = (2 * (b : ℝ) * d * (Z : ℝ) ^ 2) * (2 * (b : ℝ) * c * (W : ℝ) ^ 2) := by push_cast; ring
          _ = _ := by rw [hZ', hW']
      rw [hZW_eq]
      have h1 : (P : ℝ) * m₁ + m₂ - ((P : ℝ) - 1) ≤ 5 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
        have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
        linarith
      rw [sq]; exact mul_le_mul h1 h_hi' (by linarith [h_lo']) (by positivity)
  · refine hbound_pair X Y (4 * a ^ 2 * c * d) (by positivity) (by nlinarith) hX_pos hY_pos ?_ ?_
    · have hXY_eq : ((4 * a ^ 2 * c * d : ℕ) : ℝ) * ((X : ℝ) * Y) ^ 2 =
          ((P : ℝ) * m₁ - m₂ - ((P : ℝ) - 1)) * ((P : ℝ) * m₁ - m₂ + ((P : ℝ) - 1)) := by
        have hX' : 2 * (a : ℝ) * c * (X : ℝ) ^ 2 = (P : ℝ) * m₁ - m₂ - ((P : ℝ) - 1) := by exact_mod_cast hXsq
        have hY' : 2 * (a : ℝ) * d * (Y : ℝ) ^ 2 = (P : ℝ) * m₁ - m₂ + ((P : ℝ) - 1) := by exact_mod_cast hYsq
        calc ((4 * a ^ 2 * c * d : ℕ) : ℝ) * ((X : ℝ) * Y) ^ 2
            = (2 * (a : ℝ) * c * (X : ℝ) ^ 2) * (2 * (a : ℝ) * d * (Y : ℝ) ^ 2) := by push_cast; ring
          _ = _ := by rw [hX', hY']
      rw [hXY_eq]
      have h2 : (1 / 20 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) ≤
          (P : ℝ) * m₁ - m₂ + ((P : ℝ) - 1) := by
        have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
        linarith
      rw [sq]; exact mul_le_mul h_lo' h2 (by positivity) (by positivity)
    · have hXY_eq : ((4 * a ^ 2 * c * d : ℕ) : ℝ) * ((X : ℝ) * Y) ^ 2 =
          ((P : ℝ) * m₁ - m₂ - ((P : ℝ) - 1)) * ((P : ℝ) * m₁ - m₂ + ((P : ℝ) - 1)) := by
        have hX' : 2 * (a : ℝ) * c * (X : ℝ) ^ 2 = (P : ℝ) * m₁ - m₂ - ((P : ℝ) - 1) := by exact_mod_cast hXsq
        have hY' : 2 * (a : ℝ) * d * (Y : ℝ) ^ 2 = (P : ℝ) * m₁ - m₂ + ((P : ℝ) - 1) := by exact_mod_cast hYsq
        calc ((4 * a ^ 2 * c * d : ℕ) : ℝ) * ((X : ℝ) * Y) ^ 2
            = (2 * (a : ℝ) * c * (X : ℝ) ^ 2) * (2 * (a : ℝ) * d * (Y : ℝ) ^ 2) := by push_cast; ring
          _ = _ := by rw [hX', hY']
      rw [hXY_eq]
      have h1 : (P : ℝ) * m₁ - m₂ - ((P : ℝ) - 1) ≤ 5 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
        have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
        linarith
      have h2 : (P : ℝ) * m₁ - m₂ + ((P : ℝ) - 1) ≤ 5 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
        linarith
      rw [sq]; exact mul_le_mul h1 h2 (by linarith [h_lo']) (by positivity)

/-- **Theorem 6.4(a) (Universal Capacity Diamond, eq. 6.8)**:
For any `α ∈ [0, 1)` and `ε > 0`, there exists `N₀` such that for any two Brocard solutions
`N₀ ≤ n₁ < n₂` with `n₂ - n₁ ≤ n₁ ^ α`:
1. `(1 - α) / 2 - ε ≤ θ(n₁) + θ(n₂) ≤ (3 + α) / 2 + ε`
2. `|θ(n₁) - θ(n₂)| ≤ (1 + α) / 2 + ε`. -/
theorem thm_6_4_capacity_diamond (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 25 ≤ N₀ ∧ ∀ n₁ n₂ m₁ m₂ : ℕ, N₀ ≤ n₁ → n₁ < n₂ →
      (n₂ - n₁ : ℝ) ≤ (n₁ : ℝ) ^ α →
      Nat.factorial n₁ + 1 = m₁ ^ 2 → Nat.factorial n₂ + 1 = m₂ ^ 2 →
      (1 - α) / 2 - ε ≤ theta_weight n₁ m₁ + theta_weight n₂ m₂ ∧
      theta_weight n₁ m₁ + theta_weight n₂ m₂ ≤ (3 + α) / 2 + ε ∧
      |theta_weight n₁ m₁ - theta_weight n₂ m₂| ≤ (1 + α) / 2 + ε := by
  let δ := min (ε / 16) (1 / 8)
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 4 := by linarith [min_le_right (ε / 16) (1 / 8 : ℝ)]
  obtain ⟨N_flip, hN_flip_ge, h_flip⟩ := lem_6_3_parity_flip_uniform δ hδ0 hδ1 (ε / 16) (by positivity)
  obtain ⟨C_cs, hC_cs, N_cs, hN_cs_ge, h_cs⟩ := thm_5_2_part1_cross_symmetry
  obtain ⟨N_sodd, hN_sodd⟩ := Filter.eventually_atTop.mp
    (Asymptotics.IsLittleO.bound S_odd_asymptotic (show (0 : ℝ) < min (ε / 128) (1 / 8) by positivity))
  obtain ⟨N_dp, hN_dp⟩ := Filter.eventually_atTop.mp
    (Asymptotics.IsLittleO.bound Delta_parity_isLittleO_mul_log (show (0 : ℝ) < ε / 128 by positivity))
  have h_alpha_div : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (α - 1)) Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith) |>.comp tendsto_natCast_atTop_atTop
  obtain ⟨N_al, hN_al⟩ := Filter.eventually_atTop.mp
    (h_alpha_div.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < min (ε / 256) (1 / 4) by positivity)))
  have h_invlog : Filter.Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N_il, hN_il⟩ := Filter.eventually_atTop.mp
    (h_invlog.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < min (ε / 256) (1 / 100) by positivity)))
  obtain ⟨N_cs_exp, hN_cs_exp⟩ := Filter.eventually_atTop.mp
    ((tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) :
      Filter.Tendsto (fun n : ℕ => C_cs / Real.log (n : ℝ)) Filter.atTop (nhds 0)).eventually
      (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / 128 by positivity)))
  let N₀ := max (max (max N_flip N_cs) (max N_sodd N_dp)) (max (max N_al N_il) (max N_cs_exp 1000))
  refine ⟨N₀, by omega, ?_⟩
  intro n₁ n₂ m₁ m₂ hn₁ hlt h_gap hm₁ hm₂
  have hn₁_pos : (0 : ℝ) < n₁ := by positivity
  have hlog_n₁_pos : 0 < Real.log (n₁ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n₁))
  have h_al := hN_al n₁ (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h_al
  have hh_lt_n1 : n₂ - n₁ < n₁ := by
    have h1 : (n₁ : ℝ) ^ α = (n₁ : ℝ) * (n₁ : ℝ) ^ (α - 1) := by
      rw [← Real.rpow_one_add' hn₁_pos.le (by linarith : 1 + (α - 1) ≠ 0)]; ring_nf
    have h2 : (n₂ - n₁ : ℝ) < (1 / 4 : ℝ) * (n₁ : ℝ) := by
      calc (n₂ - n₁ : ℝ) ≤ (n₁ : ℝ) ^ α := h_gap
        _ = (n₁ : ℝ) * (n₁ : ℝ) ^ (α - 1) := h1
        _ < (n₁ : ℝ) * min (ε / 256) (1 / 4) := by gcongr
        _ ≤ (n₁ : ℝ) * (1 / 4) := by gcongr; exact min_le_right _ _
        _ = (1 / 4 : ℝ) * (n₁ : ℝ) := by ring
    exact_mod_cast (by linarith : ((n₂ - n₁ : ℕ) : ℝ) < (n₁ : ℝ))
  have hflip_ub : parityFlipWeight n₁ n₂ ≤ (α / 2 + δ + ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
    have hfl := h_flip n₁ n₂ (by omega) hlt hh_lt_n1
    by_cases hδ_le : ((n₂ - n₁ : ℕ) : ℝ) ≤ (n₁ : ℝ) ^ δ
    · have h1 := hfl.1 hδ_le
      nlinarith [show 0 ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
    · push Not at hδ_le
      have h2 := (abs_le.mp (hfl.2 hδ_le)).2
      have hlogh : Real.log ((n₂ - n₁ : ℕ) : ℝ) ≤ α * Real.log (n₁ : ℝ) := by
        have := Real.log_le_log (by exact_mod_cast (by omega : 0 < n₂ - n₁)) h_gap
        rwa [Real.log_rpow hn₁_pos] at this
      nlinarith [show 0 ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
  have hZW_XY := log_ZW_and_XY_bounds (by omega) hlt hm₁ hm₂
  have ⟨_, _, _, _, hXY, _, _, _, _, hZW, hA₁_eq, hB₁_eq, hprod⟩ :=
    prop_6_1_coprime_and_factorization (by omega) hlt hm₁ hm₂
  set u₁₁ := (m₁ - 1) / 2; set u₂₁ := (m₁ + 1) / 2
  set u₁₂ := (m₂ - 1) / 2; set u₂₂ := (m₂ + 1) / 2
  have ⟨hdec11, hdec21, _⟩ := oddPartNat_u_eq_B_mul_Z_sq (by omega) hm₁
  have ⟨hdec12, hdec22, _⟩ := oddPartNat_u_eq_B_mul_Z_sq (by omega) hm₂
  set FlipProd := ∏ p ∈ (Finset.Icc 3 n₁).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (P_ratio n₁ n₂)),
    p ^ padicValNat p (Nat.factorial n₁)
  have hdvd_universal : ∀ (T M₁ M₂ : ℕ), 0 < M₁ → 0 < M₂ → T ∣ Nat.factorial n₁ →
      (∀ p : ℕ, p.Prime → 3 ≤ p → 2 ∣ padicValNat p (P_ratio n₁ n₂) →
        p ∣ T → padicValNat p T ≤ padicValNat p (M₁ * M₂)) →
      T ∣ 2 ^ padicValNat 2 (Nat.factorial n₁) * (M₁ * M₂) * FlipProd := by
    intro T M₁ M₂ hM₁ hM₂ hT_fac hT_odd
    have hT_pos : 0 < T := Nat.pos_of_dvd_of_pos hT_fac (Nat.factorial_pos n₁)
    have hFlip_pos : 0 < FlipProd := Finset.prod_pos (fun p hp =>
      pow_pos (Finset.mem_filter.mp hp).2.1.pos _)
    have hRHS_pos : 0 < 2 ^ padicValNat 2 (Nat.factorial n₁) * (M₁ * M₂) * FlipProd := by positivity
    rw [← Nat.factorization_le_iff_dvd hT_pos.ne' hRHS_pos.ne']
    intro p
    by_cases hp_pr : p.Prime
    · haveI : Fact p.Prime := ⟨hp_pr⟩
      simp only [Nat.factorization_def _ hp_pr]
      by_cases hp2 : p = 2
      · subst hp2
        have hv_le : padicValNat 2 T ≤ padicValNat 2 (Nat.factorial n₁) :=
          (Nat.factorization_le_iff_dvd hT_pos.ne' (Nat.factorial_pos n₁).ne').mpr hT_fac 2
        calc padicValNat 2 T ≤ padicValNat 2 (Nat.factorial n₁) := hv_le
          _ = padicValNat 2 (2 ^ padicValNat 2 (Nat.factorial n₁)) := by
              rw [padicValNat_pow_eq, padicValNat_self]
          _ ≤ padicValNat 2 (2 ^ padicValNat 2 (Nat.factorial n₁) * (M₁ * M₂) * FlipProd) := by
              rw [padicValNat.mul (by positivity) hFlip_pos.ne',
                  padicValNat.mul (by positivity) (by positivity)]
              omega
      · have hp3 : 3 ≤ p := by have := hp_pr.two_le; omega
        by_cases hpT : p ∣ T
        · by_cases hp_flip : 2 ∣ padicValNat p (P_ratio n₁ n₂)
          · have h1 := hT_odd p hp_pr hp3 hp_flip hpT
            calc padicValNat p T ≤ padicValNat p (M₁ * M₂) := h1
              _ ≤ padicValNat p (2 ^ padicValNat 2 (Nat.factorial n₁) * (M₁ * M₂) * FlipProd) := by
                  rw [padicValNat.mul (by positivity) hFlip_pos.ne',
                      padicValNat.mul (by positivity) (by positivity)]
                  omega
          · have hp_le_n1 : p ≤ n₁ := by
              have hp_fac : p ∣ Nat.factorial n₁ := dvd_trans hpT hT_fac
              exact hp_pr.dvd_factorial.mp hp_fac
            have hp_mem : p ∈ (Finset.Icc 3 n₁).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (P_ratio n₁ n₂)) :=
              Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, hp_le_n1⟩, hp_pr, hp_flip⟩
            have hpow_dvd : p ^ padicValNat p (Nat.factorial n₁) ∣ FlipProd :=
              Finset.dvd_prod_of_mem _ hp_mem
            have hv_le1 : padicValNat p T ≤ padicValNat p (Nat.factorial n₁) :=
              (Nat.factorization_le_iff_dvd hT_pos.ne' (Nat.factorial_pos n₁).ne').mpr hT_fac p
            have hv_le2 : padicValNat p (Nat.factorial n₁) ≤ padicValNat p FlipProd := by
              have h1 := (Nat.factorization_le_iff_dvd (pow_pos hp_pr.pos _).ne' hFlip_pos.ne').mpr hpow_dvd p
              simpa [Nat.factorization_def _ hp_pr, padicValNat_pow_eq, padicValNat_self] using h1
            calc padicValNat p T ≤ padicValNat p FlipProd := le_trans hv_le1 hv_le2
              _ ≤ padicValNat p (2 ^ padicValNat 2 (Nat.factorial n₁) * (M₁ * M₂) * FlipProd) := by
                  rw [padicValNat.mul (by positivity) hFlip_pos.ne']
                  omega
        · rw [padicValNat.eq_zero_of_not_dvd hpT]; exact Nat.zero_le _
    · simp [Nat.factorization_eq_zero_of_non_prime _ hp_pr]
  have h_val_part : ∀ (p : ℕ), p.Prime → 3 ≤ p → 2 ∣ padicValNat p (P_ratio n₁ n₂) →
      ∀ (n_a m_a : ℕ), 4 ≤ n_a → Nat.factorial n_a + 1 = m_a ^ 2 →
      (p ∣ (m_a - 1) / 2 →
        (p ∈ Podd n_a → padicValNat p (Nat.factorial n_a) ≤ padicValNat p (B_part n_a ((m_a - 1) / 2))) ∧
        (¬ p ∈ Podd n_a → padicValNat p (Nat.factorial n_a) ≤ padicValNat p (Z_star n_a ((m_a - 1) / 2) ^ 2))) ∧
      (p ∣ (m_a + 1) / 2 →
        (p ∈ Podd n_a → padicValNat p (Nat.factorial n_a) ≤ padicValNat p (B_part n_a ((m_a + 1) / 2))) ∧
        (¬ p ∈ Podd n_a → padicValNat p (Nat.factorial n_a) ≤ padicValNat p (Z_star n_a ((m_a + 1) / 2) ^ 2))) := by
    intro p hp_pr hp3 _ n_a m_a hna hma
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have ⟨_, _, _, hcop, h4mul, _, _⟩ := brocard_u1_u2_rel hna hma
    have ⟨hdec1, hdec2, _⟩ := oddPartNat_u_eq_B_mul_Z_sq hna hma
    have hcop4 : Nat.Coprime p 4 := hp_pr.coprime_iff_not_dvd.mpr (fun h => by
      have : p ∣ 2 := hp_pr.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h)
      have := (Nat.prime_dvd_prime_iff_eq hp_pr Nat.prime_two).mp this; omega)
    have h_eq_u : ∀ (u v : ℕ), 4 * u * v = Nat.factorial n_a → Nat.Coprime u v →
        oddPartNat u = B_part n_a u * Z_star n_a u ^ 2 → p ∣ u →
        padicValNat p (Nat.factorial n_a) = padicValNat p (B_part n_a u * Z_star n_a u ^ 2) := by
      intro u v h4uv hcop_uv hdec hpu
      have hp_nv : ¬ p ∣ v := fun h => hp_pr.not_dvd_one (hcop_uv ▸ Nat.dvd_gcd hpu h)
      have hvp : padicValNat p (Nat.factorial n_a) = padicValNat p u := by
        rw [← h4uv, mul_assoc, padicValNat.mul (by norm_num) (by
          have : 0 < 4 * u * v := h4uv.symm ▸ Nat.factorial_pos n_a; positivity),
          padicValNat.eq_zero_of_not_dvd (fun h => hp_pr.not_dvd_one (hcop4 ▸ Nat.dvd_gcd h (dvd_refl 4))),
          zero_add, padicValNat.mul (by
            have : 0 < 4 * u * v := h4uv.symm ▸ Nat.factorial_pos n_a; positivity) (by
            have : 0 < 4 * u * v := h4uv.symm ▸ Nat.factorial_pos n_a; positivity),
          padicValNat.eq_zero_of_not_dvd hp_nv, add_zero]
      rw [hvp, ← hdec]
      have hu_pos : 0 < u := by
        have : 0 < 4 * u * v := h4uv.symm ▸ Nat.factorial_pos n_a; positivity
      have h2p : u = 2 ^ padicValNat 2 u * oddPartNat u := by
        unfold oddPartNat; exact (Nat.ordProj_mul_ordCompl_eq_self u 2).symm
      conv_lhs => rw [h2p]
      rw [padicValNat.mul (by positivity) (oddPartNat_pos u).ne',
        padicValNat.eq_zero_of_not_dvd (fun h => hp_pr.not_dvd_one (hcop4 ▸ Nat.dvd_gcd (hp_pr.dvd_of_dvd_pow h) (by norm_num))),
        zero_add]
    constructor
    · intro hp_u1
      have hval := h_eq_u ((m_a - 1) / 2) ((m_a + 1) / 2) h4mul hcop hdec1 hp_u1
      constructor
      · intro hp_odd
        rw [hval, padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]
        omega
      · intro hp_even
        rw [hval, padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]
        have hp_nB : ¬ p ∣ B_part n_a ((m_a - 1) / 2) := by
          unfold B_part
          rw [hp_pr.prime.dvd_finset_prod_iff]
          intro ⟨q, hq, hqd⟩
          have hq_mem := Finset.mem_filter.mp hq
          have hq_pr := hq_mem.1.1.1
          have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp (hp_pr.dvd_of_dvd_pow hqd)
          subst hpq; exact hp_even hq_mem.1.1
        rw [padicValNat.eq_zero_of_not_dvd hp_nB, zero_add]
    · intro hp_u2
      have hval := h_eq_u ((m_a + 1) / 2) ((m_a - 1) / 2) (by linarith) hcop.symm hdec2 hp_u2
      constructor
      · intro hp_odd
        rw [hval, padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]
        omega
      · intro hp_even
        rw [hval, padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]
        have hp_nB : ¬ p ∣ B_part n_a ((m_a + 1) / 2) := by
          unfold B_part
          rw [hp_pr.prime.dvd_finset_prod_iff]
          intro ⟨q, hq, hqd⟩
          have hq_mem := Finset.mem_filter.mp hq
          have hq_pr := hq_mem.1.1.1
          have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp (hp_pr.dvd_of_dvd_pow hqd)
          subst hpq; exact hp_even hq_mem.1.1
        rw [padicValNat.eq_zero_of_not_dvd hp_nB, zero_add]
  have hPodd_iff : ∀ p : ℕ, p.Prime → 3 ≤ p → 2 ∣ padicValNat p (P_ratio n₁ n₂) →
      (p ∈ Podd n₁ ↔ p ∈ Podd n₂) := by
    intro p hp_pr _ h2dvd
    have hv := padicValNat_P_ratio_eq_sub hlt hp_pr
    have hmul := P_ratio_mul_factorial hlt
    have hP_pos : 0 < P_ratio n₁ n₂ := by
      by_contra h0; have : P_ratio n₁ n₂ = 0 := by omega
      rw [this, zero_mul] at hmul; exact (Nat.factorial_pos n₂).ne' hmul.symm
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have hv_le : padicValNat p (Nat.factorial n₁) ≤ padicValNat p (Nat.factorial n₂) := by
      have := congrArg (padicValNat p) hmul
      rw [padicValNat.mul hP_pos.ne' (Nat.factorial_pos n₁).ne'] at this; omega
    simp only [Podd, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp_le, _⟩, hp_odd⟩
      refine ⟨⟨le_trans hp_le hlt.le, hp_pr⟩, ?_⟩
      omega
    · rintro ⟨⟨_, _⟩, hp_odd⟩
      have hfac_n1 : padicValNat p (Nat.factorial n₁) ≠ 0 := by
        intro h0; rw [h0] at h2dvd hv; have : padicValNat p (Nat.factorial n₂) = padicValNat p (P_ratio n₁ n₂) := by omega
        exact hp_odd (this ▸ h2dvd)
      have hp_dvd_n1 : p ∣ Nat.factorial n₁ := by
        have : 0 < padicValNat p (Nat.factorial n₁) := Nat.pos_of_ne_zero hfac_n1
        exact dvd_of_padicValNat_pos (Nat.factorial_pos n₁).ne' this
      refine ⟨⟨hp_pr.dvd_factorial.mp hp_dvd_n1, hp_pr⟩, ?_⟩
      omega
  let M₁₁ := B_part n₁ u₁₁ * Z_star n₁ u₂₁ ^ 2
  let M₂₁ := B_part n₁ u₂₁ * Z_star n₁ u₁₁ ^ 2
  let M₁₂ := B_part n₂ u₁₂ * Z_star n₂ u₂₂ ^ 2
  let M₂₂ := B_part n₂ u₂₂ * Z_star n₂ u₁₂ ^ 2
  have hZW_dvd_fac : Z_gcd m₁ m₂ * W_gcd m₁ m₂ ∣ Nat.factorial n₁ := by
    rw [← hprod]; exact ⟨4 * X_gcd m₁ m₂ * Y_gcd m₁ m₂, by ring⟩
  have hXY_dvd_fac : X_gcd m₁ m₂ * Y_gcd m₁ m₂ ∣ Nat.factorial n₁ := by
    rw [← hprod]; exact ⟨4 * Z_gcd m₁ m₂ * W_gcd m₁ m₂, by ring⟩
  have h_log_bound_from_M : ∀ (T Ma Mb : ℕ), 0 < T → 0 < Ma → 0 < Mb →
      T ∣ 2 ^ padicValNat 2 (Nat.factorial n₁) * (Ma * Mb) * FlipProd →
      Real.log (T : ℝ) ≤ (n₁ : ℝ) * Real.log 2 + Real.log (Ma : ℝ) + Real.log (Mb : ℝ) + parityFlipWeight n₁ n₂ := by
    intro T Ma Mb hT hMa hMb hdvd
    have hFlip_pos : 0 < FlipProd := Finset.prod_pos (fun p hp =>
      pow_pos (Finset.mem_filter.mp hp).2.1.pos _)
    have hle := Real.log_le_log (by exact_mod_cast hT) (by
      exact_mod_cast Nat.le_of_dvd (by positivity) hdvd)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) hFlip_pos.ne',
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Nat.cast_pow, Real.log_pow] at hle
    have hv2_le : (padicValNat 2 (Nat.factorial n₁) : ℝ) ≤ (n₁ : ℝ) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := sub_one_mul_padicValNat_factorial (p := 2) n₁
      exact_mod_cast (by linarith : padicValNat 2 (Nat.factorial n₁) ≤ n₁)
    have hlog_flip : Real.log (FlipProd : ℝ) = parityFlipWeight n₁ n₂ := by
      dsimp [FlipProd, parityFlipWeight]
      rw [Nat.cast_prod, Real.log_prod _ _ (fun p hp => by
        exact pow_ne_zero _ (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.ne_zero))]
      apply Finset.sum_congr rfl; intro p _; rw [Nat.cast_pow, Real.log_pow]
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hdvd_ZW_22 : Z_gcd m₁ m₂ * W_gcd m₁ m₂ ∣
      2 ^ padicValNat 2 (Nat.factorial n₁) * (M₂₁ * M₂₂) * FlipProd := by
    refine hdvd_universal _ M₂₁ M₂₂ (by positivity) (by positivity) hZW_dvd_fac ?_
    intro p hp_pr hp3 h2dvd hpZW
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have hv_le_n1 : padicValNat p (Z_gcd m₁ m₂ * W_gcd m₁ m₂) ≤ padicValNat p (Nat.factorial n₁) :=
      (Nat.factorization_le_iff_dvd (by
        have := Nat.pos_of_dvd_of_pos hZW_dvd_fac (Nat.factorial_pos n₁); exact this.ne')
        (Nat.factorial_pos n₁).ne').mpr hZW_dvd_fac p
    have hv_le_n2 : padicValNat p (Nat.factorial n₁) ≤ padicValNat p (Nat.factorial n₂) := by
      have hmul := P_ratio_mul_factorial hlt
      have hP_pos : 0 < P_ratio n₁ n₂ := by
        by_contra h0; have : P_ratio n₁ n₂ = 0 := by omega
        rw [this, zero_mul] at hmul; exact (Nat.factorial_pos n₂).ne' hmul.symm
      have := congrArg (padicValNat p) hmul
      rw [padicValNat.mul hP_pos.ne' (Nat.factorial_pos n₁).ne'] at this; omega
    have h1 := h_val_part p hp_pr hp3 h2dvd n₁ m₁ (by omega) hm₁
    have h2 := h_val_part p hp_pr hp3 h2dvd n₂ m₂ (by omega) hm₂
    rcases hp_pr.dvd_mul.mp hpZW with hpZ | hpW
    · by_cases hp_odd : p ∈ Podd n₁
      · have hp_odd2 := (hPodd_iff p hp_pr hp3 h2dvd).mp hp_odd
        have hp_u22 : p ∣ u₂₂ := dvd_trans hpZ (Nat.gcd_dvd_right _ _)
        have hB22 := (h2.2 hp_u22).1 hp_odd2
        have hle_M22 : padicValNat p (B_part n₂ u₂₂) ≤ padicValNat p M₂₂ := by
          dsimp [M₂₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₂ ≤ padicValNat p (M₂₁ * M₂₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
      · have hp_u11 : p ∣ u₁₁ := dvd_trans hpZ (Nat.gcd_dvd_left _ _)
        have hZ11 := (h1.1 hp_u11).2 hp_odd
        have hle_M21 : padicValNat p (Z_star n₁ u₁₁ ^ 2) ≤ padicValNat p M₂₁ := by
          dsimp [M₂₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₁ ≤ padicValNat p (M₂₁ * M₂₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
    · by_cases hp_odd : p ∈ Podd n₁
      · have hp_u21 : p ∣ u₂₁ := dvd_trans hpW (Nat.gcd_dvd_left _ _)
        have hB21 := (h1.2 hp_u21).1 hp_odd
        have hle_M21 : padicValNat p (B_part n₁ u₂₁) ≤ padicValNat p M₂₁ := by
          dsimp [M₂₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₁ ≤ padicValNat p (M₂₁ * M₂₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
      · have hp_even2 : ¬ p ∈ Podd n₂ := fun h => hp_odd ((hPodd_iff p hp_pr hp3 h2dvd).mpr h)
        have hp_u12 : p ∣ u₁₂ := dvd_trans hpW (Nat.gcd_dvd_right _ _)
        have hZ12 := (h2.1 hp_u12).2 hp_even2
        have hle_M22 : padicValNat p (Z_star n₂ u₁₂ ^ 2) ≤ padicValNat p M₂₂ := by
          dsimp [M₂₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₂ ≤ padicValNat p (M₂₁ * M₂₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
  have hdvd_ZW_11 : Z_gcd m₁ m₂ * W_gcd m₁ m₂ ∣
      2 ^ padicValNat 2 (Nat.factorial n₁) * (M₁₁ * M₁₂) * FlipProd := by
    refine hdvd_universal _ M₁₁ M₁₂ (by positivity) (by positivity) hZW_dvd_fac ?_
    intro p hp_pr hp3 h2dvd hpZW
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have hv_le_n1 : padicValNat p (Z_gcd m₁ m₂ * W_gcd m₁ m₂) ≤ padicValNat p (Nat.factorial n₁) :=
      (Nat.factorization_le_iff_dvd (by
        have := Nat.pos_of_dvd_of_pos hZW_dvd_fac (Nat.factorial_pos n₁); exact this.ne')
        (Nat.factorial_pos n₁).ne').mpr hZW_dvd_fac p
    have hv_le_n2 : padicValNat p (Nat.factorial n₁) ≤ padicValNat p (Nat.factorial n₂) := by
      have hmul := P_ratio_mul_factorial hlt
      have hP_pos : 0 < P_ratio n₁ n₂ := by
        by_contra h0; have : P_ratio n₁ n₂ = 0 := by omega
        rw [this, zero_mul] at hmul; exact (Nat.factorial_pos n₂).ne' hmul.symm
      have := congrArg (padicValNat p) hmul
      rw [padicValNat.mul hP_pos.ne' (Nat.factorial_pos n₁).ne'] at this; omega
    have h1 := h_val_part p hp_pr hp3 h2dvd n₁ m₁ (by omega) hm₁
    have h2 := h_val_part p hp_pr hp3 h2dvd n₂ m₂ (by omega) hm₂
    rcases hp_pr.dvd_mul.mp hpZW with hpZ | hpW
    · by_cases hp_odd : p ∈ Podd n₁
      · have hp_u11 : p ∣ u₁₁ := dvd_trans hpZ (Nat.gcd_dvd_left _ _)
        have hB11 := (h1.1 hp_u11).1 hp_odd
        have hle_M11 : padicValNat p (B_part n₁ u₁₁) ≤ padicValNat p M₁₁ := by
          dsimp [M₁₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₁₁ ≤ padicValNat p (M₁₁ * M₁₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
      · have hp_even2 : ¬ p ∈ Podd n₂ := fun h => hp_odd ((hPodd_iff p hp_pr hp3 h2dvd).mpr h)
        have hp_u22 : p ∣ u₂₂ := dvd_trans hpZ (Nat.gcd_dvd_right _ _)
        have hZ22 := (h2.2 hp_u22).2 hp_even2
        have hle_M12 : padicValNat p (Z_star n₂ u₂₂ ^ 2) ≤ padicValNat p M₁₂ := by
          dsimp [M₁₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₁₂ ≤ padicValNat p (M₁₁ * M₁₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
    · by_cases hp_odd : p ∈ Podd n₁
      · have hp_odd2 := (hPodd_iff p hp_pr hp3 h2dvd).mp hp_odd
        have hp_u12 : p ∣ u₁₂ := dvd_trans hpW (Nat.gcd_dvd_right _ _)
        have hB12 := (h2.1 hp_u12).1 hp_odd2
        have hle_M12 : padicValNat p (B_part n₂ u₁₂) ≤ padicValNat p M₁₂ := by
          dsimp [M₁₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₁₂ ≤ padicValNat p (M₁₁ * M₁₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
      · have hp_u21 : p ∣ u₂₁ := dvd_trans hpW (Nat.gcd_dvd_left _ _)
        have hZ21 := (h1.2 hp_u21).2 hp_odd
        have hle_M11 : padicValNat p (Z_star n₁ u₂₁ ^ 2) ≤ padicValNat p M₁₁ := by
          dsimp [M₁₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₁₁ ≤ padicValNat p (M₁₁ * M₁₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
  have hdvd_XY_12 : X_gcd m₁ m₂ * Y_gcd m₁ m₂ ∣
      2 ^ padicValNat 2 (Nat.factorial n₁) * (M₁₁ * M₂₂) * FlipProd := by
    refine hdvd_universal _ M₁₁ M₂₂ (by positivity) (by positivity) hXY_dvd_fac ?_
    intro p hp_pr hp3 h2dvd hpXY
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have hv_le_n1 : padicValNat p (X_gcd m₁ m₂ * Y_gcd m₁ m₂) ≤ padicValNat p (Nat.factorial n₁) :=
      (Nat.factorization_le_iff_dvd (by
        have := Nat.pos_of_dvd_of_pos hXY_dvd_fac (Nat.factorial_pos n₁); exact this.ne')
        (Nat.factorial_pos n₁).ne').mpr hXY_dvd_fac p
    have hv_le_n2 : padicValNat p (Nat.factorial n₁) ≤ padicValNat p (Nat.factorial n₂) := by
      have hmul := P_ratio_mul_factorial hlt
      have hP_pos : 0 < P_ratio n₁ n₂ := by
        by_contra h0; have : P_ratio n₁ n₂ = 0 := by omega
        rw [this, zero_mul] at hmul; exact (Nat.factorial_pos n₂).ne' hmul.symm
      have := congrArg (padicValNat p) hmul
      rw [padicValNat.mul hP_pos.ne' (Nat.factorial_pos n₁).ne'] at this; omega
    have h1 := h_val_part p hp_pr hp3 h2dvd n₁ m₁ (by omega) hm₁
    have h2 := h_val_part p hp_pr hp3 h2dvd n₂ m₂ (by omega) hm₂
    rcases hp_pr.dvd_mul.mp hpXY with hpX | hpY
    · by_cases hp_odd : p ∈ Podd n₁
      · have hp_u11 : p ∣ u₁₁ := dvd_trans hpX (Nat.gcd_dvd_left _ _)
        have hB11 := (h1.1 hp_u11).1 hp_odd
        have hle_M11 : padicValNat p (B_part n₁ u₁₁) ≤ padicValNat p M₁₁ := by
          dsimp [M₁₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₁₁ ≤ padicValNat p (M₁₁ * M₂₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
      · have hp_even2 : ¬ p ∈ Podd n₂ := fun h => hp_odd ((hPodd_iff p hp_pr hp3 h2dvd).mpr h)
        have hp_u12 : p ∣ u₁₂ := dvd_trans hpX (Nat.gcd_dvd_right _ _)
        have hZ12 := (h2.1 hp_u12).2 hp_even2
        have hle_M22 : padicValNat p (Z_star n₂ u₁₂ ^ 2) ≤ padicValNat p M₂₂ := by
          dsimp [M₂₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₂ ≤ padicValNat p (M₁₁ * M₂₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
    · by_cases hp_odd : p ∈ Podd n₁
      · have hp_odd2 := (hPodd_iff p hp_pr hp3 h2dvd).mp hp_odd
        have hp_u22 : p ∣ u₂₂ := dvd_trans hpY (Nat.gcd_dvd_right _ _)
        have hB22 := (h2.2 hp_u22).1 hp_odd2
        have hle_M22 : padicValNat p (B_part n₂ u₂₂) ≤ padicValNat p M₂₂ := by
          dsimp [M₂₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₂ ≤ padicValNat p (M₁₁ * M₂₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
      · have hp_u21 : p ∣ u₂₁ := dvd_trans hpY (Nat.gcd_dvd_left _ _)
        have hZ21 := (h1.2 hp_u21).2 hp_odd
        have hle_M11 : padicValNat p (Z_star n₁ u₂₁ ^ 2) ≤ padicValNat p M₁₁ := by
          dsimp [M₁₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₁₁ ≤ padicValNat p (M₁₁ * M₂₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
  have hdvd_XY_21 : X_gcd m₁ m₂ * Y_gcd m₁ m₂ ∣
      2 ^ padicValNat 2 (Nat.factorial n₁) * (M₂₁ * M₁₂) * FlipProd := by
    refine hdvd_universal _ M₂₁ M₁₂ (by positivity) (by positivity) hXY_dvd_fac ?_
    intro p hp_pr hp3 h2dvd hpXY
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have hv_le_n1 : padicValNat p (X_gcd m₁ m₂ * Y_gcd m₁ m₂) ≤ padicValNat p (Nat.factorial n₁) :=
      (Nat.factorization_le_iff_dvd (by
        have := Nat.pos_of_dvd_of_pos hXY_dvd_fac (Nat.factorial_pos n₁); exact this.ne')
        (Nat.factorial_pos n₁).ne').mpr hXY_dvd_fac p
    have hv_le_n2 : padicValNat p (Nat.factorial n₁) ≤ padicValNat p (Nat.factorial n₂) := by
      have hmul := P_ratio_mul_factorial hlt
      have hP_pos : 0 < P_ratio n₁ n₂ := by
        by_contra h0; have : P_ratio n₁ n₂ = 0 := by omega
        rw [this, zero_mul] at hmul; exact (Nat.factorial_pos n₂).ne' hmul.symm
      have := congrArg (padicValNat p) hmul
      rw [padicValNat.mul hP_pos.ne' (Nat.factorial_pos n₁).ne'] at this; omega
    have h1 := h_val_part p hp_pr hp3 h2dvd n₁ m₁ (by omega) hm₁
    have h2 := h_val_part p hp_pr hp3 h2dvd n₂ m₂ (by omega) hm₂
    rcases hp_pr.dvd_mul.mp hpXY with hpX | hpY
    · by_cases hp_odd : p ∈ Podd n₁
      · have hp_odd2 := (hPodd_iff p hp_pr hp3 h2dvd).mp hp_odd
        have hp_u12 : p ∣ u₁₂ := dvd_trans hpX (Nat.gcd_dvd_right _ _)
        have hB12 := (h2.1 hp_u12).1 hp_odd2
        have hle_M12 : padicValNat p (B_part n₂ u₁₂) ≤ padicValNat p M₁₂ := by
          dsimp [M₁₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₁₂ ≤ padicValNat p (M₂₁ * M₁₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
      · have hp_u11 : p ∣ u₁₁ := dvd_trans hpX (Nat.gcd_dvd_left _ _)
        have hZ11 := (h1.1 hp_u11).2 hp_odd
        have hle_M21 : padicValNat p (Z_star n₁ u₁₁ ^ 2) ≤ padicValNat p M₂₁ := by
          dsimp [M₂₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₁ ≤ padicValNat p (M₂₁ * M₁₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
    · by_cases hp_odd : p ∈ Podd n₁
      · have hp_u21 : p ∣ u₂₁ := dvd_trans hpY (Nat.gcd_dvd_left _ _)
        have hB21 := (h1.2 hp_u21).1 hp_odd
        have hle_M21 : padicValNat p (B_part n₁ u₂₁) ≤ padicValNat p M₂₁ := by
          dsimp [M₂₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₁ ≤ padicValNat p (M₂₁ * M₁₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
      · have hp_even2 : ¬ p ∈ Podd n₂ := fun h => hp_odd ((hPodd_iff p hp_pr hp3 h2dvd).mpr h)
        have hp_u22 : p ∣ u₂₂ := dvd_trans hpY (Nat.gcd_dvd_right _ _)
        have hZ22 := (h2.2 hp_u22).2 hp_even2
        have hle_M12 : padicValNat p (Z_star n₂ u₂₂ ^ 2) ≤ padicValNat p M₁₂ := by
          dsimp [M₁₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₁₂ ≤ padicValNat p (M₂₁ * M₁₂) := by
          rw [padicValNat.mul (by positivity) (by positivity)]; omega
        omega
  have hlog_M_rel : ∀ (n_a m_a : ℕ), N₀ ≤ n_a → n_a ≤ n₂ → Nat.factorial n_a + 1 = m_a ^ 2 →
      let u₁a := (m_a - 1) / 2; let u₂a := (m_a + 1) / 2
      |Real.log ((B_part n_a u₂a * Z_star n_a u₁a ^ 2 : ℕ) : ℝ) -
        theta_weight n_a m_a * (n₁ : ℝ) * Real.log (n₁ : ℝ)| ≤ (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) ∧
      |Real.log ((B_part n_a u₁a * Z_star n_a u₂a ^ 2 : ℕ) : ℝ) -
        (1 - theta_weight n_a m_a) * (n₁ : ℝ) * Real.log (n₁ : ℝ)| ≤ (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
    intro n_a m_a hna hna_le hma
    have hcs := h_cs n_a m_a (by omega) hma
    dsimp only at hcs
    have hSodd_a : |S_odd n_a - (1 / 2 : ℝ) * (n_a : ℝ) * Real.log (n_a : ℝ)| ≤
        min (ε / 128) (1 / 8) * (n_a : ℝ) * Real.log (n_a : ℝ) := by
      have h1 := hN_sodd n_a (by omega)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
      linarith
    have hSodd_pos : 0 < S_odd n_a := by
      have := (abs_le.mp hSodd_a).1
      have h1 : (1 / 8 : ℝ) ≥ min (ε / 128) (1 / 8) := min_le_right _ _
      have hlog_a : 0 < Real.log (n_a : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n_a))
      nlinarith [show (0 : ℝ) < n_a by positivity]
    have hθ_eq : Real.log (B_part n_a ((m_a + 1) / 2) : ℝ) = theta_weight n_a m_a * S_odd n_a := by
      unfold theta_weight; rw [if_pos hSodd_pos, div_mul_cancel₀ _ hSodd_pos.ne']
    have hB_prod : B_part n_a ((m_a - 1) / 2) * B_part n_a ((m_a + 1) / 2) = B_star5 n_a :=
      (oddPartNat_u_eq_B_mul_Z_sq (by omega) hma).2.2
    have hlog_Bstar : Real.log (B_star5 n_a : ℝ) = S_odd n_a := by
      unfold B_star5 S_odd
      rw [Nat.cast_prod, Real.log_prod _ _ (fun p hp => by
        exact pow_ne_zero _ (by exact_mod_cast (Finset.mem_filter.mp hp).1.ne_zero))]
      apply Finset.sum_congr rfl; intro p _; rw [Nat.cast_pow, Real.log_pow]
    have hlog_B1_eq : Real.log (B_part n_a ((m_a - 1) / 2) : ℝ) = (1 - theta_weight n_a m_a) * S_odd n_a := by
      have h1 := congrArg (fun k : ℕ => Real.log (k : ℝ)) hB_prod
      rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (B_part_pos _ _).ne')
        (by exact_mod_cast (B_part_pos _ _).ne'), hlog_Bstar, hθ_eq] at h1
      linarith
    have hM2_log : Real.log ((B_part n_a ((m_a + 1) / 2) * Z_star n_a ((m_a - 1) / 2) ^ 2 : ℕ) : ℝ) =
        2 * Real.log (B_part n_a ((m_a + 1) / 2) : ℝ) -
        (Real.log (B_part n_a ((m_a + 1) / 2) : ℝ) - Real.log ((Z_star n_a ((m_a - 1) / 2) : ℝ) ^ 2)) := by
      rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (B_part_pos _ _).ne')
        (by exact_mod_cast (pow_pos (Z_star_pos _ _) 2).ne'), Nat.cast_pow]
      ring
    have hM1_log : Real.log ((B_part n_a ((m_a - 1) / 2) * Z_star n_a ((m_a + 1) / 2) ^ 2 : ℕ) : ℝ) =
        2 * Real.log (B_part n_a ((m_a - 1) / 2) : ℝ) -
        (Real.log (B_part n_a ((m_a - 1) / 2) : ℝ) - Real.log ((Z_star n_a ((m_a + 1) / 2) : ℝ) ^ 2)) := by
      rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (B_part_pos _ _).ne')
        (by exact_mod_cast (pow_pos (Z_star_pos _ _) 2).ne'), Nat.cast_pow]
      ring
    have hna_pos : (0 : ℝ) < n_a := by positivity
    have hlog_a_pos : 0 < Real.log (n_a : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n_a))
    have h_il := hN_il n₁ (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h_il
    have hna_ub : (n_a : ℝ) ≤ (1 + min (ε / 256) (1 / 4)) * (n₁ : ℝ) := by
      have h1 : (n₁ : ℝ) ^ α = (n₁ : ℝ) * (n₁ : ℝ) ^ (α - 1) := by
        rw [← Real.rpow_one_add' hn₁_pos.le (by linarith : 1 + (α - 1) ≠ 0)]; ring_nf
      have h_gap_le : (n₂ - n₁ : ℝ) ≤ min (ε / 256) (1 / 4) * (n₁ : ℝ) := by
        calc (n₂ - n₁ : ℝ) ≤ (n₁ : ℝ) ^ α := h_gap
          _ = (n₁ : ℝ) * (n₁ : ℝ) ^ (α - 1) := h1
          _ ≤ (n₁ : ℝ) * min (ε / 256) (1 / 4) := by gcongr; exact h_al.le
          _ = min (ε / 256) (1 / 4) * (n₁ : ℝ) := by ring
      have hn2_le : (n₂ : ℝ) ≤ (1 + min (ε / 256) (1 / 4)) * (n₁ : ℝ) := by
        have : (n₂ : ℝ) = (n₁ : ℝ) + ((n₂ - n₁ : ℕ) : ℝ) := by
          exact_mod_cast (by omega : n₂ = n₁ + (n₂ - n₁))
        linarith
      exact le_trans (by exact_mod_cast hna_le) hn2_le
    have hlog_a_ub : Real.log (n_a : ℝ) ≤ (1 + min (ε / 256) (1 / 4)) * Real.log (n₁ : ℝ) := by
      have h1 : (n_a : ℝ) ≤ 2 * (n₁ : ℝ) := by
        have : min (ε / 256) (1 / 4) ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
        nlinarith
      have h2 := Real.log_le_log hna_pos h1
      rw [Real.log_mul (by norm_num) hn₁_pos.ne'] at h2
      have hlog2 : Real.log 2 ≤ min (ε / 256) (1 / 4) * Real.log (n₁ : ℝ) := by
        have := (div_lt_iff₀ hlog_n₁_pos).mp h_il
        linarith [Real.log_two_lt_d9]
      linarith
    have hna_log_ub : (n_a : ℝ) * Real.log (n_a : ℝ) ≤ (1 + ε / 64) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      have hmin1 : min (ε / 256) (1 / 4) ≤ 1 / 4 := min_le_right _ _
      have hmin2 : min (ε / 256) (1 / 4) ≤ ε / 256 := min_le_left _ _
      calc (n_a : ℝ) * Real.log (n_a : ℝ)
          ≤ ((1 + min (ε / 256) (1 / 4)) * (n₁ : ℝ)) * ((1 + min (ε / 256) (1 / 4)) * Real.log (n₁ : ℝ)) := by gcongr
        _ = (1 + 2 * min (ε / 256) (1 / 4) + (min (ε / 256) (1 / 4)) ^ 2) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
        _ ≤ (1 + 2 * (ε / 256) + (1 / 4) * (ε / 256)) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
            gcongr; rw [sq]; exact mul_le_mul hmin1 hmin2 (by positivity) (by norm_num)
        _ ≤ (1 + ε / 64) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
            gcongr; linarith
    have hna_log_lb : (1 - ε / 64) * (n₁ : ℝ) * Real.log (n₁ : ℝ) ≤ (n_a : ℝ) * Real.log (n_a : ℝ) := by
      have h1 : (n₁ : ℝ) * Real.log (n₁ : ℝ) ≤ (n_a : ℝ) * Real.log (n_a : ℝ) := by
        gcongr <;> exact_mod_cast (by omega : n₁ ≤ n_a)
      nlinarith [show 0 ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
    have h_na_13 : (n_a : ℝ) * Real.log (n_a : ℝ) ≤ (4 / 3 : ℝ) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      have hm1 : min (ε / 256) (1 / 4) ≤ 1 / 4 := min_le_right _ _
      have hlog_a_101 : Real.log (n_a : ℝ) ≤ (101 / 100 : ℝ) * Real.log (n₁ : ℝ) := by
        have h1' : (n_a : ℝ) ≤ 2 * (n₁ : ℝ) := by nlinarith
        have h2' := Real.log_le_log hna_pos h1'
        rw [Real.log_mul (by norm_num) hn₁_pos.ne'] at h2'
        have hlog2 : Real.log 2 ≤ (1 / 100) * Real.log (n₁ : ℝ) := by
          have := (div_lt_iff₀ hlog_n₁_pos).mp h_il
          have hmin : min (ε / 256) (1 / 100) ≤ 1 / 100 := min_le_right _ _
          linarith [Real.log_two_lt_d9]
        linarith
      calc (n_a : ℝ) * Real.log (n_a : ℝ)
          ≤ ((5 / 4 : ℝ) * (n₁ : ℝ)) * ((101 / 100 : ℝ) * Real.log (n₁ : ℝ)) := by gcongr; linarith
        _ ≤ (4 / 3 : ℝ) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by gcongr; norm_num
    have h_cs_err : C_cs * Real.exp (-(1 / 3 : ℝ) * (n_a : ℝ) * Real.log (n_a : ℝ)) +
        |(padicValNat 2 ((m_a - 1) / 2) : ℝ) - (padicValNat 2 ((m_a + 1) / 2) : ℝ)| * Real.log 2 / 2 +
        |Delta_parity_odd n_a| / 2 ≤ (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      have h1 : C_cs * Real.exp (-(1 / 3 : ℝ) * (n_a : ℝ) * Real.log (n_a : ℝ)) ≤ C_cs := by
        have : Real.exp (-(1 / 3 : ℝ) * (n_a : ℝ) * Real.log (n_a : ℝ)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [show 0 ≤ (n_a : ℝ) * Real.log (n_a : ℝ) by positivity])
        nlinarith
      have hC_le : C_cs ≤ (ε / 128) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have h := hN_cs_exp n₁ (by omega)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
        have h' := (div_lt_iff₀ hlog_n₁_pos).mp h
        have hn1_1 : (1 : ℝ) ≤ n₁ := by exact_mod_cast (by omega : 1 ≤ n₁)
        nlinarith [show 0 ≤ Real.log (n₁ : ℝ) by linarith]
      have hw2_le : |(padicValNat 2 ((m_a - 1) / 2) : ℝ) - (padicValNat 2 ((m_a + 1) / 2) : ℝ)| * Real.log 2 / 2 ≤
          (n_a : ℝ) * Real.log 2 / 2 := by
        have h4 : 4 * ((m_a - 1) / 2) * ((m_a + 1) / 2) = Nat.factorial n_a :=
          (brocard_u1_u2_rel (by omega) hma).2.2.2.2.1
        have hv1 : padicValNat 2 ((m_a - 1) / 2) ≤ n_a := by
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          have hdvd : (m_a - 1) / 2 ∣ Nat.factorial n_a := ⟨4 * ((m_a + 1) / 2), by linarith⟩
          have hv := (Nat.factorization_le_iff_dvd (brocard_u1_u2_rel (by omega) hma).1.ne'
            (Nat.factorial_pos n_a).ne').mpr hdvd 2
          simp only [Nat.factorization_def _ Nat.prime_two] at hv
          have := sub_one_mul_padicValNat_factorial (p := 2) n_a; omega
        have hv2 : padicValNat 2 ((m_a + 1) / 2) ≤ n_a := by
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          have hdvd : (m_a + 1) / 2 ∣ Nat.factorial n_a := ⟨4 * ((m_a - 1) / 2), by linarith⟩
          have hv := (Nat.factorization_le_iff_dvd (brocard_u1_u2_rel (by omega) hma).2.1.ne'
            (Nat.factorial_pos n_a).ne').mpr hdvd 2
          simp only [Nat.factorization_def _ Nat.prime_two] at hv
          have := sub_one_mul_padicValNat_factorial (p := 2) n_a; omega
        have habs : |(padicValNat 2 ((m_a - 1) / 2) : ℝ) - (padicValNat 2 ((m_a + 1) / 2) : ℝ)| ≤ (n_a : ℝ) := by
          rw [abs_le]; constructor <;> linarith [show (0 : ℝ) ≤ padicValNat 2 ((m_a - 1) / 2) by positivity,
            show (0 : ℝ) ≤ padicValNat 2 ((m_a + 1) / 2) by positivity,
            show (padicValNat 2 ((m_a - 1) / 2) : ℝ) ≤ n_a by exact_mod_cast hv1,
            show (padicValNat 2 ((m_a + 1) / 2) : ℝ) ≤ n_a by exact_mod_cast hv2]
        gcongr
      have hw2_sm : (n_a : ℝ) * Real.log 2 / 2 ≤ (ε / 128) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have h2 : Real.log 2 / 2 ≤ (ε / 256) * Real.log (n₁ : ℝ) := by
          have := (div_lt_iff₀ hlog_n₁_pos).mp h_il
          have hmin : min (ε / 256) (1 / 100) ≤ ε / 256 := min_le_left _ _
          linarith [Real.log_two_lt_d9]
        calc (n_a : ℝ) * Real.log 2 / 2 = (n_a : ℝ) * (Real.log 2 / 2) := by ring
          _ ≤ (2 * (n₁ : ℝ)) * ((ε / 256) * Real.log (n₁ : ℝ)) := by
              gcongr
              have : min (ε / 256) (1 / 4) ≤ 1 := le_trans (min_le_right _ _) (by norm_num); nlinarith
          _ = (ε / 128) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
      have hdp_le : |Delta_parity_odd n_a| / 2 ≤ (ε / 64) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have hdp_eq : Delta_parity_odd n_a = Delta_parity n_a := by
          unfold Delta_parity_odd Delta_parity S_even S_odd; rfl
        rw [hdp_eq]
        have h1 := hN_dp n_a (by omega)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
        have h2 : |Delta_parity n_a| / 2 ≤ (ε / 256) * (n_a : ℝ) * Real.log (n_a : ℝ) := by linarith
        nlinarith [show (0 : ℝ) ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
      linarith
    have hθ_01 : 0 ≤ theta_weight n_a m_a ∧ theta_weight n_a m_a ≤ 1 :=
      ⟨theta_weight_nonneg n_a m_a, theta_weight_le_one (by omega) hma⟩
    have h_diff_S : |2 * S_odd n_a - (n₁ : ℝ) * Real.log (n₁ : ℝ)| ≤ (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      have h1 : |2 * S_odd n_a - (n_a : ℝ) * Real.log (n_a : ℝ)| ≤ (ε / 64) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have h1' := abs_le.mp hSodd_a
        have hmin : min (ε / 128) (1 / 8) ≤ ε / 128 := min_le_left _ _
        rw [abs_le]; constructor <;> nlinarith [show 0 ≤ (n_a : ℝ) * Real.log (n_a : ℝ) by positivity,
          show 0 ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
      have h2 : |(n_a : ℝ) * Real.log (n_a : ℝ) - (n₁ : ℝ) * Real.log (n₁ : ℝ)| ≤ (ε / 64) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        rw [abs_le]; constructor <;> linarith
      rw [abs_le] at h1 h2 ⊢; constructor <;> linarith
    have h_cs1 := hcs.1
    have h_cs2 := hcs.2
    have h_abs1 : |Real.log (B_part n_a ((m_a + 1) / 2) : ℝ) - Real.log ((Z_star n_a ((m_a - 1) / 2) : ℝ) ^ 2)| ≤
        (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      have h_tri' : |Real.log (B_part n_a ((m_a + 1) / 2) : ℝ) - Real.log ((Z_star n_a ((m_a - 1) / 2) : ℝ) ^ 2)| ≤
          |Real.log (B_part n_a ((m_a + 1) / 2) : ℝ) - Real.log ((Z_star n_a ((m_a - 1) / 2) : ℝ) ^ 2) -
            (1 / 2 : ℝ) * (((padicValNat 2 ((m_a - 1) / 2) : ℝ) - (padicValNat 2 ((m_a + 1) / 2) : ℝ)) * Real.log 2 - Delta_parity_odd n_a)| +
          |(1 / 2 : ℝ) * (((padicValNat 2 ((m_a - 1) / 2) : ℝ) - (padicValNat 2 ((m_a + 1) / 2) : ℝ)) * Real.log 2 - Delta_parity_odd n_a)| := by
        simpa using abs_add_le
          (Real.log (B_part n_a ((m_a + 1) / 2) : ℝ) - Real.log ((Z_star n_a ((m_a - 1) / 2) : ℝ) ^ 2) -
            (1 / 2 : ℝ) * (((padicValNat 2 ((m_a - 1) / 2) : ℝ) - (padicValNat 2 ((m_a + 1) / 2) : ℝ)) * Real.log 2 - Delta_parity_odd n_a))
          ((1 / 2 : ℝ) * (((padicValNat 2 ((m_a - 1) / 2) : ℝ) - (padicValNat 2 ((m_a + 1) / 2) : ℝ)) * Real.log 2 - Delta_parity_odd n_a))
      have h_half : |(1 / 2 : ℝ) * (((padicValNat 2 ((m_a - 1) / 2) : ℝ) - (padicValNat 2 ((m_a + 1) / 2) : ℝ)) * Real.log 2 - Delta_parity_odd n_a)| ≤
          |(padicValNat 2 ((m_a - 1) / 2) : ℝ) - (padicValNat 2 ((m_a + 1) / 2) : ℝ)| * Real.log 2 / 2 + |Delta_parity_odd n_a| / 2 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        have h_sub := abs_sub (((padicValNat 2 ((m_a - 1) / 2) : ℝ) - (padicValNat 2 ((m_a + 1) / 2) : ℝ)) * Real.log 2) (Delta_parity_odd n_a)
        rw [abs_mul, abs_of_nonneg (Real.log_nonneg (by norm_num))] at h_sub
        linarith
      linarith
    have h_abs2 : |Real.log (B_part n_a ((m_a - 1) / 2) : ℝ) - Real.log ((Z_star n_a ((m_a + 1) / 2) : ℝ) ^ 2)| ≤
        (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      have h_tri' : |Real.log (B_part n_a ((m_a - 1) / 2) : ℝ) - Real.log ((Z_star n_a ((m_a + 1) / 2) : ℝ) ^ 2)| ≤
          |Real.log (B_part n_a ((m_a - 1) / 2) : ℝ) - Real.log ((Z_star n_a ((m_a + 1) / 2) : ℝ) ^ 2) -
            (1 / 2 : ℝ) * (((padicValNat 2 ((m_a + 1) / 2) : ℝ) - (padicValNat 2 ((m_a - 1) / 2) : ℝ)) * Real.log 2 - Delta_parity_odd n_a)| +
          |(1 / 2 : ℝ) * (((padicValNat 2 ((m_a + 1) / 2) : ℝ) - (padicValNat 2 ((m_a - 1) / 2) : ℝ)) * Real.log 2 - Delta_parity_odd n_a)| := by
        simpa using abs_add_le
          (Real.log (B_part n_a ((m_a - 1) / 2) : ℝ) - Real.log ((Z_star n_a ((m_a + 1) / 2) : ℝ) ^ 2) -
            (1 / 2 : ℝ) * (((padicValNat 2 ((m_a + 1) / 2) : ℝ) - (padicValNat 2 ((m_a - 1) / 2) : ℝ)) * Real.log 2 - Delta_parity_odd n_a))
          ((1 / 2 : ℝ) * (((padicValNat 2 ((m_a + 1) / 2) : ℝ) - (padicValNat 2 ((m_a - 1) / 2) : ℝ)) * Real.log 2 - Delta_parity_odd n_a))
      have h_half : |(1 / 2 : ℝ) * (((padicValNat 2 ((m_a + 1) / 2) : ℝ) - (padicValNat 2 ((m_a - 1) / 2) : ℝ)) * Real.log 2 - Delta_parity_odd n_a)| ≤
          |(padicValNat 2 ((m_a - 1) / 2) : ℝ) - (padicValNat 2 ((m_a + 1) / 2) : ℝ)| * Real.log 2 / 2 + |Delta_parity_odd n_a| / 2 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        have h_sub := abs_sub (((padicValNat 2 ((m_a + 1) / 2) : ℝ) - (padicValNat 2 ((m_a - 1) / 2) : ℝ)) * Real.log 2) (Delta_parity_odd n_a)
        rw [abs_mul, abs_of_nonneg (Real.log_nonneg (by norm_num)), abs_sub_comm] at h_sub
        linarith
      linarith
    constructor
    · rw [hM2_log, hθ_eq]
      have h_t : |theta_weight n_a m_a * (2 * S_odd n_a - (n₁ : ℝ) * Real.log (n₁ : ℝ))| ≤
          (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        rw [abs_mul, abs_of_nonneg hθ_01.1]
        exact le_trans (mul_le_of_le_one_left (abs_nonneg _) hθ_01.2) h_diff_S
      rw [abs_le] at h_t h_abs1 ⊢
      constructor <;> linarith
    · rw [hM1_log, hlog_B1_eq]
      have h_t : |(1 - theta_weight n_a m_a) * (2 * S_odd n_a - (n₁ : ℝ) * Real.log (n₁ : ℝ))| ≤
          (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        rw [abs_mul, abs_of_nonneg (by linarith [hθ_01.2])]
        exact le_trans (mul_le_of_le_one_left (abs_nonneg _) (by linarith [hθ_01.1])) h_diff_S
      rw [abs_le] at h_t h_abs2 ⊢
      constructor <;> linarith
  have h_fac_lb : (1 / 2 - ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) ≤
      (1 / 2 : ℝ) * Real.log (Nat.factorial n₁ : ℝ) - (6 * Real.log (P_ratio n₁ n₂ : ℝ) + 4) := by
    have hfac := n_log_n_sub_n_le_log_factorial n₁ (by omega)
    have h_il := hN_il n₁ (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h_il
    have hn1_le : (n₁ : ℝ) ≤ (ε / 256) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      have := (div_lt_iff₀ hlog_n₁_pos).mp h_il
      have hmin : min (ε / 256) (1 / 100) ≤ ε / 256 := min_le_left _ _
      nlinarith [show (0 : ℝ) ≤ n₁ by positivity]
    have h4_le : (4 : ℝ) ≤ (ε / 256) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by nlinarith [show (1 : ℝ) ≤ n₁ by exact_mod_cast (by omega : 1 ≤ n₁)]
    have hlogP_le : 6 * Real.log (P_ratio n₁ n₂ : ℝ) ≤ (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      have hP_le : (P_ratio n₁ n₂ : ℝ) ≤ (2 * (n₁ : ℝ)) ^ (n₂ - n₁) := by
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
        have hle_nat : ∏ j ∈ Finset.Ioc n₁ n₂, j ≤ (2 * n₁) ^ (n₂ - n₁) := by
          calc ∏ j ∈ Finset.Ioc n₁ n₂, j
              ≤ ∏ _j ∈ Finset.Ioc n₁ n₂, (2 * n₁) := Finset.prod_le_prod' (fun j hj => by
                have := (Finset.mem_Ioc.mp hj).2; omega)
            _ = (2 * n₁) ^ (Finset.Ioc n₁ n₂).card := Finset.prod_const _
            _ = (2 * n₁) ^ (n₂ - n₁) := by rw [Nat.card_Ioc]
        exact_mod_cast hle_nat
      have h1 : Real.log (P_ratio n₁ n₂ : ℝ) ≤ ((n₂ - n₁ : ℕ) : ℝ) * Real.log (2 * (n₁ : ℝ)) := by
        have h2 := Real.log_le_log (by exact_mod_cast (by have := P_ratio_ge_two (by omega : 4 ≤ n₁) hlt; omega : 0 < P_ratio n₁ n₂)) hP_le
        rwa [Real.log_pow] at h2
      have hlog2n : Real.log (2 * (n₁ : ℝ)) ≤ 2 * Real.log (n₁ : ℝ) := by
        rw [Real.log_mul (by norm_num) hn₁_pos.ne']
        have : Real.log 2 ≤ Real.log (n₁ : ℝ) := Real.log_le_log (by norm_num) (by linarith)
        linarith
      have h_gap_le : ((n₂ - n₁ : ℕ) : ℝ) ≤ (ε / 256) * (n₁ : ℝ) := by
        have h1' : (n₁ : ℝ) ^ α = (n₁ : ℝ) * (n₁ : ℝ) ^ (α - 1) := by
          rw [← Real.rpow_one_add' hn₁_pos.le (by linarith : 1 + (α - 1) ≠ 0)]; ring_nf
        have hmin : min (ε / 256) (1 / 4) ≤ ε / 256 := min_le_left _ _
        calc ((n₂ - n₁ : ℕ) : ℝ) ≤ (n₁ : ℝ) ^ α := h_gap
          _ = (n₁ : ℝ) * (n₁ : ℝ) ^ (α - 1) := h1'
          _ ≤ (n₁ : ℝ) * min (ε / 256) (1 / 4) := by gcongr; exact h_al.le
          _ ≤ (ε / 256) * (n₁ : ℝ) := by nlinarith
      calc 6 * Real.log (P_ratio n₁ n₂ : ℝ)
          ≤ 6 * (((ε / 256) * (n₁ : ℝ)) * (2 * Real.log (n₁ : ℝ))) := by gcongr
        _ = (12 * ε / 256) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
        _ ≤ (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by gcongr; norm_num
    linarith
  have hn1_log2 : (n₁ : ℝ) * Real.log 2 ≤ (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
    have h_il := hN_il n₁ (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h_il
    have h1 : Real.log 2 ≤ (ε / 16) * Real.log (n₁ : ℝ) := by
      have := (div_lt_iff₀ hlog_n₁_pos).mp h_il
      have hmin : min (ε / 256) (1 / 100) ≤ ε / 256 := min_le_left _ _
      linarith [Real.log_two_lt_d9]
    nlinarith [show (0 : ℝ) ≤ n₁ by positivity]
  have ⟨hX_pos, hY_pos, hZ_pos, hW_pos, _⟩ := prop_6_1_coprime_and_factorization (by omega) hlt hm₁ hm₂
  have hlogZW_lb : (1 / 2 - ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) ≤
      Real.log ((Z_gcd m₁ m₂ : ℝ) * W_gcd m₁ m₂) := by
    have := (abs_le.mp hZW_XY.1).1; linarith
  have hlogXY_lb : (1 / 2 - ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) ≤
      Real.log ((X_gcd m₁ m₂ : ℝ) * Y_gcd m₁ m₂) := by
    have := (abs_le.mp hZW_XY.2).1; linarith
  have hM1_rel := hlog_M_rel n₁ m₁ (by omega) hlt.le hm₁
  have hM2_rel := hlog_M_rel n₂ m₂ (by omega) (le_refl n₂) hm₂
  have h_log_ZW_22 := h_log_bound_from_M (Z_gcd m₁ m₂ * W_gcd m₁ m₂) M₂₁ M₂₂
    (mul_pos hZ_pos hW_pos) (by positivity) (by positivity) hdvd_ZW_22
  have h_log_ZW_11 := h_log_bound_from_M (Z_gcd m₁ m₂ * W_gcd m₁ m₂) M₁₁ M₁₂
    (mul_pos hZ_pos hW_pos) (by positivity) (by positivity) hdvd_ZW_11
  have h_log_XY_12 := h_log_bound_from_M (X_gcd m₁ m₂ * Y_gcd m₁ m₂) M₁₁ M₂₂
    (mul_pos hX_pos hY_pos) (by positivity) (by positivity) hdvd_XY_12
  have h_log_XY_21 := h_log_bound_from_M (X_gcd m₁ m₂ * Y_gcd m₁ m₂) M₂₁ M₁₂
    (mul_pos hX_pos hY_pos) (by positivity) (by positivity) hdvd_XY_21
  have hM21_ub := (abs_le.mp hM1_rel.1).2
  have hM11_ub := (abs_le.mp hM1_rel.2).2
  have hM22_ub := (abs_le.mp hM2_rel.1).2
  have hM12_ub := (abs_le.mp hM2_rel.2).2
  have hδ_le : δ ≤ ε / 16 := min_le_left _ _
  have hnlog_pos : 0 < (n₁ : ℝ) * Real.log (n₁ : ℝ) := by positivity
  have h1 : (1 - α) / 2 - ε ≤ theta_weight n₁ m₁ + theta_weight n₂ m₂ := by
    have hsum : ((1 - α) / 2 - ε) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) ≤
        (theta_weight n₁ m₁ + theta_weight n₂ m₂) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) := by
      push_cast at h_log_ZW_22; linarith
    exact le_of_mul_le_mul_right hsum hnlog_pos
  have h2 : theta_weight n₁ m₁ + theta_weight n₂ m₂ ≤ (3 + α) / 2 + ε := by
    have hsum : (theta_weight n₁ m₁ + theta_weight n₂ m₂) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) ≤
        ((3 + α) / 2 + ε) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) := by
      push_cast at h_log_ZW_11; linarith
    exact le_of_mul_le_mul_right hsum hnlog_pos
  have h3a : theta_weight n₂ m₂ - theta_weight n₁ m₁ ≤ (1 + α) / 2 + ε := by
    have hsum : (theta_weight n₂ m₂ - theta_weight n₁ m₁) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) ≤
        ((1 + α) / 2 + ε) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) := by
      push_cast at h_log_XY_12; linarith
    exact le_of_mul_le_mul_right hsum hnlog_pos
  have h3b : theta_weight n₁ m₁ - theta_weight n₂ m₂ ≤ (1 + α) / 2 + ε := by
    have hsum : (theta_weight n₁ m₁ - theta_weight n₂ m₂) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) ≤
        ((1 + α) / 2 + ε) * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) := by
      push_cast at h_log_XY_21; linarith
    exact le_of_mul_le_mul_right hsum hnlog_pos
  exact ⟨h1, h2, abs_le.mpr ⟨by linarith, h3b⟩⟩

/-- **Theorem 1.3(i) (Extreme Sparsity of the `k = 2` Regime, eq. 1.9)**:
For every `ε > 0`:
1. Any two `k = 2` solutions `n₁ < n₂` with `n₁` sufficiently large satisfy `n₂ - n₁ > n₁ ^ (1 - ε)`.
2. `#{1 ≤ n ≤ N : ∃ m, n! + 1 = m^2 ∧ k = 2} ≤ C_ε * N ^ ε` for all `N ≥ 1`. -/
theorem thm_1_3_part1_k2_gap_and_counting (ε : ℝ) (hε : 0 < ε) :
    (∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n₁ n₂ m₁ m₂ X₁ Y₁ X₂ Y₂ : ℕ, N₀ ≤ n₁ → n₁ < n₂ →
      Nat.factorial n₁ + 1 = m₁ ^ 2 → Nat.factorial n₂ + 1 = m₂ ^ 2 →
      IsFundamentalPell (q_n n₁) X₁ Y₁ → IsFundamentalPell (q_n n₂) X₂ Y₂ →
      (m₁ : ℝ) + (s_n n₁ : ℝ) * Real.sqrt (q_n n₁ : ℝ) = (pellUnit (q_n n₁) X₁ Y₁) ^ 2 →
      (m₂ : ℝ) + (s_n n₂ : ℝ) * Real.sqrt (q_n n₂ : ℝ) = (pellUnit (q_n n₂) X₂ Y₂) ^ 2 →
      (n₁ : ℝ) ^ (1 - ε) < (n₂ - n₁ : ℝ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N).filter (fun n => ∃ m X₁ Y₁ : ℕ,
        Nat.factorial n + 1 = m ^ 2 ∧ IsFundamentalPell (q_n n) X₁ Y₁ ∧
        (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2)).card : ℝ) ≤
      C * (N : ℝ) ^ ε) := by
  let ε' := min ε (1 / 2)
  have hε' : 0 < ε' := by positivity
  have hα0 : 0 ≤ 1 - ε' := by linarith [min_le_right ε (1 / 2 : ℝ)]
  have hα1 : 1 - ε' < 1 := by linarith
  obtain ⟨N₀, hN₀_ge, hCD⟩ := thm_6_4_capacity_diamond (1 - ε') hα0 hα1 (ε' / 4) (by positivity)
  have hgap : ∀ n₁ n₂ m₁ m₂ X₁ Y₁ X₂ Y₂ : ℕ, N₀ ≤ n₁ → n₁ < n₂ →
      Nat.factorial n₁ + 1 = m₁ ^ 2 → Nat.factorial n₂ + 1 = m₂ ^ 2 →
      IsFundamentalPell (q_n n₁) X₁ Y₁ → IsFundamentalPell (q_n n₂) X₂ Y₂ →
      (m₁ : ℝ) + (s_n n₁ : ℝ) * Real.sqrt (q_n n₁ : ℝ) = (pellUnit (q_n n₁) X₁ Y₁) ^ 2 →
      (m₂ : ℝ) + (s_n n₂ : ℝ) * Real.sqrt (q_n n₂ : ℝ) = (pellUnit (q_n n₂) X₂ Y₂) ^ 2 →
      (n₁ : ℝ) ^ (1 - ε) < (n₂ - n₁ : ℝ) := by
    intro n₁ n₂ m₁ m₂ X₁ Y₁ X₂ Y₂ hn₁ hlt hm₁ hm₂ hfund₁ hfund₂ hk₁ hk₂
    have h1 : (n₁ : ℝ) ^ (1 - ε') < (n₂ - n₁ : ℝ) := by
      by_contra hle; push Not at hle
      have hcd := (hCD n₁ n₂ m₁ m₂ hn₁ hlt hle hm₁ hm₂).1
      have hθ1 := theta_weight_eq_zero_of_k2 (by omega) (by omega) hm₁ hfund₁ hk₁
      have hθ2 := theta_weight_eq_zero_of_k2 (by omega) (by omega) hm₂ hfund₂ hk₂
      rw [hθ1, hθ2] at hcd
      linarith
    have hpow_le : (n₁ : ℝ) ^ (1 - ε) ≤ (n₁ : ℝ) ^ (1 - ε') :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n₁))
        (by linarith [min_le_left ε (1 / 2 : ℝ)])
    exact lt_of_le_of_lt hpow_le h1
  refine ⟨⟨N₀, by omega, hgap⟩, ?_⟩
  let P_k2 : ℕ → Prop := fun n => ∃ m X₁ Y₁ : ℕ,
    Nat.factorial n + 1 = m ^ 2 ∧ IsFundamentalPell (q_n n) X₁ Y₁ ∧
    (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2
  classical
  let ε₂ := min (ε / 2) (1 / 2)
  have hε₂ : 0 < ε₂ := by positivity
  obtain ⟨N₁, hN₁_ge, hCD₂⟩ := thm_6_4_capacity_diamond (1 - ε₂) (by linarith [min_le_right (ε / 2) (1 / 2 : ℝ)])
    (by linarith) (ε₂ / 4) (by positivity)
  have hgap₂ : ∀ n₁ n₂ : ℕ, N₁ ≤ n₁ → n₁ < n₂ → P_k2 n₁ → P_k2 n₂ →
      (n₁ : ℝ) ^ (1 - ε₂) < (n₂ - n₁ : ℝ) := by
    intro n₁ n₂ hn₁ hlt ⟨m₁, X₁, Y₁, hm₁, hfund₁, hk₁⟩ ⟨m₂, X₂, Y₂, hm₂, hfund₂, hk₂⟩
    by_contra hle; push Not at hle
    have hcd := (hCD₂ n₁ n₂ m₁ m₂ hn₁ hlt hle hm₁ hm₂).1
    have hθ1 := theta_weight_eq_zero_of_k2 (by omega) (by omega) hm₁ hfund₁ hk₁
    have hθ2 := theta_weight_eq_zero_of_k2 (by omega) (by omega) hm₂ hfund₂ hk₂
    rw [hθ1, hθ2] at hcd; linarith
  have h_spacing : ∀ (S : Finset ℕ) (a b : ℕ) (d : ℝ), 0 < d → a ≤ b →
      (∀ x ∈ S, a ≤ x ∧ x ≤ b) →
      (∀ x ∈ S, ∀ y ∈ S, x < y → d ≤ (y : ℝ) - (x : ℝ)) →
      (S.card : ℝ) ≤ ((b : ℝ) - (a : ℝ)) / d + 1 := by
    intro S a b d hd hab hSab hSgap
    by_cases hS1 : S.card ≤ 1
    · have : (S.card : ℝ) ≤ 1 := by exact_mod_cast hS1
      have : 0 ≤ ((b : ℝ) - (a : ℝ)) / d := div_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ (b : ℤ) - a)) hd.le
      linarith
    · push Not at hS1
      let f := S.orderEmbOfFin rfl
      have hf_mono : StrictMono f := f.strictMono
      have h_step : ∀ i : ℕ, (hi : i + 1 < S.card) →
          d ≤ (f ⟨i + 1, hi⟩ : ℝ) - (f ⟨i, by omega⟩ : ℝ) := by
        intro i hi
        exact hSgap _ (Finset.orderEmbOfFin_mem S rfl ⟨i, by omega⟩)
          _ (Finset.orderEmbOfFin_mem S rfl ⟨i + 1, hi⟩)
          (hf_mono (Fin.mk_lt_mk.mpr (by omega)))
      have h_sum_step : ((S.card - 1 : ℕ) : ℝ) * d ≤
          (f ⟨S.card - 1, by omega⟩ : ℝ) - (f ⟨0, by omega⟩ : ℝ) := by
        have hsum_eq : ∑ i ∈ Finset.range (S.card - 1),
            (if hi : i + 1 < S.card then ((f ⟨i + 1, hi⟩ : ℝ) - (f ⟨i, by omega⟩ : ℝ)) else 0) =
            (f ⟨S.card - 1, by omega⟩ : ℝ) - (f ⟨0, by omega⟩ : ℝ) := by
          have htel : ∀ k : ℕ, k ≤ S.card - 1 →
              ∑ i ∈ Finset.range k,
                (if hi : i + 1 < S.card then ((f ⟨i + 1, hi⟩ : ℝ) - (f ⟨i, by omega⟩ : ℝ)) else 0) =
              (f ⟨k, by omega⟩ : ℝ) - (f ⟨0, by omega⟩ : ℝ) := by
            intro k hk
            induction k with
            | zero => simp
            | succ m ih =>
              rw [Finset.sum_range_succ, ih (by omega), dif_pos (by omega)]
              ring
          exact htel (S.card - 1) (le_refl _)
        have hle_sum : ((S.card - 1 : ℕ) : ℝ) * d ≤
            ∑ i ∈ Finset.range (S.card - 1),
              (if hi : i + 1 < S.card then ((f ⟨i + 1, hi⟩ : ℝ) - (f ⟨i, by omega⟩ : ℝ)) else 0) := by
          calc ((S.card - 1 : ℕ) : ℝ) * d
              = ∑ _i ∈ Finset.range (S.card - 1), d := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            _ ≤ ∑ i ∈ Finset.range (S.card - 1), _ := by
                apply Finset.sum_le_sum; intro i hi
                rw [Finset.mem_range] at hi
                rw [dif_pos (by omega)]
                exact h_step i (by omega)
        linarith
      have h_first := hSab _ (Finset.orderEmbOfFin_mem S rfl ⟨0, by omega⟩)
      have h_last := hSab _ (Finset.orderEmbOfFin_mem S rfl ⟨S.card - 1, by omega⟩)
      have h_diff : (f ⟨S.card - 1, by omega⟩ : ℝ) - (f ⟨0, by omega⟩ : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
        linarith [show (a : ℝ) ≤ f ⟨0, by omega⟩ by exact_mod_cast h_first.1,
          show (f ⟨S.card - 1, by omega⟩ : ℝ) ≤ b by exact_mod_cast h_last.2]
      have h1 : ((S.card : ℝ) - 1) * d ≤ (b : ℝ) - (a : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ S.card)]; push_cast; ring
      linarith [(le_div_iff₀ hd).mpr h1]
  let C_cnt : ℝ := (N₁ : ℝ) + 4 * (2 : ℝ) ^ ε₂ / ((2 : ℝ) ^ ε₂ - 1)
  have h2e_gt : 1 < (2 : ℝ) ^ ε₂ := Real.one_lt_rpow (by norm_num) hε₂
  refine ⟨C_cnt, by positivity, fun N hN => ?_⟩
  let S_all := (Finset.Icc 1 N).filter P_k2
  let S_low := S_all.filter (fun n => n < N₁)
  let S_hi := S_all.filter (fun n => N₁ ≤ n)
  have hS_split : S_all.card ≤ S_low.card + S_hi.card := by
    have : S_all ⊆ S_low ∪ S_hi := by
      intro n hn; simp only [Finset.mem_union, Finset.mem_filter, S_low, S_hi]
      by_cases h : n < N₁; exact Or.inl ⟨hn, h⟩; exact Or.inr ⟨hn, le_of_not_gt h⟩
    exact le_trans (Finset.card_le_card this) (Finset.card_union_le _ _)
  have hS_low : (S_low.card : ℝ) ≤ (N₁ : ℝ) := by
    have hsub : S_low ⊆ Finset.Icc 1 N₁ := by
      intro n hn; simp only [S_low, S_all, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      exact ⟨hn.1.1.1, by omega⟩
    exact_mod_cast le_trans (Finset.card_le_card hsub) (by simp)
  have hS_hi : (S_hi.card : ℝ) ≤ (4 * (2 : ℝ) ^ ε₂ / ((2 : ℝ) ^ ε₂ - 1)) * (N : ℝ) ^ ε₂ := by
    let K := Nat.log 2 N
    have hsub_hi : S_hi ⊆ (Finset.range (K + 1)).biUnion
        (fun k => S_hi.filter (fun n => 2 ^ k ≤ n ∧ n ≤ 2 ^ (k + 1) - 1)) := by
      intro n hn
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      have hn_mem := Finset.mem_filter.mp hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn_mem.1).1).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn_mem.1).1).2
      refine ⟨Nat.log 2 n, Nat.lt_succ_of_le (Nat.log_mono_right hnN), hn, ?_, ?_⟩
      · exact Nat.pow_log_le_self 2 (by omega)
      · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n; omega
    have hcard_hi : S_hi.card ≤ ∑ k ∈ Finset.range (K + 1),
        (S_hi.filter (fun n => 2 ^ k ≤ n ∧ n ≤ 2 ^ (k + 1) - 1)).card :=
      le_trans (Finset.card_le_card hsub_hi) Finset.card_biUnion_le
    have hblk_card : ∀ k ∈ Finset.range (K + 1),
        ((S_hi.filter (fun n => 2 ^ k ≤ n ∧ n ≤ 2 ^ (k + 1) - 1)).card : ℝ) ≤
          2 * ((2 : ℝ) ^ ε₂) ^ k := by
      intro k _
      let B_k := S_hi.filter (fun n => 2 ^ k ≤ n ∧ n ≤ 2 ^ (k + 1) - 1)
      have h1 := h_spacing B_k (2 ^ k) (2 ^ (k + 1)) (((2 : ℝ) ^ k) ^ (1 - ε₂))
        (by positivity) (Nat.pow_le_pow_right (by norm_num) (by omega))
        (fun x hx => by
          simp only [B_k, Finset.mem_filter] at hx
          exact ⟨hx.2.1, by omega⟩)
        (fun x hx y hy hxy => by
          simp only [B_k, S_hi, S_all, Finset.mem_filter] at hx hy
          have hgap_xy := hgap₂ x y hx.1.2 hxy hx.1.1.2 hy.1.1.2
          have hpow_le : ((2 : ℝ) ^ k) ^ (1 - ε₂) ≤ (x : ℝ) ^ (1 - ε₂) :=
            Real.rpow_le_rpow (by positivity) (by exact_mod_cast hx.2.1) (by linarith [min_le_right (ε / 2) (1 / 2 : ℝ)])
          have hlt_r : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
          have : ((y - x : ℕ) : ℝ) = (y : ℝ) - (x : ℝ) := by exact_mod_cast (by omega : (y : ℤ) - x = ↑(y - x))
          linarith)
      have h_div_eq : (((2 ^ (k + 1) : ℕ) : ℝ) - ((2 ^ k : ℕ) : ℝ)) / ((2 : ℝ) ^ k) ^ (1 - ε₂) =
          ((2 : ℝ) ^ ε₂) ^ k := by
        have hsub : (((2 ^ (k + 1) : ℕ) : ℝ) - ((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k := by
          push_cast; rw [pow_succ]; ring
        rw [hsub]
        have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
        rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_sub (by norm_num), sub_sub_cancel,
          Real.rpow_mul (by norm_num), Real.rpow_natCast]
      have h1_le : (1 : ℝ) ≤ ((2 : ℝ) ^ ε₂) ^ k := one_le_pow₀ h2e_gt.le
      linarith
    have hsum_geom : ∑ k ∈ Finset.range (K + 1), (2 : ℝ) * ((2 : ℝ) ^ ε₂) ^ k =
        2 * (((2 : ℝ) ^ ε₂) ^ (K + 1) - 1) / ((2 : ℝ) ^ ε₂ - 1) := by
      rw [← Finset.mul_sum, geom_sum_eq h2e_gt.ne']; ring
    have hK_pow : ((2 : ℝ) ^ ε₂) ^ (K + 1) ≤ (2 : ℝ) ^ ε₂ * (N : ℝ) ^ ε₂ := by
      rw [pow_succ', ← Real.rpow_natCast ((2 : ℝ) ^ ε₂) K, ← Real.rpow_mul (by positivity),
        mul_comm ε₂ (K : ℝ), Real.rpow_mul (by positivity), Real.rpow_natCast]
      gcongr
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have hcard_hi_r : (S_hi.card : ℝ) ≤ ∑ k ∈ Finset.range (K + 1),
        ((S_hi.filter (fun n => 2 ^ k ≤ n ∧ n ≤ 2 ^ (k + 1) - 1)).card : ℝ) := by
      exact_mod_cast hcard_hi
    calc (S_hi.card : ℝ)
        ≤ ∑ k ∈ Finset.range (K + 1), 2 * ((2 : ℝ) ^ ε₂) ^ k := le_trans hcard_hi_r (Finset.sum_le_sum hblk_card)
      _ = 2 * (((2 : ℝ) ^ ε₂) ^ (K + 1) - 1) / ((2 : ℝ) ^ ε₂ - 1) := hsum_geom
      _ ≤ 2 * ((2 : ℝ) ^ ε₂ * (N : ℝ) ^ ε₂) / ((2 : ℝ) ^ ε₂ - 1) := by
          gcongr; linarith
      _ ≤ (4 * (2 : ℝ) ^ ε₂ / ((2 : ℝ) ^ ε₂ - 1)) * (N : ℝ) ^ ε₂ := by
          rw [div_mul_eq_mul_div]
          have h_num : 2 * ((2 : ℝ) ^ ε₂ * (N : ℝ) ^ ε₂) ≤ 4 * (2 : ℝ) ^ ε₂ * (N : ℝ) ^ ε₂ := by
            nlinarith [show 0 ≤ (2 : ℝ) ^ ε₂ * (N : ℝ) ^ ε₂ by positivity]
          gcongr
  have hN_pow : (N : ℝ) ^ ε₂ ≤ (N : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (le_trans (min_le_left _ _) (by linarith))
  have h1_le_N : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast hN) hε.le
  have hS_all_r : (S_all.card : ℝ) ≤ (S_low.card : ℝ) + (S_hi.card : ℝ) := by exact_mod_cast hS_split
  calc (S_all.card : ℝ) ≤ (N₁ : ℝ) + (4 * (2 : ℝ) ^ ε₂ / ((2 : ℝ) ^ ε₂ - 1)) * (N : ℝ) ^ ε := by
        nlinarith [show 0 ≤ 4 * (2 : ℝ) ^ ε₂ / ((2 : ℝ) ^ ε₂ - 1) by positivity]
    _ ≤ C_cnt * (N : ℝ) ^ ε := by dsimp [C_cnt]; nlinarith

/-- **Proposition 6.2(iii) (Consecutive-Squares `(k_{j^2}, k_{(j+1)^2}) ≠ (2, 2)` Exclusion)**:
For all sufficiently large `j`, `(k_{j^2}, k_{(j+1)^2}) ≠ (2, 2)`. -/
theorem prop_6_2_part3_consecutive_squares_k2_exclusion :
    ∃ J₀ : ℕ, 3 ≤ J₀ ∧ ∀ j m₁ m₂ X₁ Y₁ X₂ Y₂ : ℕ, J₀ ≤ j →
      Nat.factorial (j ^ 2) + 1 = m₁ ^ 2 →
      Nat.factorial ((j + 1) ^ 2) + 1 = m₂ ^ 2 →
      IsFundamentalPell (q_n (j ^ 2)) X₁ Y₁ →
      IsFundamentalPell (q_n ((j + 1) ^ 2)) X₂ Y₂ →
      ¬ ((m₁ : ℝ) + (s_n (j ^ 2) : ℝ) * Real.sqrt (q_n (j ^ 2) : ℝ) =
          (pellUnit (q_n (j ^ 2)) X₁ Y₁) ^ 2 ∧
         (m₂ : ℝ) + (s_n ((j + 1) ^ 2) : ℝ) * Real.sqrt (q_n ((j + 1) ^ 2) : ℝ) =
          (pellUnit (q_n ((j + 1) ^ 2)) X₂ Y₂) ^ 2) := by
  obtain ⟨N₀, _, hgap⟩ := (thm_1_3_part1_k2_gap_and_counting (1 / 4) (by norm_num)).1
  refine ⟨max N₀ 10, by omega, ?_⟩
  intro j m₁ m₂ X₁ Y₁ X₂ Y₂ hj hm₁ hm₂ hfund₁ hfund₂ ⟨hk₁, hk₂⟩
  have hn1 : N₀ ≤ j ^ 2 := by
    have hn0_j : N₀ ≤ j := le_trans (le_max_left _ _) hj
    have hj_sq : j ≤ j ^ 2 := Nat.le_self_pow (by norm_num) j
    omega
  have hlt : j ^ 2 < (j + 1) ^ 2 := by nlinarith
  have h1 := hgap (j ^ 2) ((j + 1) ^ 2) m₁ m₂ X₁ Y₁ X₂ Y₂ hn1 hlt hm₁ hm₂ hfund₁ hfund₂ hk₁ hk₂
  have hdiff : ((j + 1 : ℝ) ^ 2 - (j : ℝ) ^ 2) = 2 * (j : ℝ) + 1 := by ring
  have hpow : ((j : ℝ) ^ (3 / 2 : ℝ)) ≤ ((j ^ 2 : ℕ) : ℝ) ^ (1 - 1 / 4 : ℝ) := by
    have hj_nn : (0 : ℝ) ≤ j := by positivity
    push_cast
    rw [show (j : ℝ) ^ 2 = (j : ℝ) ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hj_nn]
    norm_num
  have h32 : 2 * (j : ℝ) + 1 ≤ (j : ℝ) ^ (3 / 2 : ℝ) := by
    have hj10 : (10 : ℝ) ≤ j := by exact_mod_cast (by omega : 10 ≤ j)
    have hsq : (2 * (j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) ^ (3 / 2 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast ((j : ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul (by positivity)]
      norm_num; nlinarith
    nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ j) (3 / 2)]
  rw [Nat.cast_sub (by nlinarith : j ^ 2 ≤ (j + 1) ^ 2)] at h1
  push_cast at h1; linarith

/-- **Theorem 6.4(b) (Polarization Concentration via Rankin Spherical Cap Cauchy–Schwarz)**:
For any `ε ∈ (0, 1/4)` and `η ∈ (0, 1/2]`, there exists `N₀` such that for all `N' ≥ N₀`,
any interval `[N', N' + ⌊(N')^{1-ε}⌋]` contains at most `⌊(η^2 * ε)⁻¹⌋ + 1` solutions `n` with
`|θ_ε(n) - 1/2| ≥ η`, and `#{4 ≤ n ≤ N : ∃ m, n! + 1 = m^2 ∧ |θ_ε(n) - 1/2| ≥ η} ≤ C_ε * η^{-2} * N^ε`. -/
private def PolBad (ε η : ℝ) (n : ℕ) : Prop :=
  ∃ m : ℕ, Nat.factorial n + 1 = m ^ 2 ∧ |theta_eps_weight ε n m - 1 / 2| ≥ η

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
        refine ⟨⟨⟨by omega, hpN⟩, hp_pr, hp_gt, by exact_mod_cast hpN, ?_⟩⟩
        rw [Nat.ModEq, Nat.mod_two_of_bodd]; omega
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
        have : |(0 : ℝ) - 1 / 2| = 1 / 2 := by norm_num
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
            refine ⟨⟨⟨by omega, hpn⟩, hp_pr, hp_gt, by exact_mod_cast hpn, ?_⟩⟩
            rw [Nat.ModEq, Nat.mod_two_of_bodd]; omega
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
        have hsub_part : P_I_n.filter (fun p => p ∣ B_part n ((m + 1) / 2)) ⊆ P_I_n := Finset.filter_subset _ _
        have h_u_eq : ∀ p ∈ P_I_n, u n hn p =
            if p ∣ B_part n ((m + 1) / 2) then (1 : ℝ) else -1 := by
          intro p hp
          have hp_mem := Finset.mem_filter.mp hp
          have hp_pr := hp_mem.1.2
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
              have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp_pr hq_mem.1.1.2).mp (hp_pr.dvd_of_dvd_pow hqd)
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
              have hp_pr := (Finset.mem_filter.mp h1).1.2
              haveI : Fact p.Prime := ⟨hp_pr⟩
              exact (Nat.factorization_le_iff_dvd (Nat.factorial_pos N').ne' (Nat.factorial_pos n).ne').mpr
                (Nat.factorial_dvd_factorial hn_mem.1) p
            have hdiff_r : (padicValNat p (Nat.factorial n) : ℝ) - (padicValNat p (Nat.factorial N') : ℝ) =
                ((padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N') : ℕ) : ℝ) := by
              exact_mod_cast (by omega : (padicValNat p (Nat.factorial n) : ℤ) - padicValNat p (Nat.factorial N') =
                ↑(padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N')))
            have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp h1).1.2.pos)
            calc |((padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) * u n hn p) -
                  ((padicValNat p (Nat.factorial N') : ℝ) * Real.log (p : ℝ) * u n hn p)|
                = |((padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N') : ℕ) : ℝ) * Real.log (p : ℝ)| * |u n hn p| := by
                  rw [← hdiff_r, abs_mul]; congr 1; ring_nf
              _ = ((padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N') : ℕ) : ℝ) * Real.log (p : ℝ) := by
                  rw [hu1, mul_one, abs_of_nonneg (by positivity)]
          · rw [if_neg (by tauto), if_pos h1, if_neg h2, sub_zero, abs_mul,
              show |u n hn p| = 1 by dsimp [u]; split_ifs <;> norm_num, mul_one,
              abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp h1).1.2.pos)))]
          · rw [if_neg (by tauto), if_neg h1, if_pos h2, zero_sub, abs_neg, abs_mul,
              show |u n hn p| = 1 by dsimp [u]; split_ifs <;> norm_num, mul_one,
              abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp h2).1.2.pos)))]
            have hp_pr := (Finset.mem_filter.mp h2).1.2
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
              have hp_pr := (Finset.mem_filter.mp hp_m.2.2).1.2
              haveI : Fact p.Prime := ⟨hp_pr⟩
              have hP_pos : 0 < Nat.factorial n / Nat.factorial N' := Nat.div_pos (Nat.factorial_le hn_mem.1) (Nat.factorial_pos N')
              have hv_eq : padicValNat p (Nat.factorial n / Nat.factorial N') =
                  padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N') := by
                have hmul := Nat.div_mul_cancel (Nat.factorial_dvd_factorial hn_mem.1)
                have hv := congrArg (padicValNat p) hmul
                rw [padicValNat.mul hP_pos.ne' (Nat.factorial_pos N').ne'] at hv; omega
              rw [← hv_eq]; exact pow_padicValNat_dvd
            · intro p hp q hq hpq
              exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Finset.mem_filter.mp (Finset.mem_filter.mp hp).2.2).1.2
                (Finset.mem_filter.mp (Finset.mem_filter.mp hq).2.2).1.2).mpr hpq)
          have hpos_U1 : 0 < ∏ p ∈ U1, p ^ (padicValNat p (Nat.factorial n) - padicValNat p (Nat.factorial N')) :=
            Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp (Finset.mem_filter.mp hp).2.2).1.2.pos _)
          have hP_pos : 0 < Nat.factorial n / Nat.factorial N' := Nat.div_pos (Nat.factorial_le hn_mem.1) (Nat.factorial_pos N')
          have hlog_U1 := Real.log_le_log (by exact_mod_cast hpos_U1) (by exact_mod_cast Nat.le_of_dvd hP_pos hdvd_U1)
          rw [Nat.cast_prod, Real.log_prod _ _ (fun p hp => pow_ne_zero _ (by
            exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).2.2).1.2.ne_zero))] at hlog_U1
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
            rcases hp with h | h <;> exact (Finset.mem_filter.mp h).1.2
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
                rcases hp_m.1 with h | h <;> exact_mod_cast (Finset.mem_filter.mp h).1.2.pos)
                (le_trans (by exact_mod_cast hp_le_n) hn_le_2N')
            exact mul_le_mul (hv_ub_U p hp_m.1) hlog_le (Real.log_nonneg (by
              simp only [U_union, Finset.mem_union] at hp_m
              rcases hp_m.1 with h | h <;> exact_mod_cast (Finset.mem_filter.mp h).1.2.pos)) (by positivity)
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
                rcases hp_m.1 with h | h <;> exact (Finset.mem_filter.mp h).1.2
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
                rw [← hv0]; exact hp_mem.1.2.2
              · have hp_mem := Finset.mem_filter.mp hp_I
                have hp_le_n : p ≤ n := le_trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hp_mem.1).1).2 hn_mem.1
                refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hp_le_n⟩, hp_pr, ?_⟩,
                  hp_mem.2.1, hp_gt⟩, hp_I⟩
                rw [hv0]; exact hp_mem.1.2.2
            · intro p hp q hq hpq
              have hp_m := Finset.mem_filter.mp hp; have hq_m := Finset.mem_filter.mp hq
              have hp_pr : p.Prime := by
                simp only [U_union, Finset.mem_union] at hp_m
                rcases hp_m.1 with h | h <;> exact (Finset.mem_filter.mp h).1.2
              have hq_pr : q.Prime := by
                simp only [U_union, Finset.mem_union] at hq_m
                rcases hq_m.1 with h | h <;> exact (Finset.mem_filter.mp h).1.2
              exact (Nat.coprime_primes hp_pr hq_pr).mpr hpq
          have hpos_U3 : 0 < ∏ p ∈ U3, p := Finset.prod_pos (fun p hp => by
            have hp_m := Finset.mem_filter.mp hp
            simp only [U_union, Finset.mem_union] at hp_m
            rcases hp_m.1 with h | h <;> exact (Finset.mem_filter.mp h).1.2.pos)
          have hP_pos : 0 < Nat.factorial n / Nat.factorial N' := Nat.div_pos (Nat.factorial_le hn_mem.1) (Nat.factorial_pos N')
          have hlog_U3 := Real.log_le_log (by exact_mod_cast hpos_U3) (by exact_mod_cast Nat.le_of_dvd hP_pos hdvd_U3)
          rw [Nat.cast_prod, Real.log_prod _ _ (fun p hp => by
            have hp_m := Finset.mem_filter.mp hp
            simp only [U_union, Finset.mem_union] at hp_m
            rcases hp_m.1 with h | h <;> exact_mod_cast (Finset.mem_filter.mp h).1.2.ne_zero)] at hlog_U3
          have hsum_U3_le : ∑ p ∈ U3, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
              4 * (N' : ℝ) ^ (ε / 2) * ∑ p ∈ U3, Real.log (p : ℝ) := by
            rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro p hp
            have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
              have hp_m := Finset.mem_filter.mp hp
              simp only [U_union, Finset.mem_union] at hp_m
              rcases hp_m.1 with h | h <;> exact_mod_cast (Finset.mem_filter.mp h).1.2.pos)
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
            refine ⟨⟨⟨by omega, hpn⟩, hp_pr, hp_gt, by exact_mod_cast hpn, ?_⟩⟩
            rw [Nat.ModEq, Nat.mod_two_of_bodd]; omega
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
      · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n; omega
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
                  rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_sub (by norm_num), sub_sub_cancel,
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
