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
    have hB_dvd_prod : B_part n ((m + 1) / 2) ∣
        ∏ p ∈ (Podd n).filter (fun p => 3 ≤ p), p ^ padicValNat p (Nat.factorial n) := by
      unfold B_part
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩
    have hpos_prod : 0 < ∏ p ∈ (Podd n).filter (fun p => 3 ≤ p), p ^ padicValNat p (Nat.factorial n) := by
      apply Finset.prod_pos; intro p hp
      simp only [Podd, Finset.mem_filter, Finset.mem_Icc] at hp
      exact pow_pos (by omega : 0 < p) _
    have hle_prod := Real.log_le_log
      (by exact_mod_cast B_part_pos n ((m + 1) / 2) : (0 : ℝ) < (B_part n ((m + 1) / 2) : ℝ))
      (by exact_mod_cast Nat.le_of_dvd hpos_prod hB_dvd_prod :
        (B_part n ((m + 1) / 2) : ℝ) ≤ ((∏ p ∈ (Podd n).filter (fun p => 3 ≤ p), p ^ padicValNat p (Nat.factorial n) : ℕ) : ℝ))
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
    simp only [Podd, Finset.mem_filter, Finset.mem_Icc] at hp
    have hp_pr := hp.1.1.2.1
    have hp_odd : ¬ 2 ∣ padicValNat p (Nat.factorial n) := hp.1.1.2.2
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
      have : (m₁ : ℝ) ^ 2 = (Nat.factorial n₁ : ℝ) + 1 := by exact_mod_cast hm₁.symm
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
        nlinarith only [hfac, hm1r, hm2r]
      have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
      linarith only [h1, hP1]
    nlinarith only [hsq, Real.sqrt_nonneg (P : ℝ), show (0 : ℝ) ≤ m₁ by positivity, show (0 : ℝ) ≤ m₂ by positivity]
  have hfac24 : 24 ≤ Nat.factorial n₁ := by
    calc 24 = Nat.factorial 4 := by norm_num [Nat.factorial]
      _ ≤ Nat.factorial n₁ := Nat.factorial_le hn₁
  have hsqrt_ge4 : 4 ≤ Real.sqrt (Nat.factorial n₁ : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 16 ≤ Nat.factorial n₁))
  have hsqrtP_le' : Real.sqrt (P : ℝ) ≤ (18 / 25 : ℝ) * (P : ℝ) := by
    have hsq : Real.sqrt (P : ℝ) ^ 2 ≤ ((18 / 25 : ℝ) * (P : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
      have hP2 : (2 : ℝ) ≤ P := by exact_mod_cast hP_ge
      nlinarith only [hP2]
    nlinarith only [hsq, Real.sqrt_nonneg (P : ℝ), show (0 : ℝ) ≤ P by positivity]
  have h_lo' : (1 / 20 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) ≤
      (P : ℝ) * m₁ - m₂ - ((P : ℝ) - 1) := by
    have h1 : (P : ℝ) * m₁ - m₂ ≥ (7 / 25 : ℝ) * (P : ℝ) * (m₁ : ℝ) := by
      have : (m₂ : ℝ) ≤ (18 / 25 : ℝ) * (P : ℝ) * (m₁ : ℝ) := by
        nlinarith only [hm2_le, hsqrtP_le', show (0 : ℝ) ≤ m₁ by positivity]
      linarith only [this]
    have h2 : (P : ℝ) - 1 ≤ (23 / 100 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
      have hsq : (1 : ℝ) ^ 2 ≤ ((23 / 100 : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have : (24 : ℝ) ≤ Nat.factorial n₁ := by exact_mod_cast hfac24
        linarith only [this]
      have h1le : 1 ≤ (23 / 100 : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
        nlinarith only [hsq, Real.sqrt_nonneg (Nat.factorial n₁ : ℝ)]
      nlinarith only [h1le, show (0 : ℝ) ≤ P by positivity]
    nlinarith only [h1, h2, hm1_gt, show (0 : ℝ) ≤ P by positivity]
  have h_hi' : (P : ℝ) * m₁ + m₂ + ((P : ℝ) - 1) ≤
      5 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
    have h1 : (m₂ : ℝ) ≤ 2 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
      nlinarith only [hm2_le, hsqrtP_le', hm1_le, show (0 : ℝ) ≤ P by positivity, Real.sqrt_nonneg (Nat.factorial n₁ : ℝ)]
    have h2 : (P : ℝ) - 1 ≤ (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
      nlinarith only [hsqrt_ge4, show (0 : ℝ) ≤ P by positivity]
    nlinarith only [h1, h2, hm1_le, show (0 : ℝ) ≤ P by positivity]
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
  suffices h_aux : ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 →
      ∃ N₀ : ℕ, 25 ≤ N₀ ∧ ∀ n₁ n₂ m₁ m₂ : ℕ, N₀ ≤ n₁ → n₁ < n₂ →
        (n₂ - n₁ : ℝ) ≤ (n₁ : ℝ) ^ α →
        Nat.factorial n₁ + 1 = m₁ ^ 2 → Nat.factorial n₂ + 1 = m₂ ^ 2 →
        (1 - α) / 2 - ε' ≤ theta_weight n₁ m₁ + theta_weight n₂ m₂ ∧
        theta_weight n₁ m₁ + theta_weight n₂ m₂ ≤ (3 + α) / 2 + ε' ∧
        |theta_weight n₁ m₁ - theta_weight n₂ m₂| ≤ (1 + α) / 2 + ε' by
    obtain ⟨N₀, hN₀, hCD⟩ := h_aux (min ε 1) (by positivity) (min_le_right _ _)
    refine ⟨N₀, hN₀, fun n₁ n₂ m₁ m₂ hn₁ hlt hgap hm₁ hm₂ => ?_⟩
    have h1 := hCD n₁ n₂ m₁ m₂ hn₁ hlt hgap hm₁ hm₂
    have hmin : min ε 1 ≤ ε := min_le_left _ _
    exact ⟨by linarith, by linarith, by linarith⟩
  clear ε hε
  intro ε hε hε_le1
  let δ := min (ε / 16) (1 / 8)
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 4 := by linarith [min_le_right (ε / 16) (1 / 8 : ℝ)]
  obtain ⟨N_flip, hN_flip_ge, h_flip⟩ := lem_6_3_parity_flip_uniform δ hδ0 hδ1 (ε / 16) (by positivity)
  obtain ⟨C_cs, hC_cs, N_cs, hN_cs_ge, h_cs⟩ := thm_5_2_part1_cross_symmetry
  obtain ⟨N_sodd, hN_sodd⟩ := Filter.eventually_atTop.mp
    (Asymptotics.IsLittleO.bound S_odd_asymptotic (show (0 : ℝ) < min (ε / 256) (1 / 8) by positivity))
  obtain ⟨N_dp, hN_dp⟩ := Filter.eventually_atTop.mp
    (Asymptotics.IsLittleO.bound Delta_parity_isLittleO_mul_log (show (0 : ℝ) < ε / 256 by positivity))
  have h_alpha_div : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (α - 1)) Filter.atTop (nhds 0) := by
    have h1 := tendsto_rpow_neg_atTop (show 0 < 1 - α by linarith) |>.comp tendsto_natCast_atTop_atTop
    refine h1.congr (fun n => ?_)
    dsimp; ring_nf
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
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n₁) _)] at h_al
  have hh_lt_n1 : n₂ - n₁ < n₁ := by
    have h1 : (n₁ : ℝ) ^ α = (n₁ : ℝ) * (n₁ : ℝ) ^ (α - 1) := by
      rw [show α = 1 + (α - 1) by ring, Real.rpow_add hn₁_pos, Real.rpow_one]
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
        have h_gap' : ((n₂ - n₁ : ℕ) : ℝ) ≤ (n₁ : ℝ) ^ α := by
          rw [Nat.cast_sub hlt.le]; exact h_gap
        have := Real.log_le_log (by exact_mod_cast (by omega : 0 < n₂ - n₁)) h_gap'
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
        have hv_le : padicValNat 2 T ≤ padicValNat 2 (Nat.factorial n₁) := by
          rw [← Nat.factorization_def T Nat.prime_two, ← Nat.factorization_def (Nat.factorial n₁) Nat.prime_two]
          exact (Nat.factorization_le_iff_dvd hT_pos.ne' (Nat.factorial_pos n₁).ne').mpr hT_fac 2
        calc padicValNat 2 T ≤ padicValNat 2 (Nat.factorial n₁) := hv_le
          _ = padicValNat 2 (2 ^ padicValNat 2 (Nat.factorial n₁)) := by
              rw [padicValNat.prime_pow]
          _ ≤ padicValNat 2 (2 ^ padicValNat 2 (Nat.factorial n₁) * (M₁ * M₂) * FlipProd) := by
              rw [padicValNat.mul (mul_pos (by positivity) (mul_pos hM₁ hM₂)).ne' hFlip_pos.ne',
                  padicValNat.mul (by positivity) (mul_pos hM₁ hM₂).ne']
              omega
      · have hp3 : 3 ≤ p := by have := hp_pr.two_le; omega
        by_cases hpT : p ∣ T
        · by_cases hp_flip : 2 ∣ padicValNat p (P_ratio n₁ n₂)
          · have h1 := hT_odd p hp_pr hp3 hp_flip hpT
            calc padicValNat p T ≤ padicValNat p (M₁ * M₂) := h1
              _ ≤ padicValNat p (2 ^ padicValNat 2 (Nat.factorial n₁) * (M₁ * M₂) * FlipProd) := by
                  rw [padicValNat.mul (mul_pos (by positivity) (mul_pos hM₁ hM₂)).ne' hFlip_pos.ne',
                      padicValNat.mul (by positivity) (mul_pos hM₁ hM₂).ne']
                  omega
          · have hp_le_n1 : p ≤ n₁ := by
              have hp_fac : p ∣ Nat.factorial n₁ := dvd_trans hpT hT_fac
              exact hp_pr.dvd_factorial.mp hp_fac
            have hp_mem : p ∈ (Finset.Icc 3 n₁).filter (fun p => p.Prime ∧ ¬ 2 ∣ padicValNat p (P_ratio n₁ n₂)) :=
              Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, hp_le_n1⟩, hp_pr, hp_flip⟩
            have hpow_dvd : p ^ padicValNat p (Nat.factorial n₁) ∣ FlipProd :=
              Finset.dvd_prod_of_mem _ hp_mem
            have hv_le1 : padicValNat p T ≤ padicValNat p (Nat.factorial n₁) := by
              rw [← Nat.factorization_def T hp_pr, ← Nat.factorization_def (Nat.factorial n₁) hp_pr]
              exact (Nat.factorization_le_iff_dvd hT_pos.ne' (Nat.factorial_pos n₁).ne').mpr hT_fac p
            have hv_le2 : padicValNat p (Nat.factorial n₁) ≤ padicValNat p FlipProd := by
              have h1 := (Nat.factorization_le_iff_dvd (pow_pos hp_pr.pos _).ne' hFlip_pos.ne').mpr hpow_dvd p
              simpa [Nat.factorization_def _ hp_pr, padicValNat.prime_pow] using h1
            calc padicValNat p T ≤ padicValNat p FlipProd := le_trans hv_le1 hv_le2
              _ ≤ padicValNat p (2 ^ padicValNat 2 (Nat.factorial n₁) * (M₁ * M₂) * FlipProd) := by
                  rw [padicValNat.mul (mul_pos (by positivity) (mul_pos hM₁ hM₂)).ne' hFlip_pos.ne']
                  omega
        · rw [padicValNat.eq_zero_of_not_dvd hpT]; exact Nat.zero_le _
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp_pr]
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
      have hu_pos : 0 < u := by
        have hpos : 0 < 4 * u * v := h4uv.symm ▸ Nat.factorial_pos n_a
        exact Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
      have hv_pos : 0 < v := by
        have hpos : 0 < 4 * u * v := h4uv.symm ▸ Nat.factorial_pos n_a
        exact Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
      have hvp : padicValNat p (Nat.factorial n_a) = padicValNat p u := by
        rw [← h4uv, mul_assoc, padicValNat.mul (by norm_num) (mul_pos hu_pos hv_pos).ne',
          padicValNat.eq_zero_of_not_dvd (fun h => hp_pr.not_dvd_one (hcop4 ▸ Nat.dvd_gcd (dvd_refl p) h)),
          zero_add, padicValNat.mul hu_pos.ne' hv_pos.ne',
          padicValNat.eq_zero_of_not_dvd hp_nv, add_zero]
      rw [hvp, ← hdec]
      have h2p : u = 2 ^ padicValNat 2 u * oddPartNat u := by
        unfold oddPartNat; exact (Nat.ordProj_mul_ordCompl_eq_self u 2).symm
      conv_lhs => rw [h2p]
      rw [padicValNat.mul (by positivity) (oddPartNat_pos u).ne',
        padicValNat.eq_zero_of_not_dvd (fun h => hp_pr.not_dvd_one (hcop4 ▸ Nat.dvd_gcd (hp_pr.dvd_of_dvd_pow h) (by norm_num))),
        zero_add]
    have hp_nZ : ∀ u_val : ℕ, p ∈ Podd n_a → ¬ p ∣ Z_star n_a u_val := by
      intro u_val hp_odd hpZ
      unfold Z_star at hpZ
      rw [hp_pr.prime.dvd_finset_prod_iff] at hpZ
      obtain ⟨q, hq, hqd⟩ := hpZ
      simp only [Peven, Finset.mem_filter, Finset.mem_Icc] at hq
      have hq_pr := hq.1.1.2.1
      have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp (hp_pr.dvd_of_dvd_pow hqd)
      subst hpq
      simp only [Podd, Finset.mem_filter] at hp_odd
      exact hp_odd.2 hq.1.1.2.2
    have hp_nB : ∀ u_val : ℕ, ¬ p ∈ Podd n_a → ¬ p ∣ B_part n_a u_val := by
      intro u_val hp_even hpB
      unfold B_part at hpB
      rw [hp_pr.prime.dvd_finset_prod_iff] at hpB
      obtain ⟨q, hq, hqd⟩ := hpB
      simp only [Podd, Finset.mem_filter, Finset.mem_Icc] at hq
      have hq_pr := hq.1.1.2.1
      have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp_pr hq_pr).mp (hp_pr.dvd_of_dvd_pow hqd)
      subst hpq
      exact hp_even (Finset.mem_filter.mpr ⟨hq.1.1.1, hq_pr, hq.1.1.2.2⟩)
    constructor
    · intro hp_u1
      have hval := h_eq_u ((m_a - 1) / 2) ((m_a + 1) / 2) h4mul hcop hdec1 hp_u1
      constructor
      · intro hp_odd
        rw [hval, padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne'),
          padicValNat.eq_zero_of_not_dvd (fun h => hp_nZ _ hp_odd (hp_pr.dvd_of_dvd_pow h)), add_zero]
      · intro hp_even
        rw [hval, padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne'),
          padicValNat.eq_zero_of_not_dvd (hp_nB _ hp_even), zero_add]
    · intro hp_u2
      have hval := h_eq_u ((m_a + 1) / 2) ((m_a - 1) / 2) (by linarith) hcop.symm hdec2 hp_u2
      constructor
      · intro hp_odd
        rw [hval, padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne'),
          padicValNat.eq_zero_of_not_dvd (fun h => hp_nZ _ hp_odd (hp_pr.dvd_of_dvd_pow h)), add_zero]
      · intro hp_even
        rw [hval, padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne'),
          padicValNat.eq_zero_of_not_dvd (hp_nB _ hp_even), zero_add]
  have hPodd_iff : ∀ p : ℕ, p.Prime → 3 ≤ p → 2 ∣ padicValNat p (P_ratio n₁ n₂) →
      (p ∈ Podd n₁ ↔ p ∈ Podd n₂) := by
    intro p hp_pr _ h2dvd
    have hmul := P_ratio_mul_factorial hlt
    have hP_pos : 0 < P_ratio n₁ n₂ := by
      by_contra h0; have : P_ratio n₁ n₂ = 0 := by omega
      rw [this, zero_mul] at hmul; exact (Nat.factorial_pos n₂).ne' hmul.symm
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have hv_eq : padicValNat p (Nat.factorial n₂) =
        padicValNat p (P_ratio n₁ n₂) + padicValNat p (Nat.factorial n₁) := by
      have := congrArg (padicValNat p) hmul
      rw [padicValNat.mul hP_pos.ne' (Nat.factorial_pos n₁).ne'] at this; exact this.symm
    simp only [Podd, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp_le, _⟩, hp_odd⟩
      refine ⟨⟨le_trans hp_le hlt.le, hp_pr⟩, ?_⟩
      omega
    · rintro ⟨⟨_, _⟩, hp_odd⟩
      have hfac_n1 : padicValNat p (Nat.factorial n₁) ≠ 0 := by
        intro h0; rw [h0, add_zero] at hv_eq
        exact hp_odd (hv_eq ▸ h2dvd)
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
    have hle := Real.log_le_log
      (by exact_mod_cast hT : (0 : ℝ) < (T : ℝ))
      (by exact_mod_cast Nat.le_of_dvd (by positivity) hdvd : (T : ℝ) ≤ ((2 ^ padicValNat 2 (Nat.factorial n₁) * (Ma * Mb) * FlipProd : ℕ) : ℝ))
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
    have hv_le_n1 : padicValNat p (Z_gcd m₁ m₂ * W_gcd m₁ m₂) ≤ padicValNat p (Nat.factorial n₁) := by
      rw [← Nat.factorization_def _ hp_pr, ← Nat.factorization_def _ hp_pr]
      exact (Nat.factorization_le_iff_dvd (by
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
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
      · have hp_u11 : p ∣ u₁₁ := dvd_trans hpZ (Nat.gcd_dvd_left _ _)
        have hZ11 := (h1.1 hp_u11).2 hp_odd
        have hle_M21 : padicValNat p (Z_star n₁ u₁₁ ^ 2) ≤ padicValNat p M₂₁ := by
          dsimp [M₂₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₁ ≤ padicValNat p (M₂₁ * M₂₂) := by
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
    · by_cases hp_odd : p ∈ Podd n₁
      · have hp_u21 : p ∣ u₂₁ := dvd_trans hpW (Nat.gcd_dvd_left _ _)
        have hB21 := (h1.2 hp_u21).1 hp_odd
        have hle_M21 : padicValNat p (B_part n₁ u₂₁) ≤ padicValNat p M₂₁ := by
          dsimp [M₂₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₁ ≤ padicValNat p (M₂₁ * M₂₂) := by
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
      · have hp_even2 : ¬ p ∈ Podd n₂ := fun h => hp_odd ((hPodd_iff p hp_pr hp3 h2dvd).mpr h)
        have hp_u12 : p ∣ u₁₂ := dvd_trans hpW (Nat.gcd_dvd_right _ _)
        have hZ12 := (h2.1 hp_u12).2 hp_even2
        have hle_M22 : padicValNat p (Z_star n₂ u₁₂ ^ 2) ≤ padicValNat p M₂₂ := by
          dsimp [M₂₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₂ ≤ padicValNat p (M₂₁ * M₂₂) := by
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
  have hdvd_ZW_11 : Z_gcd m₁ m₂ * W_gcd m₁ m₂ ∣
      2 ^ padicValNat 2 (Nat.factorial n₁) * (M₁₁ * M₁₂) * FlipProd := by
    refine hdvd_universal _ M₁₁ M₁₂ (by positivity) (by positivity) hZW_dvd_fac ?_
    intro p hp_pr hp3 h2dvd hpZW
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have hv_le_n1 : padicValNat p (Z_gcd m₁ m₂ * W_gcd m₁ m₂) ≤ padicValNat p (Nat.factorial n₁) := by
      rw [← Nat.factorization_def _ hp_pr, ← Nat.factorization_def _ hp_pr]
      exact (Nat.factorization_le_iff_dvd (by
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
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
      · have hp_even2 : ¬ p ∈ Podd n₂ := fun h => hp_odd ((hPodd_iff p hp_pr hp3 h2dvd).mpr h)
        have hp_u22 : p ∣ u₂₂ := dvd_trans hpZ (Nat.gcd_dvd_right _ _)
        have hZ22 := (h2.2 hp_u22).2 hp_even2
        have hle_M12 : padicValNat p (Z_star n₂ u₂₂ ^ 2) ≤ padicValNat p M₁₂ := by
          dsimp [M₁₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₁₂ ≤ padicValNat p (M₁₁ * M₁₂) := by
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
    · by_cases hp_odd : p ∈ Podd n₁
      · have hp_odd2 := (hPodd_iff p hp_pr hp3 h2dvd).mp hp_odd
        have hp_u12 : p ∣ u₁₂ := dvd_trans hpW (Nat.gcd_dvd_right _ _)
        have hB12 := (h2.1 hp_u12).1 hp_odd2
        have hle_M12 : padicValNat p (B_part n₂ u₁₂) ≤ padicValNat p M₁₂ := by
          dsimp [M₁₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₁₂ ≤ padicValNat p (M₁₁ * M₁₂) := by
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
      · have hp_u21 : p ∣ u₂₁ := dvd_trans hpW (Nat.gcd_dvd_left _ _)
        have hZ21 := (h1.2 hp_u21).2 hp_odd
        have hle_M11 : padicValNat p (Z_star n₁ u₂₁ ^ 2) ≤ padicValNat p M₁₁ := by
          dsimp [M₁₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₁₁ ≤ padicValNat p (M₁₁ * M₁₂) := by
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
  have hdvd_XY_12 : X_gcd m₁ m₂ * Y_gcd m₁ m₂ ∣
      2 ^ padicValNat 2 (Nat.factorial n₁) * (M₁₁ * M₂₂) * FlipProd := by
    refine hdvd_universal _ M₁₁ M₂₂ (by positivity) (by positivity) hXY_dvd_fac ?_
    intro p hp_pr hp3 h2dvd hpXY
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have hv_le_n1 : padicValNat p (X_gcd m₁ m₂ * Y_gcd m₁ m₂) ≤ padicValNat p (Nat.factorial n₁) := by
      rw [← Nat.factorization_def _ hp_pr, ← Nat.factorization_def _ hp_pr]
      exact (Nat.factorization_le_iff_dvd (by
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
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
      · have hp_even2 : ¬ p ∈ Podd n₂ := fun h => hp_odd ((hPodd_iff p hp_pr hp3 h2dvd).mpr h)
        have hp_u12 : p ∣ u₁₂ := dvd_trans hpX (Nat.gcd_dvd_right _ _)
        have hZ12 := (h2.1 hp_u12).2 hp_even2
        have hle_M22 : padicValNat p (Z_star n₂ u₁₂ ^ 2) ≤ padicValNat p M₂₂ := by
          dsimp [M₂₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₂ ≤ padicValNat p (M₁₁ * M₂₂) := by
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
    · by_cases hp_odd : p ∈ Podd n₁
      · have hp_odd2 := (hPodd_iff p hp_pr hp3 h2dvd).mp hp_odd
        have hp_u22 : p ∣ u₂₂ := dvd_trans hpY (Nat.gcd_dvd_right _ _)
        have hB22 := (h2.2 hp_u22).1 hp_odd2
        have hle_M22 : padicValNat p (B_part n₂ u₂₂) ≤ padicValNat p M₂₂ := by
          dsimp [M₂₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₂ ≤ padicValNat p (M₁₁ * M₂₂) := by
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
      · have hp_u21 : p ∣ u₂₁ := dvd_trans hpY (Nat.gcd_dvd_left _ _)
        have hZ21 := (h1.2 hp_u21).2 hp_odd
        have hle_M11 : padicValNat p (Z_star n₁ u₂₁ ^ 2) ≤ padicValNat p M₁₁ := by
          dsimp [M₁₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₁₁ ≤ padicValNat p (M₁₁ * M₂₂) := by
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
  have hdvd_XY_21 : X_gcd m₁ m₂ * Y_gcd m₁ m₂ ∣
      2 ^ padicValNat 2 (Nat.factorial n₁) * (M₂₁ * M₁₂) * FlipProd := by
    refine hdvd_universal _ M₂₁ M₁₂ (by positivity) (by positivity) hXY_dvd_fac ?_
    intro p hp_pr hp3 h2dvd hpXY
    haveI : Fact p.Prime := ⟨hp_pr⟩
    have hv_le_n1 : padicValNat p (X_gcd m₁ m₂ * Y_gcd m₁ m₂) ≤ padicValNat p (Nat.factorial n₁) := by
      rw [← Nat.factorization_def _ hp_pr, ← Nat.factorization_def _ hp_pr]
      exact (Nat.factorization_le_iff_dvd (by
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
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
      · have hp_u11 : p ∣ u₁₁ := dvd_trans hpX (Nat.gcd_dvd_left _ _)
        have hZ11 := (h1.1 hp_u11).2 hp_odd
        have hle_M21 : padicValNat p (Z_star n₁ u₁₁ ^ 2) ≤ padicValNat p M₂₁ := by
          dsimp [M₂₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₁ ≤ padicValNat p (M₂₁ * M₁₂) := by
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
    · by_cases hp_odd : p ∈ Podd n₁
      · have hp_u21 : p ∣ u₂₁ := dvd_trans hpY (Nat.gcd_dvd_left _ _)
        have hB21 := (h1.2 hp_u21).1 hp_odd
        have hle_M21 : padicValNat p (B_part n₁ u₂₁) ≤ padicValNat p M₂₁ := by
          dsimp [M₂₁]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₂₁ ≤ padicValNat p (M₂₁ * M₁₂) := by
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
        omega
      · have hp_even2 : ¬ p ∈ Podd n₂ := fun h => hp_odd ((hPodd_iff p hp_pr hp3 h2dvd).mpr h)
        have hp_u22 : p ∣ u₂₂ := dvd_trans hpY (Nat.gcd_dvd_right _ _)
        have hZ22 := (h2.2 hp_u22).2 hp_even2
        have hle_M12 : padicValNat p (Z_star n₂ u₂₂ ^ 2) ≤ padicValNat p M₁₂ := by
          dsimp [M₁₂]; rw [padicValNat.mul (B_part_pos _ _).ne' (pow_ne_zero 2 (Z_star_pos _ _).ne')]; omega
        have hle_prod : padicValNat p M₁₂ ≤ padicValNat p (M₂₁ * M₁₂) := by
          rw [padicValNat.mul (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne' (mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)).ne']; omega
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
        min (ε / 256) (1 / 8) * (n_a : ℝ) * Real.log (n_a : ℝ) := by
      have h1 := hN_sodd n_a (by omega)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
      linarith
    have hSodd_pos : 0 < S_odd n_a := by
      have := (abs_le.mp hSodd_a).1
      have h1 : (1 / 8 : ℝ) ≥ min (ε / 256) (1 / 8) := min_le_right _ _
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
        rw [show α = 1 + (α - 1) by ring, Real.rpow_add hn₁_pos, Real.rpow_one]
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
        have h2 : |Delta_parity n_a| / 2 ≤ (ε / 512) * ((n_a : ℝ) * Real.log (n_a : ℝ)) := by linarith
        have h3 : (n_a : ℝ) * Real.log (n_a : ℝ) ≤ 2 * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) := by
          nlinarith only [hna_log_ub, hε_le1, show (0 : ℝ) ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
        calc |Delta_parity n_a| / 2 ≤ (ε / 512) * ((n_a : ℝ) * Real.log (n_a : ℝ)) := h2
          _ ≤ (ε / 512) * (2 * ((n₁ : ℝ) * Real.log (n₁ : ℝ))) := by gcongr
          _ ≤ (ε / 64) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by nlinarith only [hε, show (0 : ℝ) ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
      linarith
    have hθ_01 : 0 ≤ theta_weight n_a m_a ∧ theta_weight n_a m_a ≤ 1 :=
      ⟨theta_weight_nonneg n_a m_a, theta_weight_le_one (by omega) hma⟩
    have h_diff_S : |2 * S_odd n_a - (n₁ : ℝ) * Real.log (n₁ : ℝ)| ≤ (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      have h1 : |2 * S_odd n_a - (n_a : ℝ) * Real.log (n_a : ℝ)| ≤ (ε / 64) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
        have h1' := abs_le.mp hSodd_a
        have hmin : min (ε / 256) (1 / 8) ≤ ε / 256 := min_le_left _ _
        have h_na2 : (n_a : ℝ) * Real.log (n_a : ℝ) ≤ 2 * ((n₁ : ℝ) * Real.log (n₁ : ℝ)) := by
          nlinarith only [hna_log_ub, hε_le1, show (0 : ℝ) ≤ (n₁ : ℝ) * Real.log (n₁ : ℝ) by positivity]
        have h_b : |2 * S_odd n_a - (n_a : ℝ) * Real.log (n_a : ℝ)| ≤ (ε / 128) * ((n_a : ℝ) * Real.log (n_a : ℝ)) := by
          rw [abs_le]; constructor <;> nlinarith only [h1'.1, h1'.2, hmin, show 0 ≤ (n_a : ℝ) * Real.log (n_a : ℝ) by positivity]
        calc |2 * S_odd n_a - (n_a : ℝ) * Real.log (n_a : ℝ)|
            ≤ (ε / 128) * ((n_a : ℝ) * Real.log (n_a : ℝ)) := h_b
          _ ≤ (ε / 128) * (2 * ((n₁ : ℝ) * Real.log (n₁ : ℝ))) := by gcongr
          _ = (ε / 64) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
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
    have hlogP_le : 6 * Real.log (P_ratio n₁ n₂ : ℝ) ≤ (3 * ε / 64) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
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
          rw [show α = 1 + (α - 1) by ring, Real.rpow_add hn₁_pos, Real.rpow_one]
        have hmin : min (ε / 256) (1 / 4) ≤ ε / 256 := min_le_left _ _
        calc ((n₂ - n₁ : ℕ) : ℝ) ≤ (n₁ : ℝ) ^ α := h_gap
          _ = (n₁ : ℝ) * (n₁ : ℝ) ^ (α - 1) := h1'
          _ ≤ (n₁ : ℝ) * min (ε / 256) (1 / 4) := by gcongr; exact h_al.le
          _ ≤ (ε / 256) * (n₁ : ℝ) := by nlinarith
      calc 6 * Real.log (P_ratio n₁ n₂ : ℝ)
          ≤ 6 * (((ε / 256) * (n₁ : ℝ)) * (2 * Real.log (n₁ : ℝ))) := by gcongr
        _ = (3 * ε / 64) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
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
  have hM_pos : ∀ a b, 0 < B_part n₁ a * Z_star n₁ b ^ 2 := fun a b =>
    mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)
  have hM2_pos : ∀ a b, 0 < B_part n₂ a * Z_star n₂ b ^ 2 := fun a b =>
    mul_pos (B_part_pos _ _) (pow_pos (Z_star_pos _ _) 2)
  have h_log_ZW_22 := h_log_bound_from_M (Z_gcd m₁ m₂ * W_gcd m₁ m₂) M₂₁ M₂₂
    (mul_pos hZ_pos hW_pos) (hM_pos _ _) (hM2_pos _ _) hdvd_ZW_22
  have h_log_ZW_11 := h_log_bound_from_M (Z_gcd m₁ m₂ * W_gcd m₁ m₂) M₁₁ M₁₂
    (mul_pos hZ_pos hW_pos) (hM_pos _ _) (hM2_pos _ _) hdvd_ZW_11
  have h_log_XY_12 := h_log_bound_from_M (X_gcd m₁ m₂ * Y_gcd m₁ m₂) M₁₁ M₂₂
    (mul_pos hX_pos hY_pos) (hM_pos _ _) (hM2_pos _ _) hdvd_XY_12
  have h_log_XY_21 := h_log_bound_from_M (X_gcd m₁ m₂ * Y_gcd m₁ m₂) M₂₁ M₁₂
    (mul_pos hX_pos hY_pos) (hM_pos _ _) (hM2_pos _ _) hdvd_XY_21
  have hM21_ub := (abs_le.mp hM1_rel.1).2
  have hM11_ub := (abs_le.mp hM1_rel.2).2
  have hM22_ub := (abs_le.mp hM2_rel.1).2
  have hM12_ub := (abs_le.mp hM2_rel.2).2
  have hδ_le : δ ≤ ε / 16 := min_le_left _ _
  have hnlog_pos : 0 < (n₁ : ℝ) * Real.log (n₁ : ℝ) := by positivity
  set Lnl := (n₁ : ℝ) * Real.log (n₁ : ℝ)
  have hM21_e : Real.log (M₂₁ : ℝ) ≤ (theta_weight n₁ m₁ + ε / 16) * Lnl := by
    have hr : (theta_weight n₁ m₁ + ε / 16) * Lnl =
        theta_weight n₁ m₁ * (n₁ : ℝ) * Real.log (n₁ : ℝ) + (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      dsimp [Lnl]; ring
    dsimp [M₂₁, u₁₁, u₂₁]; linarith [hM21_ub, hr]
  have hM22_e : Real.log (M₂₂ : ℝ) ≤ (theta_weight n₂ m₂ + ε / 16) * Lnl := by
    have hr : (theta_weight n₂ m₂ + ε / 16) * Lnl =
        theta_weight n₂ m₂ * (n₁ : ℝ) * Real.log (n₁ : ℝ) + (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      dsimp [Lnl]; ring
    dsimp [M₂₂, u₁₂, u₂₂]; linarith [hM22_ub, hr]
  have hM11_e : Real.log (M₁₁ : ℝ) ≤ (1 - theta_weight n₁ m₁ + ε / 16) * Lnl := by
    have hr : (1 - theta_weight n₁ m₁ + ε / 16) * Lnl =
        (1 - theta_weight n₁ m₁) * (n₁ : ℝ) * Real.log (n₁ : ℝ) + (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      dsimp [Lnl]; ring
    dsimp [M₁₁, u₁₁, u₂₁]; linarith [hM11_ub, hr]
  have hM12_e : Real.log (M₁₂ : ℝ) ≤ (1 - theta_weight n₂ m₂ + ε / 16) * Lnl := by
    have hr : (1 - theta_weight n₂ m₂ + ε / 16) * Lnl =
        (1 - theta_weight n₂ m₂) * (n₁ : ℝ) * Real.log (n₁ : ℝ) + (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
      dsimp [Lnl]; ring
    dsimp [M₁₂, u₁₂, u₂₂]; linarith [hM12_ub, hr]
  have hZW_lb_e : (1 / 2 - ε / 16) * Lnl ≤ Real.log ((Z_gcd m₁ m₂ * W_gcd m₁ m₂ : ℕ) : ℝ) := by
    push_cast; have hr : (1 / 2 - ε / 16) * Lnl = (1 / 2 - ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by dsimp [Lnl]; ring
    linarith [hlogZW_lb, hr]
  have hXY_lb_e : (1 / 2 - ε / 16) * Lnl ≤ Real.log ((X_gcd m₁ m₂ * Y_gcd m₁ m₂ : ℕ) : ℝ) := by
    push_cast; have hr : (1 / 2 - ε / 16) * Lnl = (1 / 2 - ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by dsimp [Lnl]; ring
    linarith [hlogXY_lb, hr]
  have hn1_log2_e : (n₁ : ℝ) * Real.log 2 ≤ (ε / 16) * Lnl := by
    have hr : (ε / 16) * Lnl = (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by dsimp [Lnl]; ring
    linarith [hn1_log2, hr]
  have hflip_ub_e : parityFlipWeight n₁ n₂ ≤ (α / 2 + δ + ε / 16) * Lnl := by
    have hr : (α / 2 + δ + ε / 16) * Lnl = (α / 2 + δ + ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by dsimp [Lnl]; ring
    linarith [hflip_ub, hr]
  have h1 : (1 - α) / 2 - ε ≤ theta_weight n₁ m₁ + theta_weight n₂ m₂ := by
    have hcomb : (1 / 2 - ε / 16) * Lnl ≤
        (theta_weight n₁ m₁ + theta_weight n₂ m₂ + α / 2 + δ + 4 * (ε / 16)) * Lnl := by
      have hr : (theta_weight n₁ m₁ + theta_weight n₂ m₂ + α / 2 + δ + 4 * (ε / 16)) * Lnl =
          (ε / 16) * Lnl + (theta_weight n₁ m₁ + ε / 16) * Lnl + (theta_weight n₂ m₂ + ε / 16) * Lnl +
          (α / 2 + δ + ε / 16) * Lnl := by ring
      linarith [hZW_lb_e, h_log_ZW_22, hn1_log2_e, hM21_e, hM22_e, hflip_ub_e, hr]
    have hcoeff := le_of_mul_le_mul_right hcomb hnlog_pos
    linarith
  have h2 : theta_weight n₁ m₁ + theta_weight n₂ m₂ ≤ (3 + α) / 2 + ε := by
    have hcomb : (1 / 2 - ε / 16) * Lnl ≤
        (2 - (theta_weight n₁ m₁ + theta_weight n₂ m₂) + α / 2 + δ + 4 * (ε / 16)) * Lnl := by
      have hr : (2 - (theta_weight n₁ m₁ + theta_weight n₂ m₂) + α / 2 + δ + 4 * (ε / 16)) * Lnl =
          (ε / 16) * Lnl + (1 - theta_weight n₁ m₁ + ε / 16) * Lnl + (1 - theta_weight n₂ m₂ + ε / 16) * Lnl +
          (α / 2 + δ + ε / 16) * Lnl := by ring
      linarith [hZW_lb_e, h_log_ZW_11, hn1_log2_e, hM11_e, hM12_e, hflip_ub_e, hr]
    have hcoeff := le_of_mul_le_mul_right hcomb hnlog_pos
    linarith
  have h3b : theta_weight n₁ m₁ - theta_weight n₂ m₂ ≤ (1 + α) / 2 + ε := by
    have hcomb : (1 / 2 - ε / 16) * Lnl ≤
        (1 + (theta_weight n₂ m₂ - theta_weight n₁ m₁) + α / 2 + δ + 4 * (ε / 16)) * Lnl := by
      have hr : (1 + (theta_weight n₂ m₂ - theta_weight n₁ m₁) + α / 2 + δ + 4 * (ε / 16)) * Lnl =
          (ε / 16) * Lnl + (1 - theta_weight n₁ m₁ + ε / 16) * Lnl + (theta_weight n₂ m₂ + ε / 16) * Lnl +
          (α / 2 + δ + ε / 16) * Lnl := by ring
      linarith [hXY_lb_e, h_log_XY_12, hn1_log2_e, hM11_e, hM22_e, hflip_ub_e, hr]
    have hcoeff := le_of_mul_le_mul_right hcomb hnlog_pos
    linarith
  have h3a : theta_weight n₂ m₂ - theta_weight n₁ m₁ ≤ (1 + α) / 2 + ε := by
    have hcomb : (1 / 2 - ε / 16) * Lnl ≤
        (1 + (theta_weight n₁ m₁ - theta_weight n₂ m₂) + α / 2 + δ + 4 * (ε / 16)) * Lnl := by
      have hr : (1 + (theta_weight n₁ m₁ - theta_weight n₂ m₂) + α / 2 + δ + 4 * (ε / 16)) * Lnl =
          (ε / 16) * Lnl + (theta_weight n₁ m₁ + ε / 16) * Lnl + (1 - theta_weight n₂ m₂ + ε / 16) * Lnl +
          (α / 2 + δ + ε / 16) * Lnl := by ring
      linarith [hXY_lb_e, h_log_XY_21, hn1_log2_e, hM21_e, hM12_e, hflip_ub_e, hr]
    have hcoeff := le_of_mul_le_mul_right hcomb hnlog_pos
    linarith
  exact ⟨h1, h2, abs_le.mpr ⟨by linarith, h3b⟩⟩

open Classical in
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
          have htel : ∀ k : ℕ, (hk : k ≤ S.card - 1) →
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
        have hsub : ((S.card : ℝ) - 1) = ((S.card - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ S.card)]; push_cast; ring
        rw [hsub]; linarith
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
      have hn_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn_mem.1).1
      refine ⟨Nat.log 2 n, Nat.lt_succ_of_le (Nat.log_mono_right hn_icc.2), hn_mem, ?_, ?_⟩
      · exact Nat.pow_log_le_self 2 (by omega)
      · exact Nat.le_sub_one_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n)
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
          exact ⟨hx.2.1, le_trans hx.2.2 (Nat.sub_le _ _)⟩)
        (fun x hx y hy hxy => by
          simp only [B_k, S_hi, S_all, Finset.mem_filter] at hx hy
          have hgap_xy := hgap₂ x y hx.1.2 hxy hx.1.1.2 hy.1.1.2
          have hpow_le : ((2 : ℝ) ^ k) ^ (1 - ε₂) ≤ (x : ℝ) ^ (1 - ε₂) :=
            Real.rpow_le_rpow (by positivity) (by exact_mod_cast hx.2.1) (by linarith [min_le_right (ε / 2) (1 / 2 : ℝ)])
          have hlt_r : (x : ℝ) < (y : ℝ) := by exact_mod_cast hxy
          have : ((y - x : ℕ) : ℝ) = (y : ℝ) - (x : ℝ) := by rw [Nat.cast_sub hxy.le]
          linarith)
      have h_div_eq : (((2 ^ (k + 1) : ℕ) : ℝ) - ((2 ^ k : ℕ) : ℝ)) / ((2 : ℝ) ^ k) ^ (1 - ε₂) =
          ((2 : ℝ) ^ ε₂) ^ k := by
        have hsub : (((2 ^ (k + 1) : ℕ) : ℝ) - ((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k := by
          push_cast; rw [pow_succ]; ring
        rw [hsub]
        have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
        rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_sub (by norm_num), show (k : ℝ) - (k : ℝ) * (1 - ε₂) = ε₂ * (k : ℝ) by ring,
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
  have hpow : ((j : ℝ) ^ (3 / 2 : ℝ)) ≤ ((j : ℝ) ^ 2) ^ (1 - 1 / 4 : ℝ) := by
    have hj_nn : (0 : ℝ) ≤ j := by positivity
    rw [show (j : ℝ) ^ 2 = (j : ℝ) ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hj_nn]
    norm_num
  have h32 : 2 * (j : ℝ) + 1 ≤ (j : ℝ) ^ (3 / 2 : ℝ) := by
    have hj10 : (10 : ℝ) ≤ j := by exact_mod_cast (by omega : 10 ≤ j)
    have hsq : (2 * (j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) ^ (3 / 2 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast ((j : ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul (by positivity)]
      norm_num; nlinarith
    nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ j) (3 / 2)]
  push_cast at h1; linarith


end GrasGreenbergBrocard
