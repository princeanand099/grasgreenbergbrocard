import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic
import GrasGreenbergBrocard.ExternalAxiomsSec3
import GrasGreenbergBrocard.ExternalAxiomsSec4
import GrasGreenbergBrocard.ExternalAxiomsSec5
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.ValuationParityThm
import GrasGreenbergBrocard.ValuationParityMod
import GrasGreenbergBrocard.ChebyshevLucas
import GrasGreenbergBrocard.PellFundamental
import GrasGreenbergBrocard.Thm1_1Collapse
import GrasGreenbergBrocard.Prop5_1MidpointBias

/-!
# Theorem 5.2: Midpoint Core Bipartition, Cross-Symmetry, Radical Bounds, and Effective Landau–Siegel Lower Bounds

Formalizes Section 5.1, Theorem 5.2(i)–(ii) and equations (5.4)–(5.7) of the manuscript:
- `thm_5_2_part1_bipartition`: `δ₁ δ₂ = q_n`, `gcd(δ₁, δ₂) = 1`, `z₁ z₂ = s_n / 2`,
  `δ₂ z₂^2 - δ₁ z₁^2 = 1`, `δ₁ > 1`, and `δ₂ = 1 ↔ k = 2` / `δ₂ > 1 ↔ k = 1`
- `thm_5_2_part1_cross_symmetry`: exact reciprocal cross-symmetry laws (eq. 5.4)
- `thm_5_2_part1_radical_bounds`: unconditional `n^{1/2 - ε}` bounds on `P^+(m ∓ 1)`, `ω(m ∓ 1)`,
  and `rad(m ∓ 1)` (eq. 5.5)
- `thm_5_2_part2_effective_cores`: effective sub-exponential lower bounds
  `δ₁^{mid}(n), δ₂^{mid}(n) > exp(c₀ √(log n))` (eq. 5.6)
- `thm_5_2_part2_pell_pm2_insoluble`: non-solubility of `x^2 - q_n y^2 = ±2` for all sufficiently large `n`
-/

set_option maxHeartbeats 800000

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard

/-! ### Helper Definitions for Theorem 5.2(i) -/

/-- Even-valuation odd-prime factorial integer `A_n^*` (`p ≥ 3`). -/
def A_star5 (n : ℕ) : ℕ :=
  ∏ p ∈ (Peven n).filter (3 ≤ ·), p ^ padicValNat p (Nat.factorial n)

/-- Odd-valuation odd-prime factorial integer `B_n^*` (`p ≥ 3`). -/
def B_star5 (n : ℕ) : ℕ :=
  ∏ p ∈ (Podd n).filter (3 ≤ ·), p ^ padicValNat p (Nat.factorial n)

/-- Odd-prime parity discrepancy `Δ_parity^*(n) = ∑_{3 ≤ p ≤ n} (-1)^{v_p(n!)} v_p(n!) log p`. -/
def Delta_parity_odd (n : ℕ) : ℝ :=
  Real.log (A_star5 n : ℝ) - Real.log (B_star5 n : ℝ)

/-- Odd-valuation odd-prime part `B^{(i)} = ∏_{p ∈ Podd(n) \ {2}, p ∣ u_i^*} p^{v_p(n!)}`. -/
def B_part (n u : ℕ) : ℕ :=
  ∏ p ∈ (Podd n).filter (fun p => 3 ≤ p ∧ p ∣ oddPartNat u),
    p ^ padicValNat p (Nat.factorial n)

/-- Even-valuation odd-prime square-root `Z_i^* = ∏_{q ∈ Peven(n) \ {2}, q ∣ u_i^*} q^{v_q(n!)/2}`. -/
def Z_star (n u : ℕ) : ℕ :=
  ∏ q ∈ (Peven n).filter (fun q => 3 ≤ q ∧ q ∣ oddPartNat u),
    q ^ (padicValNat q (Nat.factorial n) / 2)

lemma A_star5_pos (n : ℕ) : 0 < A_star5 n := by
  unfold A_star5
  exact Finset.prod_pos (fun p hp => pow_pos (by
    have := (Finset.mem_filter.mp hp).2; omega) _)

lemma B_star5_pos (n : ℕ) : 0 < B_star5 n := by
  unfold B_star5
  exact Finset.prod_pos (fun p hp => pow_pos (by
    have := (Finset.mem_filter.mp hp).2; omega) _)

lemma B_part_pos (n u : ℕ) : 0 < B_part n u := by
  unfold B_part
  exact Finset.prod_pos (fun p hp => pow_pos (by
    have := (Finset.mem_filter.mp hp).2.1; omega) _)

lemma Z_star_pos (n u : ℕ) : 0 < Z_star n u := by
  unfold Z_star
  exact Finset.prod_pos (fun q hq => pow_pos (by
    have := (Finset.mem_filter.mp hq).2.1; omega) _)

lemma A_star5_mul_B_star5 (n : ℕ) :
    A_star5 n * B_star5 n = oddPartNat (Nat.factorial n) := by
  apply Nat.eq_of_factorization_eq (mul_pos (A_star5_pos n) (B_star5_pos n)).ne'
    (oddPartNat_pos (Nat.factorial_pos n)).ne'
  intro p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
        padicValNat.mul (A_star5_pos n).ne' (B_star5_pos n).ne']
    have hA_val : padicValNat p (A_star5 n) =
        if p ∈ (Peven n).filter (3 ≤ ·) then padicValNat p (Nat.factorial n) else 0 := by
      unfold A_star5
      rw [padicValNat_prod_eq (fun q hq => pow_ne_zero _ (by have := (Finset.mem_filter.mp hq).2; omega))]
      split_ifs with hmem
      · rw [Finset.sum_eq_single p]
        · rw [padicValNat_pow_eq, padicValNat_self, mul_one]
        · intro q hq hqp
          have hq_pr : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
          rw [padicValNat_pow_eq,
              padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm),
              mul_zero]
        · intro habs; exact absurd hmem habs
      · apply Finset.sum_eq_zero
        intro q hq
        have hqp : q ≠ p := fun h => hmem (h ▸ hq)
        have hq_pr : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
        rw [padicValNat_pow_eq,
            padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm),
            mul_zero]
    have hB_val : padicValNat p (B_star5 n) =
        if p ∈ (Podd n).filter (3 ≤ ·) then padicValNat p (Nat.factorial n) else 0 := by
      unfold B_star5
      rw [padicValNat_prod_eq (fun q hq => pow_ne_zero _ (by have := (Finset.mem_filter.mp hq).2; omega))]
      split_ifs with hmem
      · rw [Finset.sum_eq_single p]
        · rw [padicValNat_pow_eq, padicValNat_self, mul_one]
        · intro q hq hqp
          have hq_pr : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
          rw [padicValNat_pow_eq,
              padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm),
              mul_zero]
        · intro habs; exact absurd hmem habs
      · apply Finset.sum_eq_zero
        intro q hq
        have hqp : q ≠ p := fun h => hmem (h ▸ hq)
        have hq_pr : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
        rw [padicValNat_pow_eq,
            padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm),
            mul_zero]
    rw [hA_val, hB_val]
    by_cases hp2 : p = 2
    · subst hp2
      rw [padicValNat.eq_zero_of_not_dvd (oddPartNat_not_dvd_two (Nat.factorial_pos n))]
      simp [Finset.mem_filter]
    · rw [padicValNat_oddPartNat hp hp2 (Nat.factorial_pos n)]
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      by_cases hpn : p ≤ n
      · unfold Peven Podd
        by_cases hodd : padicValNat p (Nat.factorial n) % 2 = 1
        · simp [Finset.mem_filter, Finset.mem_Icc, hp.two_le, hpn, hp, hp3, hodd, show padicValNat p (Nat.factorial n) % 2 ≠ 0 by omega]
        · simp [Finset.mem_filter, Finset.mem_Icc, hp.two_le, hpn, hp, hp3, hodd, show padicValNat p (Nat.factorial n) % 2 = 0 by omega]
      · have hnd : ¬ p ∣ Nat.factorial n := fun hd => hpn (hp.dvd_factorial.mp hd)
        rw [padicValNat.eq_zero_of_not_dvd hnd]
        simp [Finset.mem_filter, Finset.mem_Icc, hpn]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma brocard_m_odd {n m : ℕ} (hn : 2 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    m % 2 = 1 ∧ 3 ≤ m := by
  have h2_fac : 2 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) hn
  have hm2_odd : m ^ 2 % 2 = 1 := by omega
  have hm_odd : m % 2 = 1 := by
    by_contra he
    have : m % 2 = 0 := by omega
    have : m ^ 2 % 2 = 0 := by simp [sq, Nat.mul_mod, this]
    omega
  have hm3 : 3 ≤ m := by
    have hfac2 : 2 ≤ Nat.factorial n := Nat.le_of_dvd (Nat.factorial_pos n) h2_fac
    nlinarith
  exact ⟨hm_odd, hm3⟩

lemma brocard_u1_u2_rel {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    let u₁ := (m - 1) / 2
    let u₂ := (m + 1) / 2
    0 < u₁ ∧ 0 < u₂ ∧ u₂ = u₁ + 1 ∧ Nat.Coprime u₁ u₂ ∧
    4 * u₁ * u₂ = Nat.factorial n ∧ u₁ * u₂ = q_n n * (s_n n / 2) ^ 2 ∧
    2 ∣ s_n n := by
  have ⟨hm_odd, hm3⟩ := brocard_m_odd (by omega) hm
  set u₁ := (m - 1) / 2
  set u₂ := (m + 1) / 2
  have hu₁_pos : 0 < u₁ := by omega
  have hu₂_pos : 0 < u₂ := by omega
  have hu_diff : u₂ = u₁ + 1 := by omega
  have hcop : Nat.Coprime u₁ u₂ := by
    rw [hu_diff]; exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right u₁)
  have h4mul : 4 * u₁ * u₂ = Nat.factorial n := by
    have hm1 : 2 * u₁ = m - 1 := by omega
    have hm2 : 2 * u₂ = m + 1 := by omega
    zify [show 1 ≤ m by omega]
    have h1z : 2 * (u₁ : ℤ) = (m : ℤ) - 1 := by exact_mod_cast hm1
    have h2z : 2 * (u₂ : ℤ) = (m : ℤ) + 1 := by exact_mod_cast hm2
    have hmz : (Nat.factorial n : ℤ) + 1 = (m : ℤ) ^ 2 := by exact_mod_cast hm
    nlinarith
  have hfac_qs := factorial_eq_q_n_mul_s_n_sq n
  have h4_dvd_fac : 4 ∣ Nat.factorial n := by
    rw [← h4mul]; exact dvd_mul_of_dvd_left (dvd_mul_right 4 u₁) u₂
  have h2_dvd_sn : 2 ∣ s_n n := by
    have h4_dvd_qs : 2 * 2 ∣ q_n n * (s_n n) ^ 2 := by simpa [← hfac_qs] using h4_dvd_fac
    by_contra h2nd
    have hcop2 : Nat.Coprime 2 (s_n n) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2nd
    have hcop4 : Nat.Coprime (2 * 2) ((s_n n) ^ 2) := (hcop2.mul_left hcop2).pow_right 2
    have h4_dvd_q : 2 * 2 ∣ q_n n := hcop4.dvd_of_dvd_mul_right h4_dvd_qs
    exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) 2 Nat.prime_two h4_dvd_q
  have hu_qs : u₁ * u₂ = q_n n * (s_n n / 2) ^ 2 := by
    have hs2 : s_n n = 2 * (s_n n / 2) := (Nat.mul_div_cancel' h2_dvd_sn).symm
    have h4_eq : 4 * (u₁ * u₂) = 4 * (q_n n * (s_n n / 2) ^ 2) := by
      calc 4 * (u₁ * u₂) = 4 * u₁ * u₂ := by ring
        _ = Nat.factorial n := h4mul
        _ = q_n n * (s_n n) ^ 2 := hfac_qs
        _ = q_n n * (2 * (s_n n / 2)) ^ 2 := by rw [hs2]
        _ = 4 * (q_n n * (s_n n / 2) ^ 2) := by ring
    omega
  exact ⟨hu₁_pos, hu₂_pos, hu_diff, hcop, h4mul, hu_qs, h2_dvd_sn⟩

/-! ### Theorem 5.2(i): Midpoint Core Bipartition -/

theorem thm_5_2_part1_bipartition {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    let u₁ := (m - 1) / 2
    let u₂ := (m + 1) / 2
    let δ₁ := coreNat u₁
    let δ₂ := coreNat u₂
    let z₁ := sqPartNat u₁
    let z₂ := sqPartNat u₂
    δ₁ * δ₂ = q_n n ∧
    Nat.Coprime δ₁ δ₂ ∧
    z₁ * z₂ = s_n n / 2 ∧
    (δ₂ : ℤ) * (z₂ : ℤ) ^ 2 - (δ₁ : ℤ) * (z₁ : ℤ) ^ 2 = 1 ∧
    1 < δ₁ ∧
    (∀ X₁ Y₁ k : ℕ, IsFundamentalPell (q_n n) X₁ Y₁ →
      (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ k →
      (k = 1 ∨ k = 2) →
      ((δ₂ = 1 ↔ k = 2) ∧ (1 < δ₂ ↔ k = 1))) := by
  have ⟨hu₁_pos, hu₂_pos, hu_diff, hcop_u, _, hu_qs, h2_dvd_sn⟩ := brocard_u1_u2_rel hn hm
  set u₁ := (m - 1) / 2
  set u₂ := (m + 1) / 2
  set δ₁ := coreNat u₁
  set δ₂ := coreNat u₂
  set z₁ := sqPartNat u₁
  set z₂ := sqPartNat u₂
  have h1_eq : δ₁ * z₁ ^ 2 = u₁ := coreNat_mul_sqPartNat_sq hu₁_pos
  have h2_eq : δ₂ * z₂ ^ 2 = u₂ := coreNat_mul_sqPartNat_sq hu₂_pos
  have hδ₁_pos : 0 < δ₁ := coreNat_pos u₁
  have hδ₂_pos : 0 < δ₂ := coreNat_pos u₂
  have hz₁_pos : 0 < z₁ := sqPartNat_pos u₁
  have hz₂_pos : 0 < z₂ := sqPartNat_pos u₂
  have hq_pos : 0 < q_n n := (q_n_squarefree n).ne_zero |> Nat.pos_of_ne_zero
  have hs2_pos : 0 < s_n n / 2 := by
    have hs_pos : 0 < s_n n := Nat.pos_of_ne_zero (fun h0 => by
      have := factorial_eq_q_n_mul_s_n_sq n; rw [h0] at this; simp at this
      exact (Nat.factorial_pos n).ne' this)
    exact Nat.div_pos (Nat.le_of_dvd hs_pos h2_dvd_sn) (by norm_num)
  have hcop_δ : Nat.Coprime δ₁ δ₂ :=
    hcop_u.coprime_dvd_left (h1_eq ▸ dvd_mul_right δ₁ _) |>.coprime_dvd_right (h2_eq ▸ dvd_mul_right δ₂ _)
  have hδ_prod : δ₁ * δ₂ = q_n n := by
    apply Nat.eq_of_factorization_eq (mul_pos hδ₁_pos hδ₂_pos).ne' hq_pos.ne'
    intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
          padicValNat.mul hδ₁_pos.ne' hδ₂_pos.ne']
      unfold δ₁ δ₂
      rw [padicValNat_coreNat hp hu₁_pos, padicValNat_coreNat hp hu₂_pos]
      have hv_eq := congrArg (padicValNat p) hu_qs
      rw [padicValNat.mul hu₁_pos.ne' hu₂_pos.ne',
          padicValNat.mul hq_pos.ne' (pow_ne_zero 2 hs2_pos.ne'),
          padicValNat_pow_eq] at hv_eq
      have h_not_both : padicValNat p u₁ = 0 ∨ padicValNat p u₂ = 0 := by
        by_contra hboth
        push_neg at hboth
        have hd1 : p ∣ u₁ := by simpa using (padicValNat_dvd_iff_le hu₁_pos.ne').mpr (Nat.pos_of_ne_zero hboth.1)
        have hd2 : p ∣ u₂ := by simpa using (padicValNat_dvd_iff_le hu₂_pos.ne').mpr (Nat.pos_of_ne_zero hboth.2)
        have := Nat.dvd_gcd hd1 hd2
        rw [hcop_u.gcd_eq_one] at this
        exact hp.ne_one (Nat.dvd_one.mp this)
      have hq_le1 : padicValNat p (q_n n) ≤ 1 := by
        by_contra hgt
        have hp2_dvd : p * p ∣ q_n n := by
          rw [← sq]
          exact dvd_trans (pow_dvd_pow p (by omega : 2 ≤ padicValNat p (q_n n))) pow_padicValNat_dvd
        exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp hp2_dvd
      rcases h_not_both with h0 | h0 <;> rw [h0] at hv_eq ⊢ <;> omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hz_prod : z₁ * z₂ = s_n n / 2 := by
    have hsq_eq : (z₁ * z₂) ^ 2 = (s_n n / 2) ^ 2 := by
      have h1 : (δ₁ * δ₂) * (z₁ * z₂) ^ 2 = q_n n * (s_n n / 2) ^ 2 := by
        calc (δ₁ * δ₂) * (z₁ * z₂) ^ 2 = (δ₁ * z₁ ^ 2) * (δ₂ * z₂ ^ 2) := by ring
          _ = u₁ * u₂ := by rw [h1_eq, h2_eq]
          _ = q_n n * (s_n n / 2) ^ 2 := hu_qs
      rw [hδ_prod] at h1
      exact mul_left_cancel₀ hq_pos.ne' h1
    exact (Nat.pow_left_inj (by norm_num : 2 ≠ 0)).mp hsq_eq
  have hdiff : (δ₂ : ℤ) * (z₂ : ℤ) ^ 2 - (δ₁ : ℤ) * (z₁ : ℤ) ^ 2 = 1 := by
    have h1z : (δ₁ : ℤ) * (z₁ : ℤ) ^ 2 = (u₁ : ℤ) := by exact_mod_cast h1_eq
    have h2z : (δ₂ : ℤ) * (z₂ : ℤ) ^ 2 = (u₂ : ℤ) := by exact_mod_cast h2_eq
    have hdz : (u₂ : ℤ) = (u₁ : ℤ) + 1 := by exact_mod_cast hu_diff
    linarith
  have hn6 : n ≠ 6 := by
    intro h6
    subst h6
    have : (Nat.factorial 6 + 1 : ℕ) = 721 := by norm_num
    rw [this] at hm
    have hle : m ≤ 27 := by nlinarith
    interval_cases m <;> norm_num at hm
  have hδ₁_gt1 : 1 < δ₁ := by
    by_contra hle
    have hδ₁_eq1 : δ₁ = 1 := by omega
    have hδ₂_eq_q : δ₂ = q_n n := by rw [← hδ_prod, hδ₁_eq1, one_mul]
    have hneg : (z₁ : ℤ) ^ 2 - (q_n n : ℤ) * (z₂ : ℤ) ^ 2 = -1 := by
      rw [hδ₁_eq1, hδ₂_eq_q] at hdiff
      push_cast at hdiff
      linarith
    obtain ⟨p, hp, hpq, hpmod⟩ := q_n_has_prime_mod4 (by omega) hn6
    exact neg_pell_no_int_sol hp hpq hpmod (z₁ : ℤ) (z₂ : ℤ) hneg
  refine ⟨hδ_prod, hcop_δ, hz_prod, hdiff, hδ₁_gt1, ?_⟩
  intro X₁ Y₁ k hfund h_pell hk
  have hk_iff : δ₂ = 1 ↔ k = 2 := by
    constructor
    · intro hδ₂_1
      rcases hk with rfl | rfl
      · exfalso
        have h_eq1 : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (X₁ : ℝ) + (Y₁ : ℝ) * Real.sqrt (q_n n : ℝ) := by
          simpa [pellUnit, pow_one] using h_pell
        have hm_X₁ : m = X₁ ∧ s_n n = Y₁ := by
          have h_rat : ((m : ℤ) - (X₁ : ℤ) : ℝ) = ((Y₁ : ℤ) - (s_n n : ℤ) : ℝ) * Real.sqrt (q_n n : ℝ) := by
            linarith
          have h_sq : ((m : ℤ) - (X₁ : ℤ)) ^ 2 = (q_n n : ℤ) * ((Y₁ : ℤ) - (s_n n : ℤ)) ^ 2 := by
            have h_r : (((m : ℤ) - (X₁ : ℤ) : ℤ) : ℝ) ^ 2 = ((q_n n : ℤ) * ((Y₁ : ℤ) - (s_n n : ℤ)) ^ 2 : ℤ) := by
              push_cast
              calc ((m : ℝ) - (X₁ : ℝ)) ^ 2 = (((Y₁ : ℝ) - (s_n n : ℝ)) * Real.sqrt (q_n n : ℝ)) ^ 2 := by rw [h_rat]
                _ = ((Y₁ : ℝ) - (s_n n : ℝ)) ^ 2 * (Real.sqrt (q_n n : ℝ)) ^ 2 := by ring
                _ = ((Y₁ : ℝ) - (s_n n : ℝ)) ^ 2 * (q_n n : ℝ) := by rw [Real.sq_sqrt (by positivity)]
                _ = (q_n n : ℝ) * ((Y₁ : ℝ) - (s_n n : ℝ)) ^ 2 := by ring
            exact_mod_cast h_r
          by_cases hY : (Y₁ : ℤ) = (s_n n : ℤ)
          · have hX : (m : ℤ) = (X₁ : ℤ) := by
              rw [hY, sub_self, zero_pow (by norm_num), mul_zero] at h_sq
              nlinarith
            exact ⟨by omega, by omega⟩
          · exfalso
            have h_sq_nat : Int.natAbs ((m : ℤ) - (X₁ : ℤ)) ^ 2 = q_n n * Int.natAbs ((Y₁ : ℤ) - (s_n n : ℤ)) ^ 2 := by
              zify; simpa [sq_abs] using h_sq
            obtain ⟨p, hp, hpq, _⟩ := q_n_has_prime_mod4 (by omega) hn6
            haveI : Fact p.Prime := ⟨hp⟩
            have hLHS := congrArg (padicValNat p) h_sq_nat
            have hA_ne : Int.natAbs ((m : ℤ) - (X₁ : ℤ)) ≠ 0 := by
              intro h0
              have : (m : ℤ) - (X₁ : ℤ) = 0 := Int.natAbs_eq_zero.mp h0
              rw [this, zero_pow (by norm_num)] at h_sq
              have hq_ne : (q_n n : ℤ) ≠ 0 := by exact_mod_cast hq_pos.ne'
              have : ((Y₁ : ℤ) - (s_n n : ℤ)) ^ 2 = 0 := (mul_eq_zero.mp h_sq.symm).resolve_left hq_ne
              exact hY (sub_eq_zero.mp (sq_eq_zero_iff.mp this))
            have hB_ne : Int.natAbs ((Y₁ : ℤ) - (s_n n : ℤ)) ≠ 0 := fun h0 => hY (sub_eq_zero.mp (Int.natAbs_eq_zero.mp h0))
            rw [padicValNat_pow_eq, padicValNat.mul hq_pos.ne' (pow_ne_zero 2 hB_ne),
                padicValNat_pow_eq] at hLHS
            have hvp : padicValNat p (q_n n) = 1 := by
              have h1 : 1 ≤ padicValNat p (q_n n) := one_le_padicValNat_of_dvd hq_pos.ne' hpq
              have hle1 : padicValNat p (q_n n) ≤ 1 := by
                by_contra hgt
                have hpp : p * p ∣ q_n n := by
                  rw [← sq]; exact dvd_trans (pow_dvd_pow p (by omega : 2 ≤ padicValNat p (q_n n))) pow_padicValNat_dvd
                exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp hpp
              omega
            omega
        have hz_pell : z₂ ^ 2 = q_n n * z₁ ^ 2 + 1 := by
          have hδ₁_q : δ₁ = q_n n := by rw [← hδ_prod, hδ₂_1, mul_one]
          rw [hδ₂_1, hδ₁_q] at hdiff
          push_cast at hdiff
          have : (z₂ : ℤ) ^ 2 = (q_n n : ℤ) * (z₁ : ℤ) ^ 2 + 1 := by linarith
          exact_mod_cast this
        have hY_le : Y₁ ≤ z₁ := hfund.2.2.2 z₂ z₁ hz₁_pos hz_pell
        have hz₁_lt : z₁ < Y₁ := by
          rw [← hm_X₁.2]
          have : 2 * (z₁ * z₂) = s_n n := Nat.mul_div_cancel' h2_dvd_sn |> fun h => by rw [hz_prod]; exact h
          nlinarith
        omega
      · rfl
    · intro hk2
      subst hk2
      have h_eq2 : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) =
          ((X₁ : ℝ) ^ 2 + (q_n n : ℝ) * (Y₁ : ℝ) ^ 2) + (2 * (X₁ : ℝ) * (Y₁ : ℝ)) * Real.sqrt (q_n n : ℝ) := by
        rw [h_pell]
        unfold pellUnit
        rw [sq]
        ring_nf
        rw [Real.sq_sqrt (by positivity)]
        ring
      have h_sq_rel : ((m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2)) ^ 2 =
          (q_n n : ℤ) * (2 * (X₁ : ℤ) * (Y₁ : ℤ) - (s_n n : ℤ)) ^ 2 := by
        have h_rat : ((m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2) : ℝ) =
            (2 * (X₁ : ℤ) * (Y₁ : ℤ) - (s_n n : ℤ) : ℝ) * Real.sqrt (q_n n : ℝ) := by
          linarith
        have h_r : (((m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2) : ℤ) : ℝ) ^ 2 =
            ((q_n n : ℤ) * (2 * (X₁ : ℤ) * (Y₁ : ℤ) - (s_n n : ℤ)) ^ 2 : ℤ) := by
          push_cast
          calc _ = ((2 * (X₁ : ℝ) * (Y₁ : ℝ) - (s_n n : ℝ)) * Real.sqrt (q_n n : ℝ)) ^ 2 := by rw [h_rat]
            _ = (2 * (X₁ : ℝ) * (Y₁ : ℝ) - (s_n n : ℝ)) ^ 2 * (Real.sqrt (q_n n : ℝ)) ^ 2 := by ring
            _ = _ := by rw [Real.sq_sqrt (by positivity)]; ring
        exact_mod_cast h_r
      have hm_eq : m = X₁ ^ 2 + q_n n * Y₁ ^ 2 := by
        by_cases hY : 2 * (X₁ : ℤ) * (Y₁ : ℤ) = (s_n n : ℤ)
        · have hX : (m : ℤ) = (X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 := by
            rw [hY, sub_self, zero_pow (by norm_num), mul_zero] at h_sq_rel
            nlinarith
          exact_mod_cast hX
        · exfalso
          have h_sq_nat : Int.natAbs ((m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2)) ^ 2 =
              q_n n * Int.natAbs (2 * (X₁ : ℤ) * (Y₁ : ℤ) - (s_n n : ℤ)) ^ 2 := by
            zify; simpa [sq_abs] using h_sq_rel
          obtain ⟨p, hp, hpq, _⟩ := q_n_has_prime_mod4 (by omega) hn6
          haveI : Fact p.Prime := ⟨hp⟩
          have hA_ne : Int.natAbs ((m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2)) ≠ 0 := by
            intro h0
            have h1 := Int.natAbs_eq_zero.mp h0
            rw [h1, zero_pow (by norm_num)] at h_sq_rel
            have hq_ne : (q_n n : ℤ) ≠ 0 := by exact_mod_cast hq_pos.ne'
            exact hY (sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp h_sq_rel.symm).resolve_left hq_ne)))
          have hB_ne : Int.natAbs (2 * (X₁ : ℤ) * (Y₁ : ℤ) - (s_n n : ℤ)) ≠ 0 :=
            fun h0 => hY (sub_eq_zero.mp (Int.natAbs_eq_zero.mp h0))
          have hLHS := congrArg (padicValNat p) h_sq_nat
          rw [padicValNat_pow_eq, padicValNat.mul hq_pos.ne' (pow_ne_zero 2 hB_ne),
              padicValNat_pow_eq] at hLHS
          have hvp : padicValNat p (q_n n) = 1 := by
            have h1 : 1 ≤ padicValNat p (q_n n) := one_le_padicValNat_of_dvd hq_pos.ne' hpq
            have hle1 : padicValNat p (q_n n) ≤ 1 := by
              by_contra hgt
              have hpp : p * p ∣ q_n n := by
                rw [← sq]; exact dvd_trans (pow_dvd_pow p (by omega : 2 ≤ padicValNat p (q_n n))) pow_padicValNat_dvd
              exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp hpp
            omega
          omega
      have hu₂_sq : u₂ = X₁ ^ 2 := by
        have : m = 2 * X₁ ^ 2 - 1 := by
          have := hfund.2.2.1
          omega
        omega
      unfold δ₂
      rw [hu₂_sq]
      apply Nat.eq_of_factorization_eq (coreNat_pos _).ne' (by norm_num)
      intro p
      by_cases hp : p.Prime
      · haveI : Fact p.Prime := ⟨hp⟩
        rw [Nat.factorization_def _ hp, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply]
        rw [padicValNat_coreNat hp (pow_pos hfund.1 2), padicValNat_pow_eq]
        simp
      · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  refine ⟨hk_iff, ?_⟩
  constructor
  · intro hgt
    rcases hk with rfl | rfl
    · rfl
    · exfalso; have := hk_iff.mpr rfl; omega
  · intro hk1
    subst hk1
    by_contra hle
    have : δ₂ = 1 := by omega
    have := hk_iff.mp this
    omega

/-! ### Theorem 5.2(i): Reciprocal Cross-Symmetry Laws (Eq. 5.4) -/

lemma oddPartNat_u_eq_B_mul_Z_sq {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    let u₁ := (m - 1) / 2
    let u₂ := (m + 1) / 2
    oddPartNat u₁ = B_part n u₁ * (Z_star n u₁) ^ 2 ∧
    oddPartNat u₂ = B_part n u₂ * (Z_star n u₂) ^ 2 ∧
    B_part n u₁ * B_part n u₂ = B_star5 n := by
  have ⟨hu₁_pos, hu₂_pos, _, hcop_u, h4mul, _, _⟩ := brocard_u1_u2_rel hn hm
  set u₁ := (m - 1) / 2
  set u₂ := (m + 1) / 2
  have h_fac_odd : oddPartNat u₁ * oddPartNat u₂ = oddPartNat (Nat.factorial n) := by
    have h4u : 4 * (u₁ * u₂) = Nat.factorial n := by linarith
    apply Nat.eq_of_factorization_eq (mul_pos (oddPartNat_pos hu₁_pos) (oddPartNat_pos hu₂_pos)).ne'
      (oddPartNat_pos (Nat.factorial_pos n)).ne'
    intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
          padicValNat.mul (oddPartNat_pos hu₁_pos).ne' (oddPartNat_pos hu₂_pos).ne']
      by_cases hp2 : p = 2
      · subst hp2
        rw [padicValNat.eq_zero_of_not_dvd (oddPartNat_not_dvd_two hu₁_pos),
            padicValNat.eq_zero_of_not_dvd (oddPartNat_not_dvd_two hu₂_pos),
            padicValNat.eq_zero_of_not_dvd (oddPartNat_not_dvd_two (Nat.factorial_pos n))]
      · rw [padicValNat_oddPartNat hp hp2 hu₁_pos, padicValNat_oddPartNat hp hp2 hu₂_pos,
            padicValNat_oddPartNat hp hp2 (Nat.factorial_pos n)]
        have hv := congrArg (padicValNat p) h4u
        rw [padicValNat.mul (by norm_num) (mul_pos hu₁_pos hu₂_pos).ne',
            padicValNat.eq_zero_of_not_dvd (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow (by simpa [show (4 : ℕ) = 2^2 by norm_num] using hd)))),
            zero_add, padicValNat.mul hu₁_pos.ne' hu₂_pos.ne'] at hv
        exact hv.symm
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hp_val_u : ∀ p u, p.Prime → 3 ≤ p → p ∣ oddPartNat u → (u = u₁ ∨ u = u₂) →
      padicValNat p (oddPartNat u) = padicValNat p (Nat.factorial n) ∧ (p ∈ Podd n ∨ p ∈ Peven n) := by
    intro p u hp hp3 hp_u hu_eq
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by omega
    have hu_pos : 0 < u := by rcases hu_eq with rfl | rfl <;> assumption
    have h_dvd_fac : p ∣ oddPartNat (Nat.factorial n) := by
      rw [← h_fac_odd]
      rcases hu_eq with rfl | rfl
      · exact dvd_mul_of_dvd_left hp_u _
      · exact dvd_mul_of_dvd_right hp_u _
    have h_dvd_n : p ≤ n :=
      hp.dvd_factorial.mp (dvd_trans h_dvd_fac oddPartNat_dvd)
    have h_other_nd : ∀ v, (v = u₁ ∨ v = u₂) → v ≠ u → ¬ p ∣ oddPartNat v := by
      intro v hv hvu hdv
      have h1 : p ∣ u := dvd_trans hp_u oddPartNat_dvd
      have h2 : p ∣ v := dvd_trans hdv oddPartNat_dvd
      have hg : p ∣ Nat.gcd u₁ u₂ := by
        rcases hu_eq with rfl | rfl <;> rcases hv with rfl | rfl
        · exact absurd rfl hvu
        · exact Nat.dvd_gcd h1 h2
        · exact Nat.dvd_gcd h2 h1
        · exact absurd rfl hvu
      rw [hcop_u.gcd_eq_one] at hg
      exact hp.ne_one (Nat.dvd_one.mp hg)
    have h_val_eq : padicValNat p (oddPartNat u) = padicValNat p (Nat.factorial n) := by
      have hv := congrArg (padicValNat p) h_fac_odd
      rw [padicValNat.mul (oddPartNat_pos hu₁_pos).ne' (oddPartNat_pos hu₂_pos).ne',
          padicValNat_oddPartNat hp hp2 (Nat.factorial_pos n)] at hv
      rcases hu_eq with rfl | rfl
      · have h0 : padicValNat p (oddPartNat u₂) = 0 :=
          padicValNat.eq_zero_of_not_dvd (h_other_nd u₂ (Or.inr rfl) (by omega))
        omega
      · have h0 : padicValNat p (oddPartNat u₁) = 0 :=
          padicValNat.eq_zero_of_not_dvd (h_other_nd u₁ (Or.inl rfl) (by omega))
        omega
    have hmem : p ∈ Podd n ∨ p ∈ Peven n := by
      unfold Podd Peven
      simp only [Finset.mem_filter, Finset.mem_Icc]
      by_cases hodd : padicValNat p (Nat.factorial n) % 2 = 1
      · exact Or.inl ⟨⟨hp.two_le, h_dvd_n⟩, hp, hodd⟩
      · exact Or.inr ⟨⟨hp.two_le, h_dvd_n⟩, hp, by omega⟩
    exact ⟨h_val_eq, hmem⟩
  have h_decomp : ∀ u, (u = u₁ ∨ u = u₂) → oddPartNat u = B_part n u * (Z_star n u) ^ 2 := by
    intro u hu_eq
    have hu_pos : 0 < u := by rcases hu_eq with rfl | rfl <;> assumption
    apply Nat.eq_of_factorization_eq (oddPartNat_pos hu_pos).ne'
      (mul_pos (B_part_pos n u) (pow_pos (Z_star_pos n u) 2)).ne'
    intro p
    by_cases hp : p.Prime
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
          padicValNat.mul (B_part_pos n u).ne' (pow_ne_zero 2 (Z_star_pos n u).ne'),
          padicValNat_pow_eq]
      have hB_val : padicValNat p (B_part n u) =
          if p ∈ (Podd n).filter (fun q => 3 ≤ q ∧ q ∣ oddPartNat u) then padicValNat p (Nat.factorial n) else 0 := by
        unfold B_part
        rw [padicValNat_prod_eq (fun q hq => pow_ne_zero _ (by have := (Finset.mem_filter.mp hq).2.1; omega))]
        split_ifs with hmem
        · rw [Finset.sum_eq_single p]
          · rw [padicValNat_pow_eq, padicValNat_self, mul_one]
          · intro q hq hqp
            have hq_pr : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
            rw [padicValNat_pow_eq,
                padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm),
                mul_zero]
          · intro habs; exact absurd hmem habs
        · apply Finset.sum_eq_zero
          intro q hq
          have hqp : q ≠ p := fun h => hmem (h ▸ hq)
          have hq_pr : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
          rw [padicValNat_pow_eq,
              padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm),
              mul_zero]
      have hZ_val : padicValNat p (Z_star n u) =
          if p ∈ (Peven n).filter (fun q => 3 ≤ q ∧ q ∣ oddPartNat u) then padicValNat p (Nat.factorial n) / 2 else 0 := by
        unfold Z_star
        rw [padicValNat_prod_eq (fun q hq => pow_ne_zero _ (by have := (Finset.mem_filter.mp hq).2.1; omega))]
        split_ifs with hmem
        · rw [Finset.sum_eq_single p]
          · rw [padicValNat_pow_eq, padicValNat_self, mul_one]
          · intro q hq hqp
            have hq_pr : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
            rw [padicValNat_pow_eq,
                padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm),
                mul_zero]
          · intro habs; exact absurd hmem habs
        · apply Finset.sum_eq_zero
          intro q hq
          have hqp : q ≠ p := fun h => hmem (h ▸ hq)
          have hq_pr : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
          rw [padicValNat_pow_eq,
              padicValNat.eq_zero_of_not_dvd (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hd).symm),
              mul_zero]
      rw [hB_val, hZ_val]
      by_cases hp2 : p = 2
      · subst hp2
        have hnd : ¬ 2 ∣ oddPartNat u := oddPartNat_not_dvd_two hu_pos
        rw [padicValNat.eq_zero_of_not_dvd hnd]
        simp
      · have hp3 : 3 ≤ p := by have := hp.two_le; omega
        by_cases hpu : p ∣ oddPartNat u
        · have ⟨hval, hmem⟩ := hp_val_u p u hp hp3 hpu hu_eq
          rw [hval]
          rcases hmem with hm1 | hm2
          · have hnot2 : p ∉ Peven n := by
              intro hm2
              have h1 := (Finset.mem_filter.mp hm1).2.2
              have h2 := (Finset.mem_filter.mp hm2).2.2
              omega
            simp [Finset.mem_filter, hm1, hnot2, hp3, hpu]
          · have hnot1 : p ∉ Podd n := by
              intro hm1
              have h1 := (Finset.mem_filter.mp hm1).2.2
              have h2 := (Finset.mem_filter.mp hm2).2.2
              omega
            have heven : padicValNat p (Nat.factorial n) % 2 = 0 := (Finset.mem_filter.mp hm2).2.2
            simp [Finset.mem_filter, hm2, hnot1, hp3, hpu]
            omega
        · rw [padicValNat.eq_zero_of_not_dvd hpu]
          simp [Finset.mem_filter, hpu]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  refine ⟨h_decomp u₁ (Or.inl rfl), h_decomp u₂ (Or.inr rfl), ?_⟩
  have h_disj : Disjoint ((Podd n).filter (fun p => 3 ≤ p ∧ p ∣ oddPartNat u₁))
      ((Podd n).filter (fun p => 3 ≤ p ∧ p ∣ oddPartNat u₂)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (Finset.mem_filter.mp hp1).2.2
    have h2 := (Finset.mem_filter.mp hp2).2.2
    have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1).2.1
    have hg : p ∣ Nat.gcd u₁ u₂ := Nat.dvd_gcd (dvd_trans h1 oddPartNat_dvd) (dvd_trans h2 oddPartNat_dvd)
    rw [hcop_u.gcd_eq_one] at hg
    exact hp_pr.ne_one (Nat.dvd_one.mp hg)
  have h_union : ((Podd n).filter (fun p => 3 ≤ p ∧ p ∣ oddPartNat u₁)) ∪
      ((Podd n).filter (fun p => 3 ≤ p ∧ p ∣ oddPartNat u₂)) = (Podd n).filter (3 ≤ ·) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hp, hp3, _⟩ | ⟨hp, hp3, _⟩) <;> exact ⟨hp, hp3⟩
    · rintro ⟨hp, hp3⟩
      have hp_pr : p.Prime := (Finset.mem_filter.mp hp).2.1
      have hp_le : p ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      have hp2 : p ≠ 2 := by omega
      have hp_dvd_fac : p ∣ oddPartNat (Nat.factorial n) := by
        have h1 : p ∣ Nat.factorial n := hp_pr.dvd_factorial.mpr hp_le
        have hcop2 : Nat.Coprime p (2 ^ padicValNat 2 (Nat.factorial n)) :=
          Nat.Coprime.pow_right _ ((Nat.coprime_primes hp_pr Nat.prime_two).mpr hp2)
        rw [← oddPartNat_mul_two_pow (Nat.factorial_pos n)] at h1
        exact hcop2.dvd_of_dvd_mul_right h1
      rw [← h_fac_odd] at hp_dvd_fac
      rcases hp_pr.dvd_mul.mp hp_dvd_fac with h1 | h2
      · exact Or.inl ⟨hp, hp3, h1⟩
      · exact Or.inr ⟨hp, hp3, h2⟩
  unfold B_part B_star5
  rw [← Finset.prod_union h_disj, h_union]

/-- **Theorem 5.2(i) — Reciprocal Cross-Symmetry Laws (eq. 5.4)**:
For any solution `(n, m)` to `n! + 1 = m^2` with `n ≥ 4`,
`log B^{(2)} - log((Z₁^*)^2) = (1/2)((w₂^{(1)} - w₂^{(2)}) log 2 - Δ_parity^*(n)) + O(exp(-(1/3) n log n))`
and symmetrically for `log B^{(1)} - log((Z₂^*)^2)`. -/
theorem thm_5_2_part1_cross_symmetry :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ n m : ℕ, N₀ ≤ n →
      Nat.factorial n + 1 = m ^ 2 →
      let u₁ := (m - 1) / 2
      let u₂ := (m + 1) / 2
      let w₂₁ := padicValNat 2 u₁
      let w₂₂ := padicValNat 2 u₂
      |Real.log (B_part n u₂ : ℝ) - Real.log ((Z_star n u₁ : ℝ) ^ 2) -
        (1 / 2 : ℝ) * (((w₂₁ : ℝ) - (w₂₂ : ℝ)) * Real.log 2 - Delta_parity_odd n)| ≤
        C * Real.exp (-(1 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) ∧
      |Real.log (B_part n u₁ : ℝ) - Real.log ((Z_star n u₂ : ℝ) ^ 2) -
        (1 / 2 : ℝ) * (((w₂₂ : ℝ) - (w₂₁ : ℝ)) * Real.log 2 - Delta_parity_odd n)| ≤
        C * Real.exp (-(1 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) := by
  refine ⟨4, by norm_num, 25, by omega, ?_⟩
  intro n m hn hm
  have ⟨hu₁_pos, hu₂_pos, _, _, h4mul, _, _⟩ := brocard_u1_u2_rel (by omega) hm
  set u₁ := (m - 1) / 2
  set u₂ := (m + 1) / 2
  set w₂₁ := padicValNat 2 u₁
  set w₂₂ := padicValNat 2 u₂
  have ⟨h_dec1, h_dec2, hB_prod⟩ := oddPartNat_u_eq_B_mul_Z_sq (by omega) hm
  have hv2_rel : padicValNat 2 (Nat.factorial n) = 2 + w₂₁ + w₂₂ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h4u : 4 * (u₁ * u₂) = Nat.factorial n := by linarith
    have hv2 := congrArg (padicValNat 2) h4u
    rw [padicValNat.mul (by norm_num) (mul_pos hu₁_pos hu₂_pos).ne',
        padicValNat.mul hu₁_pos.ne' hu₂_pos.ne',
        show padicValNat 2 4 = 2 from by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat_pow_eq, padicValNat_self]; norm_num] at hv2
    exact hv2.symm
  have hlog_Bstar : Real.log (B_star5 n : ℝ) =
      (1 / 2 : ℝ) * (Real.log (Nat.factorial n : ℝ) - Delta_parity_odd n -
        (padicValNat 2 (Nat.factorial n) : ℝ) * Real.log 2) := by
    have hAB := A_star5_mul_B_star5 n
    have h_odd_fac := oddPartNat_mul_two_pow (Nat.factorial_pos n)
    have h_eq_nat : A_star5 n * B_star5 n * 2 ^ padicValNat 2 (Nat.factorial n) = Nat.factorial n := by
      rw [hAB, h_odd_fac]
    have h_eq_real : (A_star5 n : ℝ) * (B_star5 n : ℝ) * (2 : ℝ) ^ padicValNat 2 (Nat.factorial n) =
        (Nat.factorial n : ℝ) := by exact_mod_cast h_eq_nat
    have hlog := congrArg Real.log h_eq_real
    rw [Real.log_mul (mul_pos (by exact_mod_cast A_star5_pos n) (by exact_mod_cast B_star5_pos n)).ne'
          (pow_ne_zero _ (by norm_num)),
        Real.log_mul (by exact_mod_cast (A_star5_pos n).ne') (by exact_mod_cast (B_star5_pos n).ne'),
        Real.log_pow] at hlog
    unfold Delta_parity_odd
    linarith
  have hlog_B12 : Real.log (B_part n u₁ : ℝ) + Real.log (B_part n u₂ : ℝ) = Real.log (B_star5 n : ℝ) := by
    have h_r : (B_part n u₁ : ℝ) * (B_part n u₂ : ℝ) = (B_star5 n : ℝ) := by exact_mod_cast hB_prod
    rw [← Real.log_mul (by exact_mod_cast (B_part_pos n u₁).ne') (by exact_mod_cast (B_part_pos n u₂).ne'), h_r]
  have hlog_u1 : Real.log (u₁ : ℝ) - (w₂₁ : ℝ) * Real.log 2 =
      Real.log (B_part n u₁ : ℝ) + Real.log ((Z_star n u₁ : ℝ) ^ 2) := by
    have h1 : (oddPartNat u₁ : ℝ) * (2 : ℝ) ^ w₂₁ = (u₁ : ℝ) := by
      exact_mod_cast oddPartNat_mul_two_pow hu₁_pos
    have h2 : (oddPartNat u₁ : ℝ) = (B_part n u₁ : ℝ) * (Z_star n u₁ : ℝ) ^ 2 := by
      exact_mod_cast h_dec1
    have hl1 := congrArg Real.log h1
    rw [Real.log_mul (by exact_mod_cast (oddPartNat_pos hu₁_pos).ne') (pow_ne_zero _ (by norm_num)),
        Real.log_pow] at hl1
    have hl2 := congrArg Real.log h2
    rw [Real.log_mul (by exact_mod_cast (B_part_pos n u₁).ne') (pow_ne_zero 2 (by exact_mod_cast (Z_star_pos n u₁).ne'))] at hl2
    linarith
  have hlog_u2 : Real.log (u₂ : ℝ) - (w₂₂ : ℝ) * Real.log 2 =
      Real.log (B_part n u₂ : ℝ) + Real.log ((Z_star n u₂ : ℝ) ^ 2) := by
    have h1 : (oddPartNat u₂ : ℝ) * (2 : ℝ) ^ w₂₂ = (u₂ : ℝ) := by
      exact_mod_cast oddPartNat_mul_two_pow hu₂_pos
    have h2 : (oddPartNat u₂ : ℝ) = (B_part n u₂ : ℝ) * (Z_star n u₂ : ℝ) ^ 2 := by
      exact_mod_cast h_dec2
    have hl1 := congrArg Real.log h1
    rw [Real.log_mul (by exact_mod_cast (oddPartNat_pos hu₂_pos).ne') (pow_ne_zero _ (by norm_num)),
        Real.log_pow] at hl1
    have hl2 := congrArg Real.log h2
    rw [Real.log_mul (by exact_mod_cast (B_part_pos n u₂).ne') (pow_ne_zero 2 (by exact_mod_cast (Z_star_pos n u₂).ne'))] at hl2
    linarith
  have h_fac_lb : (2 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤ Real.log (Nat.factorial n : ℝ) := by
    have h1 := n_log_n_sub_n_le_log_factorial n (by omega)
    have hlog : 3 ≤ Real.log (n : ℝ) := by
      have hexp3 : Real.exp 3 < 25 := by
        have h_e : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
        have h_e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; ring_nf
        nlinarith
      exact (Real.le_log_iff_exp_le (by positivity)).mpr (le_trans hexp3.le (by exact_mod_cast hn))
    nlinarith
  have hm_lb : Real.exp ((1 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) ≤ (m : ℝ) := by
    have hsq : Real.exp ((2 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) ≤ (m : ℝ) ^ 2 := by
      have hfac_exp : Real.exp ((2 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) ≤ (Nat.factorial n : ℝ) :=
        (Real.exp_le_iff_le_log (by exact_mod_cast Nat.factorial_pos n)).mpr h_fac_lb
      have hm2 : (Nat.factorial n : ℝ) + 1 = (m : ℝ) ^ 2 := by exact_mod_cast hm
      linarith
    have h_half : Real.exp ((1 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) ^ 2 =
        Real.exp ((2 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    nlinarith [Real.exp_pos ((1 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)), show (0 : ℝ) ≤ (m : ℝ) by positivity]
  have hu_err : |Real.log (u₁ : ℝ) - ((1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ) - Real.log 2)| ≤
      4 * Real.exp (-(1 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) ∧
      |Real.log (u₂ : ℝ) - ((1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ) - Real.log 2)| ≤
      4 * Real.exp (-(1 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) := by
    have h_sum_u : Real.log (u₁ : ℝ) + Real.log (u₂ : ℝ) = Real.log (Nat.factorial n : ℝ) - 2 * Real.log 2 := by
      have h4r : 4 * (u₁ : ℝ) * (u₂ : ℝ) = (Nat.factorial n : ℝ) := by exact_mod_cast h4mul
      have hl := congrArg Real.log h4r
      rw [Real.log_mul (by positivity) (by exact_mod_cast hu₂_pos.ne'),
          Real.log_mul (by norm_num) (by exact_mod_cast hu₁_pos.ne'),
          show Real.log 4 = 2 * Real.log 2 from by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num] at hl
      linarith
    have h_diff_u_nn : 0 ≤ Real.log (u₂ : ℝ) - Real.log (u₁ : ℝ) := by
      have : (u₁ : ℝ) ≤ (u₂ : ℝ) := by exact_mod_cast (by omega : u₁ ≤ u₂)
      linarith [Real.log_le_log (by exact_mod_cast hu₁_pos) this]
    have h_diff_u_ub : Real.log (u₂ : ℝ) - Real.log (u₁ : ℝ) ≤ 1 / (u₁ : ℝ) := by
      rw [← Real.log_div (by exact_mod_cast hu₂_pos.ne') (by exact_mod_cast hu₁_pos.ne')]
      have hdiv : (u₂ : ℝ) / (u₁ : ℝ) = 1 + 1 / (u₁ : ℝ) := by
        have : (u₂ : ℝ) = (u₁ : ℝ) + 1 := by exact_mod_cast (by omega : u₂ = u₁ + 1)
        rw [this]; field_simp [show (u₁ : ℝ) ≠ 0 by exact_mod_cast hu₁_pos.ne']
      rw [hdiv]
      exact Real.log_one_add_le (by positivity)
    have h_u1_lb : (m : ℝ) / 4 ≤ (u₁ : ℝ) := by
      have : 2 * u₁ = m - 1 := by omega
      have : (m : ℝ) ≤ 4 * (u₁ : ℝ) := by
        have : m ≤ 4 * u₁ := by omega
        exact_mod_cast this
      linarith
    have h_inv_ub : 1 / (u₁ : ℝ) ≤ 4 * Real.exp (-(1 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) := by
      have hexp_inv : Real.exp (-(1 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) =
          (Real.exp ((1 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)))⁻¹ := by
        rw [← Real.exp_neg]; ring_nf
      rw [hexp_inv]
      calc 1 / (u₁ : ℝ) ≤ 1 / ((m : ℝ) / 4) := one_div_le_one_div_of_le (by positivity) h_u1_lb
        _ = 4 * (m : ℝ)⁻¹ := by ring
        _ ≤ 4 * (Real.exp ((1 / 3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)))⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact inv_anti₀ (Real.exp_pos _) hm_lb
    have h_half1 : Real.log (u₁ : ℝ) - ((1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ) - Real.log 2) =
        -(1 / 2 : ℝ) * (Real.log (u₂ : ℝ) - Real.log (u₁ : ℝ)) := by linarith
    have h_half2 : Real.log (u₂ : ℝ) - ((1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ) - Real.log 2) =
        (1 / 2 : ℝ) * (Real.log (u₂ : ℝ) - Real.log (u₁ : ℝ)) := by linarith
    rw [h_half1, h_half2, abs_neg, abs_mul, abs_of_nonneg (by norm_num), abs_of_nonneg h_diff_u_nn]
    constructor <;> linarith
  have hv2_r : (padicValNat 2 (Nat.factorial n) : ℝ) = 2 + (w₂₁ : ℝ) + (w₂₂ : ℝ) := by
    exact_mod_cast hv2_rel
  have h_id1 : Real.log (B_part n u₂ : ℝ) - Real.log ((Z_star n u₁ : ℝ) ^ 2) -
      (1 / 2 : ℝ) * (((w₂₁ : ℝ) - (w₂₂ : ℝ)) * Real.log 2 - Delta_parity_odd n) =
      -(Real.log (u₁ : ℝ) - ((1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ) - Real.log 2)) := by
    rw [hv2_r] at hlog_Bstar
    linarith
  have h_id2 : Real.log (B_part n u₁ : ℝ) - Real.log ((Z_star n u₂ : ℝ) ^ 2) -
      (1 / 2 : ℝ) * (((w₂₂ : ℝ) - (w₂₁ : ℝ)) * Real.log 2 - Delta_parity_odd n) =
      -(Real.log (u₂ : ℝ) - ((1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ) - Real.log 2)) := by
    rw [hv2_r] at hlog_Bstar
    linarith
  rw [h_id1, h_id2, abs_neg, abs_neg]
  exact hu_err

/-! ### Theorem 5.2(i): Radical Bounds for `m - 1` and `m + 1` (Eq. 5.5) -/

theorem thm_5_2_part1_radical_bounds (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 4) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ n m : ℕ, N₀ ≤ n →
      Nat.factorial n + 1 = m ^ 2 →
      (∃ p : ℕ, p.Prime ∧ p ∣ (m - 1) ∧ (n : ℝ) ^ (1 / 2 - ε) ≤ (p : ℝ)) ∧
      (∃ p : ℕ, p.Prime ∧ p ∣ (m + 1) ∧ (n : ℝ) ^ (1 / 2 - ε) ≤ (p : ℝ)) ∧
      (n : ℝ) ^ (1 / 2 - ε) ≤ ((m - 1).primeFactors.card : ℝ) ∧
      (n : ℝ) ^ (1 / 2 - ε) ≤ ((m + 1).primeFactors.card : ℝ) ∧
      Real.exp ((n : ℝ) ^ (1 / 2 - ε)) ≤ ((∏ p ∈ (m - 1).primeFactors, p : ℕ) : ℝ) ∧
      Real.exp ((n : ℝ) ^ (1 / 2 - ε)) ≤ ((∏ p ∈ (m + 1).primeFactors, p : ℕ) : ℝ) := by
  set δ := ε / 2
  have hδ0 : 0 < δ := by linarith
  have hδ1 : δ < 1 / 8 := by linarith
  have h_band1 := multi_modulus_power_band_equidistribution 2 1 (by norm_num) 0 (1 / 2 - δ)
    le_rfl (by linarith) (by linarith)
  have h_band0 := multi_modulus_power_band_equidistribution 2 0 (by norm_num) 0 (1 / 2 - δ)
    le_rfl (by linarith) (by linarith)
  have h_band_ev : ∀ᶠ n : ℕ in atTop,
      ∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
        p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ)),
        (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
      (1 / 2 - δ + δ / 10) * ((n : ℝ) * Real.log (n : ℝ)) := by
    have h1 := h_band1.bound (by positivity : (0 : ℝ) < δ / 20)
    have h0 := h_band0.bound (by positivity : (0 : ℝ) < δ / 20)
    filter_upwards [h1, h0, eventually_ge_atTop 2] with n hn1 hn0 hn2
    have hn_log_nn : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
    rw [Real.norm_of_nonneg hn_log_nn] at hn1 hn0
    have hb1 := (abs_le.mp (Real.norm_eq_abs _ ▸ hn1)).2
    have hb0 := (abs_le.mp (Real.norm_eq_abs _ ▸ hn0)).2
    have hsub : (1 / 2 - δ - 0) / ((2 : ℕ) : ℝ) = 1 / 4 - δ / 2 := by norm_num; ring
    rw [hsub] at hb1 hb0
    have h_split :
        (∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ)),
          (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) =
        (∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ) ∧
          padicValNat p (Nat.factorial n) ≡ 1 [MOD 2]),
          (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) +
        (∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ) ∧
          padicValNat p (Nat.factorial n) ≡ 0 [MOD 2]),
          (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) := by
      have hdisj : Disjoint
          ((Finset.Icc 2 n).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧
            (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ) ∧ padicValNat p (Nat.factorial n) ≡ 1 [MOD 2]))
          ((Finset.Icc 2 n).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧
            (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ) ∧ padicValNat p (Nat.factorial n) ≡ 0 [MOD 2])) := by
        rw [Finset.disjoint_left]
        intro p hp1 hp0
        have h1m := (Finset.mem_filter.mp hp1).2.2.2.2
        have h0m := (Finset.mem_filter.mp hp0).2.2.2.2
        simp [Nat.ModEq] at h1m h0m
        omega
      have hunion :
          ((Finset.Icc 2 n).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧
            (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ) ∧ padicValNat p (Nat.factorial n) ≡ 1 [MOD 2])) ∪
          ((Finset.Icc 2 n).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧
            (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ) ∧ padicValNat p (Nat.factorial n) ≡ 0 [MOD 2])) =
          (Finset.Icc 2 n).filter (fun p : ℕ => p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧
            (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ)) := by
        ext p
        simp only [Finset.mem_union, Finset.mem_filter, Nat.ModEq]
        tauto
      rw [← hunion, Finset.sum_union hdisj]
    rw [h_split]
    linarith
  have h_n_large : ∀ᶠ n : ℕ in atTop,
      25 ≤ n ∧
      (1 / 2 - δ / 4) * ((n : ℝ) * Real.log (n : ℝ)) ≤
        (1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ) - Real.log 2 - (n : ℝ) * Real.log 2 - 1 ∧
      (n : ℝ) ^ (1 / 2 - ε) ≤ (δ / 8) * (n : ℝ) ^ (1 / 2 - δ) ∧
      (n : ℝ) ^ (1 / 2 - ε) ≤ (δ / 8) * (1 / 2 - δ) * (n : ℝ) ^ (1 / 2 - δ) * Real.log (n : ℝ) ∧
      2 ≤ (n : ℝ) ^ (1 / 2 - δ) := by
    have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hrpow_δ : Tendsto (fun n : ℕ => (n : ℝ) ^ δ) atTop atTop :=
      (tendsto_rpow_atTop hδ0).comp tendsto_natCast_atTop_atTop
    have hrpow_half : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 - δ)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 / 2 - δ)).comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 25,
      hlog_inf.eventually (eventually_ge_atTop ((8 / δ) * (1 + 2 * Real.log 2))),
      hlog_inf.eventually (eventually_ge_atTop (1 / ((δ / 8) * (1 / 2 - δ)))),
      hrpow_δ.eventually (eventually_ge_atTop (8 / δ)),
      hrpow_half.eventually (eventually_ge_atTop 2)] with n hn25 hlog1 hlog2 hrpowδ hrpowh
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hfac_lb := n_log_n_sub_n_le_log_factorial n (by omega)
    have h_err_ub : (1 / 2 : ℝ) * (n : ℝ) + Real.log 2 + (n : ℝ) * Real.log 2 + 1 ≤
        (δ / 4) * ((n : ℝ) * Real.log (n : ℝ)) := by
      have hlog_ge : (8 / δ) * (1 + 2 * Real.log 2) ≤ Real.log (n : ℝ) := hlog1
      have h1 : 1 + 2 * Real.log 2 ≤ (δ / 8) * Real.log (n : ℝ) := by
        have := mul_le_mul_of_nonneg_left hlog_ge (by positivity : 0 ≤ δ / 8)
        have heq : (δ / 8) * ((8 / δ) * (1 + 2 * Real.log 2)) = 1 + 2 * Real.log 2 := by
          field_simp [hδ0.ne']
        linarith
      have h2 : (n : ℝ) * (1 + 2 * Real.log 2) ≤ (δ / 8) * ((n : ℝ) * Real.log (n : ℝ)) := by
        nlinarith
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith [show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast (by omega : 1 ≤ n)]
    have h_rpow_rel : (n : ℝ) ^ (1 / 2 - ε) * (n : ℝ) ^ δ = (n : ℝ) ^ (1 / 2 - δ) := by
      rw [← Real.rpow_add hn_pos]
      congr 1; ring
    have h_eps_le : (n : ℝ) ^ (1 / 2 - ε) ≤ (δ / 8) * (n : ℝ) ^ (1 / 2 - δ) := by
      rw [← h_rpow_rel]
      have : (n : ℝ) ^ (1 / 2 - ε) * (8 / δ) ≤ (n : ℝ) ^ (1 / 2 - ε) * (n : ℝ) ^ δ :=
        mul_le_mul_of_nonneg_left hrpowδ (Real.rpow_nonneg hn_pos.le _)
      have heq : (δ / 8) * ((n : ℝ) ^ (1 / 2 - ε) * (8 / δ)) = (n : ℝ) ^ (1 / 2 - ε) := by
        field_simp [hδ0.ne']
      linarith
    have h_eps_log_le : (n : ℝ) ^ (1 / 2 - ε) ≤ (δ / 8) * (1 / 2 - δ) * (n : ℝ) ^ (1 / 2 - δ) * Real.log (n : ℝ) := by
      have h1 : 1 ≤ (δ / 8) * (1 / 2 - δ) * Real.log (n : ℝ) := by
        have hpos : 0 < (δ / 8) * (1 / 2 - δ) := by nlinarith
        have := mul_le_mul_of_nonneg_left hlog2 hpos.le
        have heq : (δ / 8) * (1 / 2 - δ) * (1 / ((δ / 8) * (1 / 2 - δ))) = 1 := by
          field_simp [hpos.ne']
        linarith
      have h_le_d : (n : ℝ) ^ (1 / 2 - ε) ≤ (n : ℝ) ^ (1 / 2 - δ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
      calc (n : ℝ) ^ (1 / 2 - ε) ≤ (n : ℝ) ^ (1 / 2 - δ) * 1 := by linarith
        _ ≤ (n : ℝ) ^ (1 / 2 - δ) * ((δ / 8) * (1 / 2 - δ) * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hn_pos.le _)
        _ = _ := by ring
    exact ⟨hn25, by linarith, h_eps_le, h_eps_log_le, hrpowh⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (h_band_ev.and h_n_large)
  refine ⟨max 4 N₀, le_max_left _ _, fun n m hn hm => ?_⟩
  obtain ⟨hband, hn25, h_lb_tot, h_eps_le, h_eps_log_le, hrpowh⟩ := hN₀ n (le_trans (le_max_right _ _) hn)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have ⟨hm_odd, hm3⟩ := brocard_m_odd (by omega) hm
  have ⟨hu₁_pos, hu₂_pos, _, _, h4mul, _, _⟩ := brocard_u1_u2_rel (by omega) hm
  set u₁ := (m - 1) / 2
  set u₂ := (m + 1) / 2
  have hu_bounds : ∀ u : ℕ, 0 < u → u ∣ Nat.factorial n →
      (1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ) - Real.log 2 - 1 ≤ Real.log (u : ℝ) →
      (∃ p : ℕ, p.Prime ∧ p ∣ u ∧ (n : ℝ) ^ (1 / 2 - ε) ≤ (p : ℝ)) ∧
      (n : ℝ) ^ (1 / 2 - ε) ≤ (u.primeFactors.card : ℝ) ∧
      Real.exp ((n : ℝ) ^ (1 / 2 - ε)) ≤ ((∏ p ∈ u.primeFactors, p : ℕ) : ℝ) := by
    intro u hu_pos hu_dvd_fac hlog_u_lb
    have hlog_u_odd : (1 / 2 - δ / 4) * ((n : ℝ) * Real.log (n : ℝ)) ≤
        Real.log (oddPartNat u : ℝ) := by
      have hv2_le : (padicValNat 2 u : ℝ) ≤ (n : ℝ) := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hd : padicValNat 2 u ≤ padicValNat 2 (Nat.factorial n) := by
          have h1 : 2 ^ padicValNat 2 u ∣ Nat.factorial n := dvd_trans pow_padicValNat_dvd hu_dvd_fac
          exact (padicValNat_dvd_iff_le (Nat.factorial_pos n).ne').mp h1
        have hleg : (2 - 1) * padicValNat 2 (Nat.factorial n) = n - (Nat.digits 2 n).sum :=
          Nat.sub_one_mul_padicValNat_factorial (p := 2) n
        have : padicValNat 2 (Nat.factorial n) ≤ n := by omega
        exact_mod_cast le_trans hd this
      have h1 : (oddPartNat u : ℝ) * (2 : ℝ) ^ padicValNat 2 u = (u : ℝ) := by
        exact_mod_cast oddPartNat_mul_two_pow hu_pos
      have hl := congrArg Real.log h1
      rw [Real.log_mul (by exact_mod_cast (oddPartNat_pos hu_pos).ne') (pow_ne_zero _ (by norm_num)),
          Real.log_pow] at hl
      have hlog2_nn : 0 ≤ Real.log 2 := Real.log_pos (by norm_num) |>.le
      nlinarith
    have h_sum_odd : Real.log (oddPartNat u : ℝ) ≤
        ∑ p ∈ (oddPartNat u).primeFactors, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
      have hfac_eq := Nat.prod_factorization_pow_eq_self (oddPartNat_pos hu_pos).ne'
      have h_r : (∏ p ∈ (oddPartNat u).primeFactors, (p : ℝ) ^ (oddPartNat u).factorization p) =
          (oddPartNat u : ℝ) := by
        exact_mod_cast hfac_eq
      rw [← h_r, Real.log_prod (fun p hp => pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]
      apply Finset.sum_le_sum
      intro p hp
      have hp_pr := Nat.prime_of_mem_primeFactors hp
      haveI : Fact p.Prime := ⟨hp_pr⟩
      rw [Real.log_pow, Nat.factorization_def _ hp_pr]
      have h_vp_le : padicValNat p (oddPartNat u) ≤ padicValNat p (Nat.factorial n) := by
        have hd : p ^ padicValNat p (oddPartNat u) ∣ Nat.factorial n :=
          dvd_trans pow_padicValNat_dvd (dvd_trans oddPartNat_dvd hu_dvd_fac)
        exact (padicValNat_dvd_iff_le (Nat.factorial_pos n).ne').mp hd
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h_vp_le) (Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le))
    set S_lo := (oddPartNat u).primeFactors.filter (fun p => (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ))
    set S_hi := (oddPartNat u).primeFactors.filter (fun p => (n : ℝ) ^ (1 / 2 - δ) < (p : ℝ))
    have h_part : (oddPartNat u).primeFactors = S_lo ∪ S_hi := by
      ext p; simp only [S_lo, S_hi, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hp
        by_cases hle : (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ)
        · exact Or.inl ⟨hp, hle⟩
        · exact Or.inr ⟨hp, lt_of_not_ge hle⟩
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    have h_disj : Disjoint S_lo S_hi := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 := (Finset.mem_filter.mp hp1).2
      have h2 := (Finset.mem_filter.mp hp2).2
      linarith
    have hS_lo_le :
        (∑ p ∈ S_lo, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) ≤
        (1 / 2 - δ + δ / 10) * ((n : ℝ) * Real.log (n : ℝ)) := by
      have hsub : S_lo ⊆ (Finset.Icc 2 n).filter (fun p : ℕ =>
          p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ)) := by
        intro p hp
        have hp_mem := (Finset.mem_filter.mp hp).1
        have hp_le_r := (Finset.mem_filter.mp hp).2
        have hp_pr := Nat.prime_of_mem_primeFactors hp_mem
        have hp_dvd_fac : p ∣ Nat.factorial n :=
          dvd_trans (Nat.dvd_of_mem_primeFactors hp_mem) (dvd_trans oddPartNat_dvd hu_dvd_fac)
        have hp_le_n : p ≤ n := hp_pr.dvd_factorial.mp hp_dvd_fac
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_pr.two_le, hp_le_n⟩, hp_pr, ?_, hp_le_r⟩
        rw [Real.rpow_zero]
        exact_mod_cast hp_pr.one_lt
      have hsum_le :
          (∑ p ∈ S_lo, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) ≤
          ∑ p ∈ (Finset.Icc 2 n).filter (fun p : ℕ =>
            p.Prime ∧ (n : ℝ) ^ (0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 / 2 - δ)),
            (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp _
        have hp_pr := (Finset.mem_filter.mp hp).2.1
        exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le))
      exact le_trans hsum_le hband
    have hS_hi_lb : (δ / 2) * ((n : ℝ) * Real.log (n : ℝ)) ≤
        ∑ p ∈ S_hi, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) := by
      have h_eq : (∑ p ∈ (oddPartNat u).primeFactors, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) =
          (∑ p ∈ S_lo, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) +
          (∑ p ∈ S_hi, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) := by
        rw [h_part, Finset.sum_union h_disj]
      linarith
    have h_term_ub : ∀ p ∈ S_hi,
        (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
        2 * (n : ℝ) ^ (1 / 2 + δ) * Real.log (n : ℝ) := by
      intro p hp
      have hp_mem := (Finset.mem_filter.mp hp).1
      have hp_gt := (Finset.mem_filter.mp hp).2
      have hp_pr := Nat.prime_of_mem_primeFactors hp_mem
      haveI : Fact p.Prime := ⟨hp_pr⟩
      have hp_dvd_fac : p ∣ Nat.factorial n :=
        dvd_trans (Nat.dvd_of_mem_primeFactors hp_mem) (dvd_trans oddPartNat_dvd hu_dvd_fac)
      have hp_le_n : p ≤ n := hp_pr.dvd_factorial.mp hp_dvd_fac
      have hleg : (p - 1) * padicValNat p (Nat.factorial n) = n - (Nat.digits p n).sum :=
        Nat.sub_one_mul_padicValNat_factorial (p := p) n
      have h_mul_le : ((p - 1 : ℕ) : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (by omega : (p - 1) * padicValNat p (Nat.factorial n) ≤ n)
      have hp_ge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_pr.two_le
      have h_half_p : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
      have hp1_eq : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        have := hp_pr.one_lt.le; exact_mod_cast Nat.cast_sub this
      rw [hp1_eq] at h_mul_le
      have h_p_vp : (p : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) ≤ 2 * (n : ℝ) := by
        have : ((p : ℝ) / 2) * (padicValNat p (Nat.factorial n) : ℝ) ≤
            ((p : ℝ) - 1) * (padicValNat p (Nat.factorial n) : ℝ) :=
          mul_le_mul_of_nonneg_right h_half_p (Nat.cast_nonneg _)
        linarith
      have h_vp_ub : (padicValNat p (Nat.factorial n) : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + δ) := by
        have h_pow_mul : (n : ℝ) ^ (1 / 2 - δ) * (n : ℝ) ^ (1 / 2 + δ) = (n : ℝ) := by
          rw [← Real.rpow_add hn_pos]; norm_num
        have h1 : (n : ℝ) ^ (1 / 2 - δ) * (padicValNat p (Nat.factorial n) : ℝ) ≤
            (p : ℝ) * (padicValNat p (Nat.factorial n) : ℝ) :=
          mul_le_mul_of_nonneg_right hp_gt.le (Nat.cast_nonneg _)
        have h2 : (n : ℝ) ^ (1 / 2 - δ) * (padicValNat p (Nat.factorial n) : ℝ) ≤
            (n : ℝ) ^ (1 / 2 - δ) * (2 * (n : ℝ) ^ (1 / 2 + δ)) := by
          calc _ ≤ 2 * (n : ℝ) := le_trans h1 h_p_vp
            _ = (n : ℝ) ^ (1 / 2 - δ) * (2 * (n : ℝ) ^ (1 / 2 + δ)) := by linarith [h_pow_mul]
        exact le_of_mul_le_mul_left h2 (Real.rpow_pos_of_pos hn_pos _)
      have hlog_le : Real.log (p : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast hp_pr.pos) (by exact_mod_cast hp_le_n)
      have hlog_p_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)
      exact mul_le_mul h_vp_ub hlog_le hlog_p_nn (by positivity)
    have hS_hi_ub :
        (∑ p ∈ S_hi, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) ≤
        (S_hi.card : ℝ) * (2 * (n : ℝ) ^ (1 / 2 + δ) * Real.log (n : ℝ)) := by
      calc _ ≤ ∑ _p ∈ S_hi, (2 * (n : ℝ) ^ (1 / 2 + δ) * Real.log (n : ℝ)) := Finset.sum_le_sum h_term_ub
        _ = (S_hi.card : ℝ) * (2 * (n : ℝ) ^ (1 / 2 + δ) * Real.log (n : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    have hlog_n_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hS_hi_ne : S_hi.Nonempty := by
      by_contra h_emp
      rw [Finset.not_nonempty_iff_eq_empty] at h_emp
      rw [h_emp, Finset.sum_empty] at hS_hi_lb
      have : 0 < (δ / 2) * ((n : ℝ) * Real.log (n : ℝ)) := by positivity
      linarith
    have hp_exists : ∃ p : ℕ, p.Prime ∧ p ∣ u ∧ (n : ℝ) ^ (1 / 2 - ε) ≤ (p : ℝ) := by
      obtain ⟨p, hp⟩ := hS_hi_ne
      have hp_mem := (Finset.mem_filter.mp hp).1
      have hp_gt := (Finset.mem_filter.mp hp).2
      have hp_pr := Nat.prime_of_mem_primeFactors hp_mem
      have hp_dvd : p ∣ u := dvd_trans (Nat.dvd_of_mem_primeFactors hp_mem) oddPartNat_dvd
      have h_rpow : (n : ℝ) ^ (1 / 2 - ε) ≤ (n : ℝ) ^ (1 / 2 - δ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
      exact ⟨p, hp_pr, hp_dvd, le_trans h_rpow hp_gt.le⟩
    have hcard_lb : (δ / 4) * (n : ℝ) ^ (1 / 2 - δ) ≤ (S_hi.card : ℝ) := by
      have h1 : (δ / 2) * ((n : ℝ) * Real.log (n : ℝ)) ≤
          (S_hi.card : ℝ) * (2 * (n : ℝ) ^ (1 / 2 + δ) * Real.log (n : ℝ)) := le_trans hS_hi_lb hS_hi_ub
      have h_pow_mul : (n : ℝ) ^ (1 / 2 - δ) * (n : ℝ) ^ (1 / 2 + δ) = (n : ℝ) := by
        rw [← Real.rpow_add hn_pos]; norm_num
      have h2 : (δ / 4) * (n : ℝ) ^ (1 / 2 - δ) * (2 * (n : ℝ) ^ (1 / 2 + δ) * Real.log (n : ℝ)) ≤
          (S_hi.card : ℝ) * (2 * (n : ℝ) ^ (1 / 2 + δ) * Real.log (n : ℝ)) := by
        have heq : (δ / 4) * (n : ℝ) ^ (1 / 2 - δ) * (2 * (n : ℝ) ^ (1 / 2 + δ) * Real.log (n : ℝ)) =
            (δ / 2) * ((n : ℝ) * Real.log (n : ℝ)) := by
          calc _ = (δ / 2) * (((n : ℝ) ^ (1 / 2 - δ) * (n : ℝ) ^ (1 / 2 + δ)) * Real.log (n : ℝ)) := by ring
            _ = (δ / 2) * ((n : ℝ) * Real.log (n : ℝ)) := by rw [h_pow_mul]; ring
        linarith
      exact le_of_mul_le_mul_right h2 (by positivity)
    have hsub_u : S_hi ⊆ u.primeFactors := by
      intro p hp
      have hp_mem := (Finset.mem_filter.mp hp).1
      have hp_pr := Nat.prime_of_mem_primeFactors hp_mem
      exact Nat.mem_primeFactors.mpr ⟨hp_pr, dvd_trans (Nat.dvd_of_mem_primeFactors hp_mem) oddPartNat_dvd, hu_pos.ne'⟩
    have homega_lb : (n : ℝ) ^ (1 / 2 - ε) ≤ (u.primeFactors.card : ℝ) := by
      have hcard_le : (S_hi.card : ℝ) ≤ (u.primeFactors.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub_u
      linarith
    have hrad_lb : Real.exp ((n : ℝ) ^ (1 / 2 - ε)) ≤ ((∏ p ∈ u.primeFactors, p : ℕ) : ℝ) := by
      have hprod_ge : (∏ p ∈ S_hi, (p : ℝ)) ≤ ((∏ p ∈ u.primeFactors, p : ℕ) : ℝ) := by
        have h1 : ∏ p ∈ S_hi, p ∣ ∏ p ∈ u.primeFactors, p :=
          Finset.prod_dvd_prod_of_subset S_hi u.primeFactors id hsub_u
        have hpos_prod : 0 < ∏ p ∈ u.primeFactors, p :=
          Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
        exact_mod_cast Nat.le_of_dvd hpos_prod h1
      have hlog_prod_lb : (n : ℝ) ^ (1 / 2 - ε) ≤ Real.log (∏ p ∈ S_hi, (p : ℝ)) := by
        rw [Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero)]
        have h_each : ∀ p ∈ S_hi, (1 / 2 - δ) * Real.log (n : ℝ) ≤ Real.log (p : ℝ) := by
          intro p hp
          have hp_gt := (Finset.mem_filter.mp hp).2
          have h1 : Real.log ((n : ℝ) ^ (1 / 2 - δ)) ≤ Real.log (p : ℝ) :=
            Real.log_le_log (Real.rpow_pos_of_pos hn_pos _) hp_gt.le
          rwa [Real.log_rpow hn_pos] at h1
        calc (n : ℝ) ^ (1 / 2 - ε)
            ≤ (δ / 8) * (1 / 2 - δ) * (n : ℝ) ^ (1 / 2 - δ) * Real.log (n : ℝ) := h_eps_log_le
          _ ≤ (δ / 4) * (n : ℝ) ^ (1 / 2 - δ) * ((1 / 2 - δ) * Real.log (n : ℝ)) := by
            nlinarith [Real.rpow_nonneg hn_pos.le (1 / 2 - δ)]
          _ ≤ (S_hi.card : ℝ) * ((1 / 2 - δ) * Real.log (n : ℝ)) :=
            mul_le_mul_of_nonneg_right hcard_lb (by positivity)
          _ = ∑ _p ∈ S_hi, ((1 / 2 - δ) * Real.log (n : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ p ∈ S_hi, Real.log (p : ℝ) := Finset.sum_le_sum h_each
      have hpos_S : 0 < ∏ p ∈ S_hi, (p : ℝ) :=
        Finset.prod_pos (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)
      exact le_trans ((Real.exp_le_iff_le_log hpos_S).mpr hlog_prod_lb) hprod_ge
    exact ⟨hp_exists, homega_lb, hrad_lb⟩
  have hu₁_dvd : u₁ ∣ Nat.factorial n := ⟨4 * u₂, by linarith⟩
  have hu₂_dvd : u₂ ∣ Nat.factorial n := ⟨4 * u₁, by linarith⟩
  have hm_ge_sqrt : Real.sqrt (Nat.factorial n : ℝ) ≤ (m : ℝ) := by
    rw [Real.sqrt_le_left (by positivity)]
    exact_mod_cast (by omega : Nat.factorial n ≤ m ^ 2)
  have hlog_u1_lb : (1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ) - Real.log 2 - 1 ≤ Real.log (u₁ : ℝ) := by
    have h1 : (m : ℝ) ≤ 3 * (u₁ : ℝ) := by
      have : 2 * u₁ = m - 1 := by omega
      exact_mod_cast (by omega : m ≤ 3 * u₁)
    have hlog3 : Real.log 3 ≤ Real.log 2 + 1 := by
      have h3e : (3 : ℝ) ≤ 2 * Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hl := Real.log_le_log (by norm_num) h3e
      rwa [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at hl
    have hl := Real.log_le_log (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos n)) (le_trans hm_ge_sqrt h1)
    rw [Real.log_sqrt (by positivity), Real.log_mul (by norm_num) (by exact_mod_cast hu₁_pos.ne')] at hl
    linarith
  have hlog_u2_lb : (1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ) - Real.log 2 - 1 ≤ Real.log (u₂ : ℝ) := by
    have h1 : (u₁ : ℝ) ≤ (u₂ : ℝ) := by exact_mod_cast (by omega : u₁ ≤ u₂)
    exact le_trans hlog_u1_lb (Real.log_le_log (by exact_mod_cast hu₁_pos) h1)
  obtain ⟨⟨p₁, hp₁, hp₁_dvd, hp₁_ge⟩, hom₁, hrad₁⟩ := hu_bounds u₁ hu₁_pos hu₁_dvd hlog_u1_lb
  obtain ⟨⟨p₂, hp₂, hp₂_dvd, hp₂_ge⟩, hom₂, hrad₂⟩ := hu_bounds u₂ hu₂_pos hu₂_dvd hlog_u2_lb
  have hu₁_m : u₁ ∣ m - 1 := ⟨2, by omega⟩
  have hu₂_m : u₂ ∣ m + 1 := ⟨2, by omega⟩
  have hsub₁ : u₁.primeFactors ⊆ (m - 1).primeFactors := by
    intro p hp; have hp_pr := Nat.prime_of_mem_primeFactors hp
    exact Nat.mem_primeFactors.mpr ⟨hp_pr, dvd_trans (Nat.dvd_of_mem_primeFactors hp) hu₁_m, by omega⟩
  have hsub₂ : u₂.primeFactors ⊆ (m + 1).primeFactors := by
    intro p hp; have hp_pr := Nat.prime_of_mem_primeFactors hp
    exact Nat.mem_primeFactors.mpr ⟨hp_pr, dvd_trans (Nat.dvd_of_mem_primeFactors hp) hu₂_m, by omega⟩
  have hcard₁ : (u₁.primeFactors.card : ℝ) ≤ ((m - 1).primeFactors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub₁
  have hcard₂ : (u₂.primeFactors.card : ℝ) ≤ ((m + 1).primeFactors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub₂
  have hprod₁ : ((∏ p ∈ u₁.primeFactors, p : ℕ) : ℝ) ≤ ((∏ p ∈ (m - 1).primeFactors, p : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos))
      (Finset.prod_dvd_prod_of_subset u₁.primeFactors (m - 1).primeFactors id hsub₁)
  have hprod₂ : ((∏ p ∈ u₂.primeFactors, p : ℕ) : ℝ) ≤ ((∏ p ∈ (m + 1).primeFactors, p : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos))
      (Finset.prod_dvd_prod_of_subset u₂.primeFactors (m + 1).primeFactors id hsub₂)
  exact ⟨⟨p₁, hp₁, dvd_trans hp₁_dvd hu₁_m, hp₁_ge⟩,
         ⟨p₂, hp₂, dvd_trans hp₂_dvd hu₂_m, hp₂_ge⟩,
         le_trans hom₁ hcard₁,
         le_trans hom₂ hcard₂,
         le_trans hrad₁ hprod₁,
         le_trans hrad₂ hprod₂⟩

/-! ### Theorem 5.2(ii): Effective Sub-Exponential Midpoint Core Bounds and Non-Solubility of `x^2 - q_n y^2 = ±2` -/

lemma delta2Mid_ne_two {n X₁ Y₁ : ℕ} (hn : 8 ≤ n) (hfund : IsFundamentalPell (q_n n) X₁ Y₁) :
    delta2Mid X₁ ≠ 2 := by
  intro h2
  have hq_ge : 2 ≤ q_n n := q_n_ge_two (by omega)
  have hq_pos : 0 < q_n n := by omega
  have hX1 : 1 < X₁ := X1_gt_one hq_ge hfund
  have ⟨h_eq1, h_eq2, _⟩ := eq_5_1_midpoint_decomp hq_ge hfund
  rw [h2] at h_eq2
  have hdiff_q : (X₁ - 1) * (X₁ + 1) = q_n n * Y₁ ^ 2 := by
    zify [hX1.le]
    have : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
    linarith
  have h4_dvd_qY : 4 ∣ q_n n * Y₁ ^ 2 := by
    rw [← hdiff_q, h_eq2]
    have h2_dvd_X1m1 : 2 ∣ X₁ - 1 := by omega
    obtain ⟨t, ht⟩ := h2_dvd_X1m1
    rw [ht]
    exact ⟨t * vMid X₁ ^ 2, by ring⟩
  have h2_dvd_Y : 2 ∣ Y₁ := by
    by_contra h2nd
    have hcop : Nat.Coprime 4 (Y₁ ^ 2) :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2nd).pow_left 2 |>.pow_right 2
    have h4_dvd_q : 2 * 2 ∣ q_n n := hcop.dvd_of_dvd_mul_right h4_dvd_qY
    exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) 2 Nat.prime_two h4_dvd_q
  obtain ⟨Y', hY'⟩ := h2_dvd_Y
  have hv_pos : 0 < vMid X₁ := sqPartNat_pos _
  have h_prod_v : vMid X₁ ^ 2 * (vMid X₁ ^ 2 - 1) = q_n n * Y' ^ 2 := by
    have h1 : 4 * (vMid X₁ ^ 2 * (vMid X₁ ^ 2 - 1)) = (X₁ - 1) * (X₁ + 1) := by
      have : X₁ - 1 = 2 * (vMid X₁ ^ 2 - 1) := by omega
      rw [this, h_eq2]; ring
    rw [hdiff_q, hY'] at h1
    omega
  have hq_dvd : q_n n ∣ vMid X₁ ^ 2 - 1 := by
    rw [← Nat.prod_factorization_pow_eq_self hq_pos.ne']
    apply Finset.prod_primes_dvd
    · intro p hp; exact (Nat.prime_of_mem_primeFactors hp).prime
    · intro p hp
      have hp_pr := Nat.prime_of_mem_primeFactors hp
      haveI : Fact p.Prime := ⟨hp_pr⟩
      have hvp_q1 : (q_n n).factorization p = 1 := by
        rw [Nat.factorization_def _ hp_pr]
        have h1 : 1 ≤ padicValNat p (q_n n) :=
          one_le_padicValNat_of_dvd hq_pos.ne' (Nat.dvd_of_mem_primeFactors hp)
        have hle1 : padicValNat p (q_n n) ≤ 1 := by
          by_contra hgt
          have hpp : p * p ∣ q_n n := by
            rw [← sq]; exact dvd_trans (pow_dvd_pow p (by omega : 2 ≤ padicValNat p (q_n n))) pow_padicValNat_dvd
          exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp_pr hpp
        omega
      rw [hvp_q1, pow_one]
      have hv_eq := congrArg (padicValNat p) h_prod_v
      have hv2_ge1 : 1 ≤ vMid X₁ ^ 2 - 1 := by omega
      have hY'_pos : 0 < Y' := by nlinarith
      rw [padicValNat.mul (pow_ne_zero 2 hv_pos.ne') hv2_ge1.ne',
          padicValNat.mul hq_pos.ne' (pow_ne_zero 2 hY'_pos.ne'),
          padicValNat_pow_eq, padicValNat_pow_eq] at hv_eq
      have hvp_q_1 : padicValNat p (q_n n) = 1 := by
        rw [← Nat.factorization_def _ hp_pr]; exact hvp_q1
      rw [hvp_q_1] at hv_eq
      have h_odd_v2m1 : padicValNat p (vMid X₁ ^ 2 - 1) % 2 = 1 := by omega
      simpa using (padicValNat_dvd_iff_le hv2_ge1.ne').mpr (by omega : 1 ≤ padicValNat p (vMid X₁ ^ 2 - 1))
  obtain ⟨w, hw⟩ := hq_dvd
  have hvw_eq : vMid X₁ ^ 2 * w = Y' ^ 2 := by
    rw [hw] at h_prod_v
    have : q_n n * (vMid X₁ ^ 2 * w) = q_n n * Y' ^ 2 := by linarith
    exact mul_left_cancel₀ hq_pos.ne' this
  have hw_pos : 0 < w := by
    by_contra h0
    have : w = 0 := by omega
    rw [this, mul_zero] at hw
    omega
  have hw_sq : IsSquare w := by
    rw [← coreNat_mul_sqPartNat_sq hw_pos]
    have hcore1 : coreNat w = 1 := by
      apply Nat.eq_of_factorization_eq (coreNat_pos w).ne' (by norm_num)
      intro p
      by_cases hp : p.Prime
      · haveI : Fact p.Prime := ⟨hp⟩
        rw [Nat.factorization_def _ hp, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply,
            padicValNat_coreNat hp hw_pos]
        have hv_eq := congrArg (padicValNat p) hvw_eq
        have hY'_pos : 0 < Y' := by nlinarith
        rw [padicValNat.mul (pow_ne_zero 2 hv_pos.ne') hw_pos.ne',
            padicValNat_pow_eq, padicValNat_pow_eq] at hv_eq
        have : padicValNat p w % 2 = 0 := by omega
        simp [this]
      · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
    rw [hcore1, one_mul, sq]
    exact ⟨sqPartNat w, rfl⟩
  obtain ⟨u', hu'⟩ := hw_sq
  have hu'_pos : 0 < u' := by nlinarith
  have hv_pell : vMid X₁ ^ 2 = q_n n * u' ^ 2 + 1 := by
    have : vMid X₁ ^ 2 - 1 = q_n n * (u' * u') := by rw [← hu', hw]
    have : vMid X₁ ^ 2 - 1 = q_n n * u' ^ 2 := by simpa [sq] using this
    omega
  have hY_le : Y₁ ≤ u' := hfund.2.2.2 (vMid X₁) u' hu'_pos hv_pell
  have hY'_eq : Y' = vMid X₁ * u' := by
    have hsq : (vMid X₁ * u') ^ 2 = Y' ^ 2 := by
      calc (vMid X₁ * u') ^ 2 = vMid X₁ ^ 2 * (u' * u') := by ring
        _ = vMid X₁ ^ 2 * w := by rw [← hu']
        _ = Y' ^ 2 := hvw_eq
    exact (Nat.pow_left_inj (by norm_num : 2 ≠ 0)).mp hsq
  omega

/-- **Theorem 5.2(ii) — Effective Sub-Exponential Midpoint Core Bounds (eq. 5.6)**:
There exists an absolute effective constant `c₀ > 0` such that for all sufficiently large `n`,
`δ₁^{mid}(n) > exp(c₀ √(log n))` and `δ₂^{mid}(n) > exp(c₀ √(log n))`. -/
theorem thm_5_2_part2_effective_cores :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n X₁ Y₁ : ℕ, N₀ ≤ n →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      Real.exp (c₀ * Real.sqrt (Real.log (n : ℝ))) < (delta1Mid X₁ : ℝ) ∧
      Real.exp (c₀ * Real.sqrt (Real.log (n : ℝ))) < (delta2Mid X₁ : ℝ) := by
  obtain ⟨c₀, c₃, C, hc₀, hc₃, hC, N_dav, hN_dav8, h_dav⟩ := davenport_real_char_half_band_upper
  have h_asymp : ∀ᶠ n : ℕ in atTop,
      116 ≤ n ∧
      (8 : ℝ) ≤ Real.exp (c₀ * Real.sqrt (Real.log (n : ℝ))) ∧
      C * (n : ℝ) * Real.exp (-c₃ * Real.sqrt (Real.log (n : ℝ))) <
        0.4 * (n : ℝ) - c₀ * Real.sqrt (Real.log (n : ℝ)) := by
    have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hsqrt_inf : Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hlog_inf
    have h_exp1 : Tendsto (fun n : ℕ => Real.exp (c₀ * Real.sqrt (Real.log (n : ℝ)))) atTop atTop :=
      Real.tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop hc₀ hsqrt_inf)
    have h_exp2 : Tendsto (fun n : ℕ => C * Real.exp (-c₃ * Real.sqrt (Real.log (n : ℝ)))) atTop (nhds 0) := by
      have : Tendsto (fun n : ℕ => -c₃ * Real.sqrt (Real.log (n : ℝ))) atTop Filter.atBot :=
        Filter.Tendsto.const_mul_atTop_of_neg (by linarith) hsqrt_inf
      simpa using (Real.tendsto_exp_atBot.comp this).const_mul C
    have h_sqrt_div_n : Tendsto (fun n : ℕ => c₀ * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ)) atTop (nhds 0) := by
      have h_le : ∀ᶠ n : ℕ in atTop, 0 ≤ c₀ * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ) ∧
          c₀ * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ) ≤ c₀ * (Real.log (n : ℝ) / (n : ℝ)) := by
        filter_upwards [eventually_ge_atTop 3] with n hn
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hlog1 : 1 ≤ Real.log (n : ℝ) := by
          rw [Real.le_log_iff_exp_le hn_pos]
          linarith [Real.exp_one_lt_d9, show (3 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn]
        have hsqrt_le : Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
          rw [Real.sqrt_le_left (by linarith)]
          nlinarith
        refine ⟨by positivity, ?_⟩
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsqrt_le hn_pos.le) hc₀.le
      have hlog_div : Tendsto (fun n : ℕ => c₀ * (Real.log (n : ℝ) / (n : ℝ))) atTop (nhds 0) := by
        have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
          simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
        simpa using (h1.comp tendsto_natCast_atTop_atTop).const_mul c₀
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog_div
        (h_le.mono fun _ h => h.1) (h_le.mono fun _ h => h.2)
    filter_upwards [eventually_ge_atTop 116,
      h_exp1.eventually (eventually_ge_atTop 8),
      h_exp2.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 0.1)),
      h_sqrt_div_n.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 0.1))] with n hn116 hexp8 hexp01 hsqrt01
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h1 : C * (n : ℝ) * Real.exp (-c₃ * Real.sqrt (Real.log (n : ℝ))) < 0.1 * (n : ℝ) := by
      have : C * Real.exp (-c₃ * Real.sqrt (Real.log (n : ℝ))) < 0.1 := hexp01
      nlinarith
    have h2 : c₀ * Real.sqrt (Real.log (n : ℝ)) < 0.1 * (n : ℝ) := by
      have := (div_lt_iff₀ hn_pos).mp hsqrt01
      linarith
    exact ⟨hn116, hexp8, by linarith⟩
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h_asymp
  refine ⟨c₀, hc₀, max N_dav M, le_trans hN_dav8 (le_max_left _ _), ?_⟩
  intro n X₁ Y₁ hn hfund
  obtain ⟨hn116, hexp8, h_contra_ineq⟩ := hM n (le_trans (le_max_right _ _) hn)
  have hn_dav : N_dav ≤ n := le_trans (le_max_left _ _) hn
  have hθ := rosser_schoenfeld_theta_diff n hn116
  have h_bound_delta : ∀ (δ : ℕ) (d : ℤ), 0 < δ → d ≠ 0 → ¬ IsSquare d → d.natAbs = 2 * δ →
      (∀ p : ℕ, p.Prime → n / 2 < p → p ≤ n →
        chiLegendre d p = if p ∣ δ then 0 else 1) →
      Real.exp (c₀ * Real.sqrt (Real.log (n : ℝ))) < (δ : ℝ) := by
    intro δ d hδ_pos hd_ne hd_nsq hd_abs hchi
    by_contra hle
    push_neg at hle
    have h4d : 4 * (d.natAbs : ℝ) ≤ Real.exp (2 * c₀ * Real.sqrt (Real.log (n : ℝ))) := by
      have h_mul : 2 * c₀ * Real.sqrt (Real.log (n : ℝ)) =
          c₀ * Real.sqrt (Real.log (n : ℝ)) + c₀ * Real.sqrt (Real.log (n : ℝ)) := by ring
      rw [h_mul, Real.exp_add, hd_abs]
      push_cast
      nlinarith [Real.exp_pos (c₀ * Real.sqrt (Real.log (n : ℝ)))]
    have h_ub := h_dav n hn_dav d hd_ne hd_nsq h4d
    have h_eq_sum :
        (∑ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ 3 ≤ p),
          (chiLegendre d p : ℝ) * Real.log (p : ℝ)) =
        (∑ p ∈ (Finset.Ioc (n / 2) n).filter Nat.Prime, Real.log (p : ℝ)) -
        (∑ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ p ∣ δ), Real.log (p : ℝ)) := by
      have h_fil : (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ 3 ≤ p) =
          (Finset.Ioc (n / 2) n).filter Nat.Prime := by
        ext p; simp only [Finset.mem_filter, Finset.mem_Ioc]; omega
      rw [h_fil]
      have hterm : ∀ p ∈ (Finset.Ioc (n / 2) n).filter Nat.Prime,
          (chiLegendre d p : ℝ) * Real.log (p : ℝ) =
          Real.log (p : ℝ) - if p ∣ δ then Real.log (p : ℝ) else 0 := by
        intro p hp_mem
        rw [Finset.mem_filter, Finset.mem_Ioc] at hp_mem
        rw [hchi p hp_mem.2 hp_mem.1.1 hp_mem.1.2]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
      congr 1
      rw [← Finset.sum_filter]
      congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_Ioc]; tauto
    have h_dvd_le :
        (∑ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ p ∣ δ), Real.log (p : ℝ)) ≤
        Real.log (δ : ℝ) := by
      have hprod_dvd : (∏ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ p ∣ δ), p) ∣ δ := by
        apply Finset.prod_primes_dvd
        · intro p hp; exact (Finset.mem_filter.mp hp).2.1.prime
        · intro p hp; exact (Finset.mem_filter.mp hp).2.2
      have hprod_pos : 0 < ∏ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ p ∣ δ), (p : ℝ) :=
        Finset.prod_pos (fun p hp => by exact_mod_cast (Finset.mem_filter.mp hp).2.1.pos)
      calc _ = Real.log (∏ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ p ∣ δ), (p : ℝ)) := by
            rw [Real.log_prod (fun p hp => by exact_mod_cast (Finset.mem_filter.mp hp).2.1.ne_zero)]
        _ ≤ Real.log (δ : ℝ) := Real.log_le_log hprod_pos (by exact_mod_cast Nat.le_of_dvd hδ_pos hprod_dvd)
    have hlog_δ_le : Real.log (δ : ℝ) ≤ c₀ * Real.sqrt (Real.log (n : ℝ)) := by
      rw [← Real.log_exp (c₀ * Real.sqrt (Real.log (n : ℝ)))]
      exact Real.log_le_log (by exact_mod_cast hδ_pos) hle
    linarith
  constructor
  · refine h_bound_delta (delta1Mid X₁) (-2 * (delta1Mid X₁ : ℤ)) (coreNat_pos _) (by
      have := coreNat_pos (X₁ - 1); unfold delta1Mid; omega) ?_ (by omega) ?_
    · intro ⟨r, hr⟩
      have hneg : (-2 * (delta1Mid X₁ : ℤ)) < 0 := by
        have := coreNat_pos (X₁ - 1); unfold delta1Mid; omega
      nlinarith [mul_self_nonneg r]
    · intro p hp hlo hhi
      exact (psi_eval_upper_half (by omega) hfund hp hlo hhi).1
  · refine h_bound_delta (delta2Mid X₁) (2 * (delta2Mid X₁ : ℤ)) (coreNat_pos _) (by
      have := coreNat_pos (X₁ + 1); unfold delta2Mid; omega) ?_ (by omega) ?_
    · intro ⟨r, hr⟩
      have h2_ne : delta2Mid X₁ ≠ 2 := delta2Mid_ne_two (by omega) hfund
      have hsf : Squarefree (delta2Mid X₁) := coreNat_squarefree _
      have hr_eq : 2 * delta2Mid X₁ = r.natAbs ^ 2 := by
        zify; simpa [sq_abs, sq] using hr
      by_cases h2d : 2 ∣ delta2Mid X₁
      · obtain ⟨t, ht⟩ := h2d
        have ht_ne1 : t ≠ 1 := by intro h1; subst h1; omega
        obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd ht_ne1
        have hp_ne2 : p ≠ 2 := by
          intro h2; subst h2
          exact (Nat.squarefree_iff_prime_squarefree.mp hsf) 2 Nat.prime_two (ht ▸ mul_dvd_mul_left 2 hpt)
        have hp_dvd_r2 : p ∣ r.natAbs ^ 2 := by
          rw [← hr_eq, ht]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpt 2) 2
        have hp_dvd_r : p ∣ r.natAbs := hp.dvd_of_dvd_pow hp_dvd_r2
        have hp2_dvd : p * p ∣ 2 * delta2Mid X₁ := by
          rw [hr_eq, sq]; exact mul_dvd_mul hp_dvd_r hp_dvd_r
        have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp_ne2
        have hp2_dvd_d : p * p ∣ delta2Mid X₁ := (hcop.mul_left hcop).symm.dvd_of_dvd_mul_left (by simpa [mul_comm] using hp2_dvd)
        exact (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp hp2_dvd_d
      · have h2_dvd_r2 : 2 ∣ r.natAbs ^ 2 := by rw [← hr_eq]; exact dvd_mul_right 2 _
        have h2_dvd_r : 2 ∣ r.natAbs := Nat.prime_two.dvd_of_dvd_pow h2_dvd_r2
        have h4_dvd : 4 ∣ 2 * delta2Mid X₁ := by rw [hr_eq, sq]; exact mul_dvd_mul h2_dvd_r h2_dvd_r
        have : 2 ∣ delta2Mid X₁ := by omega
        exact h2d this
    · intro p hp hlo hhi
      exact (psi_eval_upper_half (by omega) hfund hp hlo hhi).2

/-- **Theorem 5.2(ii) — Non-Solubility of `x^2 - q_n y^2 = ±2`**:
For all sufficiently large `n`, neither `x^2 - q_n y^2 = 2` nor `x^2 - q_n y^2 = -2` has an
integer solution. -/
theorem thm_5_2_part2_pell_pm2_insoluble :
    ∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n →
      (∀ x y : ℤ, x ^ 2 - (q_n n : ℤ) * y ^ 2 ≠ 2) ∧
      (∀ x y : ℤ, x ^ 2 - (q_n n : ℤ) * y ^ 2 ≠ -2) := by
  obtain ⟨c₀, hc₀, N₀, hN₀8, h_cores⟩ := thm_5_2_part2_effective_cores
  refine ⟨N₀, hN₀8, fun n hn => ?_⟩
  have hq_ge : 2 ≤ q_n n := q_n_ge_two (by omega)
  have hq_pos : 0 < q_n n := by omega
  have h_exists_fund : ∃ X₁ Y₁ : ℕ, IsFundamentalPell (q_n n) X₁ Y₁ := by
    have hnsq : ¬ IsSquare (q_n n) := by
      intro ⟨r, hr⟩
      have hr_ge : 2 ≤ r := by nlinarith
      obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd (by omega : r ≠ 1)
      exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp (hr ▸ mul_dvd_mul hpr hpr)
    obtain ⟨u, hu⟩ := Pell.exists_of_not_isSquare hnsq
    have h_sols : ∃ y : ℕ, 0 < y ∧ ∃ x : ℕ, x ^ 2 = q_n n * y ^ 2 + 1 := by
      refine ⟨u.y.natAbs, Int.natAbs_pos.mpr hu.2, u.x.natAbs, ?_⟩
      zify
      have h1 : u.x ^ 2 - (q_n n : ℤ) * u.y ^ 2 = 1 := hu.1
      simpa [sq_abs] using show u.x ^ 2 = (q_n n : ℤ) * u.y ^ 2 + 1 by linarith
    classical
    let Y₁ := Nat.find h_sols
    have hY₁ := Nat.find_spec h_sols
    obtain ⟨X₁, hX₁⟩ := hY₁.2
    have hX₁_pos : 0 < X₁ := by nlinarith
    exact ⟨X₁, Y₁, hX₁_pos, hY₁.1, hX₁, fun x y hy hxy => Nat.find_min' h_sols ⟨hy, x, hxy⟩⟩
  obtain ⟨X₁, Y₁, hfund⟩ := h_exists_fund
  have ⟨hδ₁_gt, hδ₂_gt⟩ := h_cores n X₁ Y₁ hn hfund
  have h_exp_ge1 : 1 ≤ Real.exp (c₀ * Real.sqrt (Real.log (n : ℝ))) :=
    Real.one_le_exp (mul_nonneg hc₀.le (Real.sqrt_nonneg _))
  have hδ₁_gt1 : 1 < delta1Mid X₁ := by
    have : (1 : ℝ) < (delta1Mid X₁ : ℝ) := lt_of_le_of_lt h_exp_ge1 hδ₁_gt
    exact_mod_cast this
  have hδ₂_gt1 : 1 < delta2Mid X₁ := by
    have : (1 : ℝ) < (delta2Mid X₁ : ℝ) := lt_of_le_of_lt h_exp_ge1 hδ₂_gt
    exact_mod_cast this
  have ⟨h_eq1, h_eq2, _⟩ := eq_5_1_midpoint_decomp hq_ge hfund
  have h_no_pm2 : ∀ (sgn : ℤ), sgn = 2 ∨ sgn = -2 →
      ∀ x y : ℤ, x ^ 2 - (q_n n : ℤ) * y ^ 2 ≠ sgn := by
    intro sgn hsgn x y hxy
    have hy_ne : y ≠ 0 := by
      intro h0; subst h0; simp at hxy
      rcases hsgn with rfl | rfl
      · have : x.natAbs ^ 2 = 2 := by zify; simpa [sq_abs] using hxy
        have : x.natAbs ≤ 2 := by nlinarith
        interval_cases x.natAbs <;> norm_num at this
      · nlinarith
    have hx_ne : x ≠ 0 := by
      intro h0; subst h0; simp at hxy
      rcases hsgn with rfl | rfl
      · nlinarith
      · have : (q_n n : ℤ) * y ^ 2 = 2 := by linarith
        have hq_gt2 : 2 < q_n n := by
          have hodd : ¬ 2 ∣ oddPartNat (q_n n) := oddPartNat_not_dvd_two hq_pos
          have h1 := oddPartNat_q_n_gt_one (by omega : 8 ≤ n)
          have hle := oddPartNat_le (m := q_n n)
          omega
        have : 1 ≤ y ^ 2 := by nlinarith [sq_pos_iff.mpr hy_ne]
        nlinarith
    let X : ℤ := if sgn = 2 then x ^ 2 - 1 else x ^ 2 + 1
    let Y : ℕ := (x * y).natAbs
    have hX_pos : 0 < X := by
      rcases hsgn with rfl | rfl
      · simp only [↓reduceIte]
        have : 1 ≤ x ^ 2 := by nlinarith [sq_pos_iff.mpr hx_ne]
        have : x ^ 2 ≠ 1 := by
          intro h1; rw [h1] at hxy
          have : (q_n n : ℤ) * y ^ 2 = -1 := by linarith
          nlinarith [sq_nonneg y]
        omega
      · simp only [show (-2 : ℤ) ≠ 2 by norm_num, ↓reduceIte]
        nlinarith [sq_nonneg x]
    have hY_pos : 0 < Y := Int.natAbs_pos.mpr (mul_ne_zero hx_ne hy_ne)
    have hXY_pell : X ^ 2 - (q_n n : ℤ) * (Y : ℤ) ^ 2 = 1 := by
      rcases hsgn with rfl | rfl
      · dsimp [X, Y]; simp only [↓reduceIte, sq_abs]
        have hqy : (q_n n : ℤ) * y ^ 2 = x ^ 2 - 2 := by linarith
        calc (x ^ 2 - 1) ^ 2 - (q_n n : ℤ) * (x * y) ^ 2
            = (x ^ 2 - 1) ^ 2 - x ^ 2 * ((q_n n : ℤ) * y ^ 2) := by ring
          _ = (x ^ 2 - 1) ^ 2 - x ^ 2 * (x ^ 2 - 2) := by rw [hqy]
          _ = 1 := by ring
      · dsimp [X, Y]; simp only [show (-2 : ℤ) ≠ 2 by norm_num, ↓reduceIte, sq_abs]
        have hqy : (q_n n : ℤ) * y ^ 2 = x ^ 2 + 2 := by linarith
        calc (x ^ 2 + 1) ^ 2 - (q_n n : ℤ) * (x * y) ^ 2
            = (x ^ 2 + 1) ^ 2 - x ^ 2 * ((q_n n : ℤ) * y ^ 2) := by ring
          _ = (x ^ 2 + 1) ^ 2 - x ^ 2 * (x ^ 2 + 2) := by rw [hqy]
          _ = 1 := by ring
    have h_pow : ∃ m : ℕ, 1 ≤ m ∧
        X = lucasX (q_n n) X₁ Y₁ m ∧ (Y : ℤ) = lucasY (q_n n) X₁ Y₁ m := by
      have h_desc : ∀ (A B : ℕ), 0 < A → 0 < B → A ^ 2 = q_n n * B ^ 2 + 1 →
          ∃ m : ℕ, 1 ≤ m ∧ (A : ℤ) = lucasX (q_n n) X₁ Y₁ m ∧ (B : ℤ) = lucasY (q_n n) X₁ Y₁ m := by
        intro A B
        induction B using Nat.strong_induction_on generalizing A with
        | _ B ih =>
          intro hA hB hAB
          have hY1_le : Y₁ ≤ B := hfund.2.2.2 A B hB hAB
          by_cases heq : B = Y₁
          · subst heq
            have hA_eq : A = X₁ := by
              have : A ^ 2 = X₁ ^ 2 := by rw [hAB, hfund.2.2.1]
              exact (Nat.pow_left_inj (by norm_num : 2 ≠ 0)).mp this
            subst hA_eq
            exact ⟨1, le_rfl, by simp [lucasX], by simp [lucasY]⟩
          · have hY1_lt : Y₁ < B := lt_of_le_of_ne hY1_le (Ne.symm heq)
            let A' : ℤ := (A : ℤ) * (X₁ : ℤ) - (q_n n : ℤ) * (B : ℤ) * (Y₁ : ℤ)
            let B' : ℤ := (B : ℤ) * (X₁ : ℤ) - (A : ℤ) * (Y₁ : ℤ)
            have hB'_pos : 0 < B' := by
              have h1 : (A : ℤ) ^ 2 * (Y₁ : ℤ) ^ 2 < (B : ℤ) ^ 2 * (X₁ : ℤ) ^ 2 := by
                have hAX : (A : ℤ) ^ 2 * (Y₁ : ℤ) ^ 2 = ((q_n n : ℤ) * (B : ℤ) ^ 2 + 1) * (Y₁ : ℤ) ^ 2 := by
                  have : (A : ℤ) ^ 2 = (q_n n : ℤ) * (B : ℤ) ^ 2 + 1 := by exact_mod_cast hAB
                  rw [this]
                have hBX : (B : ℤ) ^ 2 * (X₁ : ℤ) ^ 2 = (B : ℤ) ^ 2 * ((q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1) := by
                  have : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
                  rw [this]
                have hlt_sq : (Y₁ : ℤ) ^ 2 < (B : ℤ) ^ 2 := by
                  have : Y₁ ^ 2 < B ^ 2 := Nat.pow_lt_pow_left hY1_lt (by norm_num)
                  exact_mod_cast this
                linarith
              have : (A : ℤ) * (Y₁ : ℤ) < (B : ℤ) * (X₁ : ℤ) := by nlinarith
              dsimp [B']; linarith
            have hA'_pos : 0 < A' := by
              have hsq_gt : (q_n n : ℤ) ^ 2 * (B : ℤ) ^ 2 * (Y₁ : ℤ) ^ 2 < (A : ℤ) ^ 2 * (X₁ : ℤ) ^ 2 := by
                have hA_eq : (A : ℤ) ^ 2 = (q_n n : ℤ) * (B : ℤ) ^ 2 + 1 := by exact_mod_cast hAB
                have hX_eq : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
                rw [hA_eq, hX_eq]; nlinarith
              have : (q_n n : ℤ) * (B : ℤ) * (Y₁ : ℤ) < (A : ℤ) * (X₁ : ℤ) := by nlinarith
              dsimp [A']; linarith
            have hB'_lt : B'.natAbs < B := by
              have hX1_gt : 1 < X₁ := X1_gt_one hq_ge hfund
              have hsq_lt : (B : ℤ) ^ 2 * ((X₁ : ℤ) - 1) ^ 2 < (A : ℤ) ^ 2 * (Y₁ : ℤ) ^ 2 := by
                have hA_eq : (A : ℤ) ^ 2 = (q_n n : ℤ) * (B : ℤ) ^ 2 + 1 := by exact_mod_cast hAB
                have hX_eq : (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 = (X₁ : ℤ) ^ 2 - 1 := by
                  have : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
                  linarith
                have h1 : (B : ℤ) ^ 2 * ((X₁ : ℤ) - 1) ^ 2 < (B : ℤ) ^ 2 * ((X₁ : ℤ) ^ 2 - 1) := by
                  have : ((X₁ : ℤ) - 1) ^ 2 < (X₁ : ℤ) ^ 2 - 1 := by nlinarith
                  exact mul_lt_mul_of_pos_left this (by positivity)
                calc (B : ℤ) ^ 2 * ((X₁ : ℤ) - 1) ^ 2 < (B : ℤ) ^ 2 * ((X₁ : ℤ) ^ 2 - 1) := h1
                  _ = (q_n n : ℤ) * (B : ℤ) ^ 2 * (Y₁ : ℤ) ^ 2 := by rw [← hX_eq]; ring
                  _ < ((q_n n : ℤ) * (B : ℤ) ^ 2 + 1) * (Y₁ : ℤ) ^ 2 := by nlinarith [sq_pos_iff.mpr (by exact_mod_cast hfund.2.1.ne' : (Y₁ : ℤ) ≠ 0)]
                  _ = (A : ℤ) ^ 2 * (Y₁ : ℤ) ^ 2 := by rw [hA_eq]
              have : (B : ℤ) * ((X₁ : ℤ) - 1) < (A : ℤ) * (Y₁ : ℤ) := by nlinarith
              have hB'_lt_z : B' < (B : ℤ) := by dsimp [B']; linarith
              omega
            have hA'B' : A' ^ 2 - (q_n n : ℤ) * B' ^ 2 = 1 := by
              have h1 : (A : ℤ) ^ 2 - (q_n n : ℤ) * (B : ℤ) ^ 2 = 1 := by
                have h : (A : ℤ) ^ 2 = (q_n n : ℤ) * (B : ℤ) ^ 2 + 1 := by exact_mod_cast hAB
                linarith
              have h2 : (X₁ : ℤ) ^ 2 - (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 = 1 := by
                have h : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
                linarith
              dsimp [A', B']
              calc _ = ((A : ℤ) ^ 2 - (q_n n : ℤ) * (B : ℤ) ^ 2) * ((X₁ : ℤ) ^ 2 - (q_n n : ℤ) * (Y₁ : ℤ) ^ 2) := by ring
                _ = 1 * 1 := by rw [h1, h2]
                _ = 1 := by ring
            obtain ⟨m, hm1, hmA, hmB⟩ := ih B'.natAbs hB'_lt A'.natAbs (by omega) (by omega) (by
              zify; rw [Int.natAbs_of_nonneg hA'_pos.le, Int.natAbs_of_nonneg hB'_pos.le]; linarith)
            refine ⟨m + 1, by omega, ?_, ?_⟩
            · have hA'z : (A'.natAbs : ℤ) = A' := Int.natAbs_of_nonneg hA'_pos.le
              have hB'z : (B'.natAbs : ℤ) = B' := Int.natAbs_of_nonneg hB'_pos.le
              have h_re : ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q_n n)) ^ (m + 1)).re =
                  lucasX (q_n n) X₁ Y₁ m * (X₁ : ℤ) + (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ m * (Y₁ : ℤ) := by
                rw [pow_succ]; rfl
              unfold lucasX
              rw [h_re, ← hmA, ← hmB, hA'z, hB'z]
              dsimp [A', B']
              have hX_eq : (X₁ : ℤ) ^ 2 - (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 = 1 := by
                have h : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
                linarith
              calc _ = (A : ℤ) * ((X₁ : ℤ) ^ 2 - (q_n n : ℤ) * (Y₁ : ℤ) ^ 2) := by ring
                _ = (A : ℤ) := by rw [hX_eq, mul_one]
            · have hA'z : (A'.natAbs : ℤ) = A' := Int.natAbs_of_nonneg hA'_pos.le
              have hB'z : (B'.natAbs : ℤ) = B' := Int.natAbs_of_nonneg hB'_pos.le
              have h_im : ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q_n n)) ^ (m + 1)).im =
                  lucasX (q_n n) X₁ Y₁ m * (Y₁ : ℤ) + lucasY (q_n n) X₁ Y₁ m * (X₁ : ℤ) := by
                rw [pow_succ]; rfl
              unfold lucasY
              rw [h_im, ← hmA, ← hmB, hA'z, hB'z]
              dsimp [A', B']
              have hX_eq : (X₁ : ℤ) ^ 2 - (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 = 1 := by
                have h : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
                linarith
              calc _ = (B : ℤ) * ((X₁ : ℤ) ^ 2 - (q_n n : ℤ) * (Y₁ : ℤ) ^ 2) := by ring
                _ = (B : ℤ) := by rw [hX_eq, mul_one]
      obtain ⟨m, hm1, hmX, hmY⟩ := h_desc X.natAbs Y (by omega) hY_pos (by
        zify; rw [abs_of_pos hX_pos]; linarith)
      exact ⟨m, hm1, by rw [← hmX, Int.natAbs_of_nonneg hX_pos.le], hmY⟩
    obtain ⟨m, hm1, hmX, _⟩ := h_pow
    rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
    · have hm2r : m = 2 * r := by omega
      subst hm2r
      have h_norm_r : lucasX (q_n n) X₁ Y₁ r ^ 2 - (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ r ^ 2 = 1 := by
        have h_pow_norm : ∀ t : ℕ, lucasX (q_n n) X₁ Y₁ t ^ 2 - (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ t ^ 2 = 1 := by
          intro t
          induction t with
          | zero => simp [lucasX, lucasY]
          | succ t iht =>
            have hre : lucasX (q_n n) X₁ Y₁ (t + 1) = lucasX (q_n n) X₁ Y₁ t * (X₁ : ℤ) + (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ t * (Y₁ : ℤ) := by
              unfold lucasX lucasY; rw [pow_succ]; rfl
            have him : lucasY (q_n n) X₁ Y₁ (t + 1) = lucasX (q_n n) X₁ Y₁ t * (Y₁ : ℤ) + lucasY (q_n n) X₁ Y₁ t * (X₁ : ℤ) := by
              unfold lucasX lucasY; rw [pow_succ]; rfl
            rw [hre, him]
            have hX_eq : (X₁ : ℤ) ^ 2 - (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 = 1 := by
              have h : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
              linarith
            calc _ = (lucasX (q_n n) X₁ Y₁ t ^ 2 - (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ t ^ 2) *
                ((X₁ : ℤ) ^ 2 - (q_n n : ℤ) * (Y₁ : ℤ) ^ 2) := by ring
              _ = 1 * 1 := by rw [iht, hX_eq]
              _ = 1 := by ring
        exact h_pow_norm r
      have hX_2r : lucasX (q_n n) X₁ Y₁ (2 * r) = 2 * lucasX (q_n n) X₁ Y₁ r ^ 2 - 1 := by
        have h_sq : (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q_n n)) ^ (2 * r) =
            ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q_n n)) ^ r) ^ 2 := by rw [← pow_mul, mul_comm]
        have hre : lucasX (q_n n) X₁ Y₁ (2 * r) = lucasX (q_n n) X₁ Y₁ r ^ 2 + (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ r ^ 2 := by
          set z := (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q_n n)) ^ r
          have hza : lucasX (q_n n) X₁ Y₁ r = z.re := rfl
          have hzb : lucasY (q_n n) X₁ Y₁ r = z.im := rfl
          rw [hza, hzb]
          unfold lucasX; rw [h_sq, sq]
          rcases z with ⟨za, zb⟩; rfl
        linarith
      rcases hsgn with rfl | rfl
      · have hX_eq : x ^ 2 - 1 = X := rfl
        have hx2 : x ^ 2 = 2 * lucasX (q_n n) X₁ Y₁ r ^ 2 := by linarith
        have h2_sq : x.natAbs ^ 2 = 2 * (lucasX (q_n n) X₁ Y₁ r).natAbs ^ 2 := by
          zify; simpa [sq_abs] using hx2
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hXr_ne : (lucasX (q_n n) X₁ Y₁ r).natAbs ≠ 0 := by
          intro h0; have : lucasX (q_n n) X₁ Y₁ r = 0 := Int.natAbs_eq_zero.mp h0
          rw [this] at h_norm_r; nlinarith [sq_nonneg (lucasY (q_n n) X₁ Y₁ r)]
        have hv := congrArg (padicValNat 2) h2_sq
        rw [padicValNat_pow_eq,
            padicValNat.mul (by norm_num) (pow_ne_zero 2 hXr_ne),
            padicValNat_pow_eq, padicValNat_self] at hv
        omega
      · have hX_eq : x ^ 2 + 1 = X := rfl
        have hx2 : x ^ 2 = 2 * (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ r ^ 2 := by linarith
        have h2_sq : x.natAbs ^ 2 = 2 * q_n n * (lucasY (q_n n) X₁ Y₁ r).natAbs ^ 2 := by
          zify; simpa [sq_abs] using hx2
        have hYr_ne : (lucasY (q_n n) X₁ Y₁ r).natAbs ≠ 0 := by
          intro h0; have : lucasY (q_n n) X₁ Y₁ r = 0 := Int.natAbs_eq_zero.mp h0
          rw [this] at hx2; simp at hx2; exact hx_ne hx2
        have hn8 : 8 ≤ n := le_trans hN₀8 hn
        obtain ⟨p, hp, hpq, hpmod⟩ := q_n_has_prime_mod4 (by omega) (by omega)
        have hp2 : p ≠ 2 := by intro h2; subst h2; norm_num at hpmod
        haveI : Fact p.Prime := ⟨hp⟩
        have hv := congrArg (padicValNat p) h2_sq
        rw [padicValNat_pow_eq,
            padicValNat.mul (mul_pos (by norm_num) hq_pos).ne' (pow_ne_zero 2 hYr_ne),
            padicValNat.mul (by norm_num) hq_pos.ne',
            padicValNat.eq_zero_of_not_dvd (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)),
            zero_add, padicValNat_pow_eq] at hv
        have hvp_q1 : padicValNat p (q_n n) = 1 := by
          have h1 := one_le_padicValNat_of_dvd hq_pos.ne' hpq
          have hle1 : padicValNat p (q_n n) ≤ 1 := by
            by_contra hgt
            exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp
              (by rw [← sq]; exact dvd_trans (pow_dvd_pow p (by omega : 2 ≤ padicValNat p (q_n n))) pow_padicValNat_dvd)
          omega
        rw [hvp_q1] at hv
        omega
    · have hm2r1 : m = 2 * r + 1 := by omega
      subst hm2r1
      have h_norm_r : lucasX (q_n n) X₁ Y₁ r ^ 2 - (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ r ^ 2 = 1 := by
        have h_pow_norm : ∀ t : ℕ, lucasX (q_n n) X₁ Y₁ t ^ 2 - (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ t ^ 2 = 1 := by
          intro t
          induction t with
          | zero => simp [lucasX, lucasY]
          | succ t iht =>
            have hre : lucasX (q_n n) X₁ Y₁ (t + 1) = lucasX (q_n n) X₁ Y₁ t * (X₁ : ℤ) + (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ t * (Y₁ : ℤ) := by
              unfold lucasX lucasY; rw [pow_succ]; rfl
            have him : lucasY (q_n n) X₁ Y₁ (t + 1) = lucasX (q_n n) X₁ Y₁ t * (Y₁ : ℤ) + lucasY (q_n n) X₁ Y₁ t * (X₁ : ℤ) := by
              unfold lucasX lucasY; rw [pow_succ]; rfl
            rw [hre, him]
            have hX_eq : (X₁ : ℤ) ^ 2 - (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 = 1 := by
              have h : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
              linarith
            calc _ = (lucasX (q_n n) X₁ Y₁ t ^ 2 - (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ t ^ 2) *
                ((X₁ : ℤ) ^ 2 - (q_n n : ℤ) * (Y₁ : ℤ) ^ 2) := by ring
              _ = 1 * 1 := by rw [iht, hX_eq]
              _ = 1 := by ring
        exact h_pow_norm r
      have hX_2r1 : lucasX (q_n n) X₁ Y₁ (2 * r + 1) =
          (X₁ : ℤ) * (lucasX (q_n n) X₁ Y₁ r ^ 2 + (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ r ^ 2) +
          2 * (q_n n : ℤ) * (Y₁ : ℤ) * lucasX (q_n n) X₁ Y₁ r * lucasY (q_n n) X₁ Y₁ r := by
        have h_pow_eq : (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q_n n)) ^ (2 * r + 1) =
            ⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ * ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q_n n)) ^ r) ^ 2 := by
          rw [pow_succ', ← pow_mul, mul_comm 2 r]
        set z := (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q_n n)) ^ r
        have hza : lucasX (q_n n) X₁ Y₁ r = z.re := rfl
        have hzb : lucasY (q_n n) X₁ Y₁ r = z.im := rfl
        rw [hza, hzb]
        unfold lucasX; rw [h_pow_eq, sq]
        rcases z with ⟨za, zb⟩; change (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ * (⟨za, zb⟩ * ⟨za, zb⟩ : Zsqrtd (q_n n))).re = _; dsimp [HMul.hMul, Mul.mul, Zsqrtd.mul]; ring
      rcases hsgn with rfl | rfl
      · have hx2 : X + 1 = x ^ 2 := by dsimp [X]; ring
        have h_id : (delta2Mid X₁ : ℤ) * (vMid X₁ : ℤ) ^ 2 * x ^ 2 =
            ((delta2Mid X₁ : ℤ) * (vMid X₁ : ℤ) ^ 2 * lucasX (q_n n) X₁ Y₁ r +
              (q_n n : ℤ) * (Y₁ : ℤ) * lucasY (q_n n) X₁ Y₁ r) ^ 2 := by
          have h2 : (delta2Mid X₁ : ℤ) * (vMid X₁ : ℤ) ^ 2 = (X₁ : ℤ) + 1 := by exact_mod_cast h_eq2.symm
          rw [← hx2, hmX, hX_2r1]
          have hX1_sq : (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 = ((X₁ : ℤ) - 1) * ((X₁ : ℤ) + 1) := by
            have : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
            linarith
          rw [h2]
          calc ((X₁ : ℤ) + 1) * ((X₁ : ℤ) * (lucasX (q_n n) X₁ Y₁ r ^ 2 + (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ r ^ 2) +
                2 * (q_n n : ℤ) * (Y₁ : ℤ) * lucasX (q_n n) X₁ Y₁ r * lucasY (q_n n) X₁ Y₁ r + 1)
              = ((X₁ : ℤ) + 1) * ((X₁ : ℤ) * (lucasX (q_n n) X₁ Y₁ r ^ 2 + (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ r ^ 2) +
                2 * (q_n n : ℤ) * (Y₁ : ℤ) * lucasX (q_n n) X₁ Y₁ r * lucasY (q_n n) X₁ Y₁ r +
                (lucasX (q_n n) X₁ Y₁ r ^ 2 - (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ r ^ 2)) := by rw [h_norm_r]
            _ = ((X₁ : ℤ) + 1) ^ 2 * lucasX (q_n n) X₁ Y₁ r ^ 2 +
                2 * ((X₁ : ℤ) + 1) * (q_n n : ℤ) * (Y₁ : ℤ) * lucasX (q_n n) X₁ Y₁ r * lucasY (q_n n) X₁ Y₁ r +
                ((X₁ : ℤ) - 1) * ((X₁ : ℤ) + 1) * (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ r ^ 2 := by ring
            _ = ((X₁ : ℤ) + 1) ^ 2 * lucasX (q_n n) X₁ Y₁ r ^ 2 +
                2 * ((X₁ : ℤ) + 1) * (q_n n : ℤ) * (Y₁ : ℤ) * lucasX (q_n n) X₁ Y₁ r * lucasY (q_n n) X₁ Y₁ r +
                (q_n n : ℤ) ^ 2 * (Y₁ : ℤ) ^ 2 * lucasY (q_n n) X₁ Y₁ r ^ 2 := by rw [← hX1_sq]; ring
            _ = (((X₁ : ℤ) + 1) * lucasX (q_n n) X₁ Y₁ r + (q_n n : ℤ) * (Y₁ : ℤ) * lucasY (q_n n) X₁ Y₁ r) ^ 2 := by ring
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hδ₂_gt1.ne'
        haveI : Fact p.Prime := ⟨hp⟩
        have h_nat : delta2Mid X₁ * (vMid X₁ * x.natAbs) ^ 2 =
            ((delta2Mid X₁ : ℤ) * (vMid X₁ : ℤ) ^ 2 * lucasX (q_n n) X₁ Y₁ r +
              (q_n n : ℤ) * (Y₁ : ℤ) * lucasY (q_n n) X₁ Y₁ r).natAbs ^ 2 := by
          zify; simpa [mul_assoc, mul_pow, sq_abs] using h_id
        have hv_pos : 0 < vMid X₁ := sqPartNat_pos _
        have hLHS_ne : vMid X₁ * x.natAbs ≠ 0 := mul_ne_zero hv_pos.ne' (Int.natAbs_pos.mpr hx_ne).ne'
        have hRHS_ne : ((delta2Mid X₁ : ℤ) * (vMid X₁ : ℤ) ^ 2 * lucasX (q_n n) X₁ Y₁ r +
            (q_n n : ℤ) * (Y₁ : ℤ) * lucasY (q_n n) X₁ Y₁ r).natAbs ≠ 0 := by
          intro h0; rw [h0] at h_nat; simp at h_nat
          rcases h_nat with h_d | h_v | h_x
          · exact (coreNat_pos _).ne' h_d
          · exact hv_pos.ne' h_v
          · exact hx_ne h_x
        have hv := congrArg (padicValNat p) h_nat
        have hd_ne : delta2Mid X₁ ≠ 0 := (coreNat_pos _).ne'
        rw [padicValNat.mul hd_ne (pow_ne_zero 2 hLHS_ne),
            padicValNat_pow_eq, padicValNat_pow_eq] at hv
        have hvp1 : padicValNat p (delta2Mid X₁) = 1 := by
          have h1 := one_le_padicValNat_of_dvd (coreNat_pos _).ne' hpd
          have hle1 : padicValNat p (delta2Mid X₁) ≤ 1 := by
            by_contra hgt
            exact (Nat.squarefree_iff_prime_squarefree.mp (coreNat_squarefree _)) p hp
              (by rw [← sq]; exact dvd_trans (pow_dvd_pow p (by omega : 2 ≤ padicValNat p (delta2Mid X₁))) pow_padicValNat_dvd)
          omega
        rw [hvp1] at hv
        omega
      · have hx2 : X - 1 = x ^ 2 := by dsimp [X]; simp
        have h_id : (delta1Mid X₁ : ℤ) * (uMid X₁ : ℤ) ^ 2 * x ^ 2 =
            ((delta1Mid X₁ : ℤ) * (uMid X₁ : ℤ) ^ 2 * lucasX (q_n n) X₁ Y₁ r +
              (q_n n : ℤ) * (Y₁ : ℤ) * lucasY (q_n n) X₁ Y₁ r) ^ 2 := by
          have h1 : (delta1Mid X₁ : ℤ) * (uMid X₁ : ℤ) ^ 2 = (X₁ : ℤ) - 1 := by
            have h1n : (delta1Mid X₁ : ℤ) * (uMid X₁ : ℤ) ^ 2 = ((X₁ - 1 : ℕ) : ℤ) := by exact_mod_cast h_eq1.symm
            rw [Nat.cast_sub (X1_gt_one hq_ge hfund).le] at h1n; push_cast at h1n; exact h1n
          rw [← hx2, hmX, hX_2r1]
          have hX1_sq : (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 = ((X₁ : ℤ) - 1) * ((X₁ : ℤ) + 1) := by
            have : (X₁ : ℤ) ^ 2 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hfund.2.2.1
            linarith
          rw [h1]
          calc ((X₁ : ℤ) - 1) * ((X₁ : ℤ) * (lucasX (q_n n) X₁ Y₁ r ^ 2 + (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ r ^ 2) +
                2 * (q_n n : ℤ) * (Y₁ : ℤ) * lucasX (q_n n) X₁ Y₁ r * lucasY (q_n n) X₁ Y₁ r - 1)
              = ((X₁ : ℤ) - 1) * ((X₁ : ℤ) * (lucasX (q_n n) X₁ Y₁ r ^ 2 + (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ r ^ 2) +
                2 * (q_n n : ℤ) * (Y₁ : ℤ) * lucasX (q_n n) X₁ Y₁ r * lucasY (q_n n) X₁ Y₁ r -
                (lucasX (q_n n) X₁ Y₁ r ^ 2 - (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ r ^ 2)) := by rw [h_norm_r]
            _ = ((X₁ : ℤ) - 1) ^ 2 * lucasX (q_n n) X₁ Y₁ r ^ 2 +
                2 * ((X₁ : ℤ) - 1) * (q_n n : ℤ) * (Y₁ : ℤ) * lucasX (q_n n) X₁ Y₁ r * lucasY (q_n n) X₁ Y₁ r +
                ((X₁ : ℤ) - 1) * ((X₁ : ℤ) + 1) * (q_n n : ℤ) * lucasY (q_n n) X₁ Y₁ r ^ 2 := by ring
            _ = ((X₁ : ℤ) - 1) ^ 2 * lucasX (q_n n) X₁ Y₁ r ^ 2 +
                2 * ((X₁ : ℤ) - 1) * (q_n n : ℤ) * (Y₁ : ℤ) * lucasX (q_n n) X₁ Y₁ r * lucasY (q_n n) X₁ Y₁ r +
                (q_n n : ℤ) ^ 2 * (Y₁ : ℤ) ^ 2 * lucasY (q_n n) X₁ Y₁ r ^ 2 := by rw [← hX1_sq]; ring
            _ = (((X₁ : ℤ) - 1) * lucasX (q_n n) X₁ Y₁ r + (q_n n : ℤ) * (Y₁ : ℤ) * lucasY (q_n n) X₁ Y₁ r) ^ 2 := by ring
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hδ₁_gt1.ne'
        haveI : Fact p.Prime := ⟨hp⟩
        have h_nat : delta1Mid X₁ * (uMid X₁ * x.natAbs) ^ 2 =
            ((delta1Mid X₁ : ℤ) * (uMid X₁ : ℤ) ^ 2 * lucasX (q_n n) X₁ Y₁ r +
              (q_n n : ℤ) * (Y₁ : ℤ) * lucasY (q_n n) X₁ Y₁ r).natAbs ^ 2 := by
          zify; simpa [mul_assoc, mul_pow, sq_abs] using h_id
        have hu_pos : 0 < uMid X₁ := sqPartNat_pos _
        have hLHS_ne : uMid X₁ * x.natAbs ≠ 0 := mul_ne_zero hu_pos.ne' (Int.natAbs_pos.mpr hx_ne).ne'
        have hRHS_ne : ((delta1Mid X₁ : ℤ) * (uMid X₁ : ℤ) ^ 2 * lucasX (q_n n) X₁ Y₁ r +
            (q_n n : ℤ) * (Y₁ : ℤ) * lucasY (q_n n) X₁ Y₁ r).natAbs ≠ 0 := by
          intro h0; rw [h0] at h_nat; simp at h_nat
          rcases h_nat with h_d | h_u | h_x
          · exact (coreNat_pos _).ne' h_d
          · exact hu_pos.ne' h_u
          · exact hx_ne h_x
        have hv := congrArg (padicValNat p) h_nat
        have hd_ne : delta1Mid X₁ ≠ 0 := (coreNat_pos _).ne'
        rw [padicValNat.mul hd_ne (pow_ne_zero 2 hLHS_ne),
            padicValNat_pow_eq, padicValNat_pow_eq] at hv
        have hvp1 : padicValNat p (delta1Mid X₁) = 1 := by
          have h1 := one_le_padicValNat_of_dvd (coreNat_pos _).ne' hpd
          have hle1 : padicValNat p (delta1Mid X₁) ≤ 1 := by
            by_contra hgt
            exact (Nat.squarefree_iff_prime_squarefree.mp (coreNat_squarefree _)) p hp
              (by rw [← sq]; exact dvd_trans (pow_dvd_pow p (by omega : 2 ≤ padicValNat p (delta1Mid X₁))) pow_padicValNat_dvd)
          omega
        rw [hvp1] at hv
        omega
  exact ⟨h_no_pm2 2 (Or.inl rfl), h_no_pm2 (-2) (Or.inr rfl)⟩

end GrasGreenbergBrocard
