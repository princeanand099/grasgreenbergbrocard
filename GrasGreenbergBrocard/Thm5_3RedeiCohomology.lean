import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic
import GrasGreenbergBrocard.ExternalAxiomsSec3
import GrasGreenbergBrocard.ExternalAxiomsSec4
import GrasGreenbergBrocard.ExternalAxiomsSec5
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.PellFundamental
import GrasGreenbergBrocard.Prop5_1MidpointBias
import GrasGreenbergBrocard.Thm5_2EffectiveCores

/-!
# Theorem 5.3: Rédei–Reichardt 4-Rank Cohomology and Reduced Dual Quartic Laws

Formalizes Section 5.2, Theorem 5.3(i)–(ii), and equations (5.8)–(5.10) of the manuscript:
- `thm_5_3_part1_cohomology_4rank`: Galois cohomology exact sequence (eq. 5.8) and
  `dim_{𝔽₂} ker_{𝔽₂}(R_n^{ram}) = 1 + rank₄ Cl^+(q_n)` (eq. 5.9)
- `PevenPlus`, `PevenMinus`: split-even and inert-even prime partitions `𝒫_even^±(n)`
- `thm_5_3_part2_inert_absorption`: deterministic `𝒫_even^-(n)`-absorption into `z₁, z₂`
- `thm_5_3_part2_dual_quartic`: reduced dual quartic equations (eq. 5.10)
-/

set_option maxHeartbeats 400000

noncomputable section

open Real Finset BigOperators

namespace GrasGreenbergBrocard

/-! ### Theorem 5.3(i): Galois Cohomology Exact Sequence & 4-Rank Identity (Eqs. 5.8–5.9) -/

/-- **Theorem 5.3(i) — Galois Cohomology Exact Sequence and Rédei–Reichardt 4-Rank Identity
(eqs. 5.8–5.9)**:
For any `n ≥ 8` and non-zero midpoint cocycle `y^{mid} ∈ ker_{𝔽₂}(R_n^{ram})`,
there is an exact sequence of `𝔽₂`-vector spaces
`0 → span_{𝔽₂}{y^{mid}} → ker_{𝔽₂}(R_n^{ram}) → Cl^+(q_n)[2] ∩ 2 Cl^+(q_n) → 0`,
and consequently `dim_{𝔽₂} ker_{𝔽₂}(R_n^{ram}) = 1 + rank₄ Cl^+(q_n)`. -/
theorem thm_5_3_part1_cohomology_4rank {n : ℕ} (hn : 8 ≤ n)
    (yMid : redeiKernel n) (hyMid_ne : yMid ≠ 0) :
    ∃ data : RedeiNarrowClassData n yMid,
      Function.Surjective data.psiPlus ∧
      LinearMap.ker data.psiPlus = Submodule.span (ZMod 2) {yMid} ∧
      Module.finrank (ZMod 2) (redeiKernel n) = 1 + data.rank4 := by
  obtain ⟨data⟩ := redei_reichardt_exact_sequence n hn yMid hyMid_ne
  have h_finrank_eq : Module.finrank (ZMod 2) (LinearMap.range data.psiPlus) +
      Module.finrank (ZMod 2) (LinearMap.ker data.psiPlus) =
      Module.finrank (ZMod 2) (redeiKernel n) :=
    LinearMap.finrank_range_add_finrank_ker data.psiPlus
  have h_range : Module.finrank (ZMod 2) (LinearMap.range data.psiPlus) = data.rank4 := by
    rw [LinearMap.range_eq_top.mpr data.psiPlus_surjective, finrank_top, data.h_rank4]
  have h_ker : Module.finrank (ZMod 2) (LinearMap.ker data.psiPlus) = 1 := by
    rw [data.ker_psiPlus_eq_span, finrank_span_singleton hyMid_ne]
  refine ⟨data, data.psiPlus_surjective, data.ker_psiPlus_eq_span, ?_⟩
  omega

/-! ### Theorem 5.3(ii): Deterministic `𝒫_even^-(n)`-Absorption and Reduced Dual Quartic Laws -/

/-- Split-even primes `𝒫_even^+(n) = {q ∈ 𝒫_even(n) \ {2} : (-q_n / q) = +1}`. -/
def PevenPlus (n : ℕ) : Finset ℕ :=
  (Peven n).filter (fun q => 3 ≤ q ∧ chiLegendre (-(q_n n : ℤ)) q = 1)

/-- Inert-even primes `𝒫_even^-(n) = {q ∈ 𝒫_even(n) \ {2} : (-q_n / q) = -1}`. -/
def PevenMinus (n : ℕ) : Finset ℕ :=
  (Peven n).filter (fun q => 3 ≤ q ∧ chiLegendre (-(q_n n : ℤ)) q = -1)

/-- Split-even square-root factor `W_i = ∏_{q ∈ 𝒫_even^+(n), q ∣ z_i} q^{v_q(n!)/2}`. -/
def W_split (n z : ℕ) : ℕ :=
  ∏ q ∈ (PevenPlus n).filter (· ∣ z), q ^ (padicValNat q (Nat.factorial n) / 2)

/-- Absorbed factor `B̃_i = u_i / W_i^2` absorbing 2-adic, odd-valuation, and inert-even powers. -/
def B_tilde (n u z : ℕ) : ℕ :=
  u / (W_split n z) ^ 2

/-- Total split-even factor `A_{n,+}^* = ∏_{q ∈ 𝒫_even^+(n)} q^{v_q(n!)}`. -/
def A_plus_star (n : ℕ) : ℕ :=
  ∏ q ∈ PevenPlus n, q ^ padicValNat q (Nat.factorial n)

lemma W_split_pos (n z : ℕ) : 0 < W_split n z := by
  unfold W_split
  exact Finset.prod_pos (fun q hq => pow_pos (by
    have := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1; omega) _)

lemma A_plus_star_pos (n : ℕ) : 0 < A_plus_star n := by
  unfold A_plus_star
  exact Finset.prod_pos (fun q hq => pow_pos (by
    have := (Finset.mem_filter.mp hq).2.1; omega) _)

/-- **Theorem 5.3(ii), part 1 — Deterministic `𝒫_even^-(n)`-Absorption**:
For any solution `(n, m)` to `n! + 1 = m^2` with `n ≥ 4`, `u₁ = (m - 1)/2 = δ₁ z₁^2`,
`u₂ = (m + 1)/2 = δ₂ z₂^2`, every inert prime `q ∈ 𝒫_even^-(n)` satisfies:
`q ∣ z₁ ↔ (δ₂ / q) = +1` and `q ∣ z₂ ↔ (δ₂ / q) = -1`. -/
theorem thm_5_3_part2_inert_absorption {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2)
    {q : ℕ} (hq : q ∈ PevenMinus n) :
    let u₁ := (m - 1) / 2
    let u₂ := (m + 1) / 2
    let δ₂ := coreNat u₂
    let z₁ := sqPartNat u₁
    let z₂ := sqPartNat u₂
    (q ∣ z₁ ↔ chiLegendre (δ₂ : ℤ) q = 1) ∧
    (q ∣ z₂ ↔ chiLegendre (δ₂ : ℤ) q = -1) := by
  have hmem := Finset.mem_filter.mp hq
  have hq_peven := Finset.mem_filter.mp hmem.1
  have hq_le_n : q ≤ n := (Finset.mem_Icc.mp hq_peven.1).2
  have hq_pr : q.Prime := hq_peven.2.1
  have hq_even : padicValNat q (Nat.factorial n) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hq_peven.2.2
  have hq3 : 3 ≤ q := hmem.2.1
  have hq_inert : chiLegendre (-(q_n n : ℤ)) q = -1 := hmem.2.2
  haveI : Fact q.Prime := ⟨hq_pr⟩
  have ⟨hδ_prod, _, hz_prod, hdiff, _, _⟩ := thm_5_2_part1_bipartition hn hm
  set u₁ := (m - 1) / 2
  set u₂ := (m + 1) / 2
  set δ₁ := coreNat u₁
  set δ₂ := coreNat u₂
  set z₁ := sqPartNat u₁
  set z₂ := sqPartNat u₂
  have hq_dvd_fac : q ∣ Nat.factorial n := hq_pr.dvd_factorial.mpr hq_le_n
  have hq_val_ge1 : 1 ≤ padicValNat q (Nat.factorial n) :=
    one_le_padicValNat_of_dvd (Nat.factorial_pos n).ne' hq_dvd_fac
  have hq_val_ge2 : 2 ≤ padicValNat q (Nat.factorial n) := by omega
  have hq2_dvd_fac : q ^ 2 ∣ Nat.factorial n :=
    (padicValNat_dvd_iff_le (Nat.factorial_pos n).ne').mpr hq_val_ge2
  have hfac_qs := factorial_eq_q_n_mul_s_n_sq n
  have hq_nd_qn : ¬ q ∣ q_n n := by
    intro hqd
    have hvp1 : padicValNat q (Nat.factorial n) = 1 + 2 * padicValNat q (s_n n) := by
      have hq_pos : 0 < q_n n := (q_n_squarefree n).ne_zero |> Nat.pos_of_ne_zero
      have hs_pos : 0 < s_n n := Nat.pos_of_ne_zero (fun h0 => by
        rw [h0] at hfac_qs; simp at hfac_qs; exact (Nat.factorial_pos n).ne' hfac_qs)
      have hv := congrArg (padicValNat q) hfac_qs
      rw [padicValNat.mul hq_pos.ne' (pow_ne_zero 2 hs_pos.ne'), padicValNat_pow_eq] at hv
      have hvpq1 : padicValNat q (q_n n) = 1 := by
        have h1 := one_le_padicValNat_of_dvd hq_pos.ne' hqd
        have hle1 : padicValNat q (q_n n) ≤ 1 := by
          by_contra hgt
          exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) q hq_pr
            (by rw [← sq]; exact dvd_trans (pow_dvd_pow q (by omega : 2 ≤ padicValNat q (q_n n))) pow_padicValNat_dvd)
        omega
      omega
    omega
  have hq_dvd_sn : q ∣ s_n n := by
    have hq2_dvd_qs : q ^ 2 ∣ q_n n * (s_n n) ^ 2 := hfac_qs ▸ hq2_dvd_fac
    have hcop : Nat.Coprime (q ^ 2) (q_n n) :=
      ((hq_pr.coprime_iff_not_dvd).mpr hq_nd_qn).pow_left 2
    have hq2_dvd_s2 : q ^ 2 ∣ (s_n n) ^ 2 := hcop.dvd_of_dvd_mul_left hq2_dvd_qs
    exact hq_pr.dvd_of_dvd_pow (dvd_trans (dvd_pow_self q (by norm_num)) hq2_dvd_s2)
  have hq_dvd_z1z2 : q ∣ z₁ * z₂ := by
    rw [hz_prod]
    have h2q : Nat.Coprime q 2 := (Nat.coprime_primes hq_pr Nat.prime_two).mpr (by omega)
    have hs_eq : 2 * (s_n n / 2) = s_n n := by
      have ⟨_, _, _, _, _, _, h2s⟩ := brocard_u1_u2_rel hn hm
      exact Nat.mul_div_cancel' h2s
    exact h2q.dvd_of_dvd_mul_left (hs_eq.symm ▸ hq_dvd_sn)
  have hq_not_both : ¬ (q ∣ z₁ ∧ q ∣ z₂) := by
    rintro ⟨h1, h2⟩
    have ⟨hu1_pos, hu2_pos, _, hcop_u, _⟩ := brocard_u1_u2_rel hn hm
    have h1_eq : coreNat u₁ * sqPartNat u₁ ^ 2 = u₁ := coreNat_mul_sqPartNat_sq hu1_pos
    have h2_eq : coreNat u₂ * sqPartNat u₂ ^ 2 = u₂ := coreNat_mul_sqPartNat_sq hu2_pos
    have h_u1 : q ∣ u₁ := h1_eq ▸ dvd_mul_of_dvd_right (dvd_pow h1 (by norm_num)) _
    have h_u2 : q ∣ u₂ := h2_eq ▸ dvd_mul_of_dvd_right (dvd_pow h2 (by norm_num)) _
    have := Nat.dvd_gcd h_u1 h_u2
    rw [hcop_u.gcd_eq_one] at this
    exact hq_pr.ne_one (Nat.dvd_one.mp this)
  have h_leg_prod : chiLegendre (-(δ₁ : ℤ)) q * chiLegendre (δ₂ : ℤ) q = -1 := by
    unfold chiLegendre at hq_inert ⊢
    simp only [dif_pos hq_pr] at hq_inert ⊢
    have hq_eq : (-(q_n n : ℤ)) = (-(δ₁ : ℤ)) * (δ₂ : ℤ) := by
      have : q_n n = δ₁ * δ₂ := hδ_prod.symm
      rw [this]; push_cast; ring
    rw [hq_eq, legendreSym.mul] at hq_inert
    exact hq_inert
  have hz1_imp : q ∣ z₁ → chiLegendre (δ₂ : ℤ) q = 1 := by
    intro hqz1
    have hqz1_z : ((z₁ : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (by exact_mod_cast hqz1)
    have hmod := congrArg (Int.cast (R := ZMod q)) hdiff
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_one] at hmod
    rw [hqz1_z, zero_pow (by norm_num), mul_zero, sub_zero] at hmod
    have hz2_ne : ((z₂ : ℤ) : ZMod q) ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num), mul_zero] at hmod
      exact zero_ne_one hmod
    have hd2_ne : ((δ₂ : ℤ) : ZMod q) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmod
      exact zero_ne_one hmod
    have hsq : IsSquare ((δ₂ : ℤ) : ZMod q) := by
      refine ⟨((z₂ : ℤ) : ZMod q)⁻¹, ?_⟩
      have hinv : ((z₂ : ℤ) : ZMod q) * ((z₂ : ℤ) : ZMod q)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ (isUnit_iff_ne_zero.mpr hz2_ne)
      calc ((δ₂ : ℤ) : ZMod q) = ((δ₂ : ℤ) : ZMod q) * (((z₂ : ℤ) : ZMod q) * ((z₂ : ℤ) : ZMod q)⁻¹) ^ 2 := by
            rw [hinv, one_pow, mul_one]
        _ = (((δ₂ : ℤ) : ZMod q) * ((z₂ : ℤ) : ZMod q) ^ 2) * (((z₂ : ℤ) : ZMod q)⁻¹) ^ 2 := by ring
        _ = (((z₂ : ℤ) : ZMod q)⁻¹) * (((z₂ : ℤ) : ZMod q)⁻¹) := by rw [hmod, one_mul, sq]
    unfold chiLegendre
    simp only [dif_pos hq_pr]
    exact (legendreSym.eq_one_iff q hd2_ne).mpr hsq
  have hz2_imp : q ∣ z₂ → chiLegendre (δ₂ : ℤ) q = -1 := by
    intro hqz2
    have hqz2_z : ((z₂ : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (by exact_mod_cast hqz2)
    have hmod := congrArg (Int.cast (R := ZMod q)) hdiff
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_one] at hmod
    rw [hqz2_z, zero_pow (by norm_num), mul_zero, zero_sub] at hmod
    have hz1_ne : ((z₁ : ℤ) : ZMod q) ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num), mul_zero, neg_zero] at hmod
      exact zero_ne_one hmod
    have hd1_ne : ((-(δ₁ : ℤ) : ℤ) : ZMod q) ≠ 0 := by
      intro h0
      have h0' : -((δ₁ : ℤ) : ZMod q) = 0 := by simpa using h0
      have h_eq0 : ((δ₁ : ℤ) : ZMod q) = 0 := neg_eq_zero.mp h0'
      rw [h_eq0, zero_mul, neg_zero] at hmod
      exact zero_ne_one hmod
    have hsq : IsSquare ((-(δ₁ : ℤ) : ℤ) : ZMod q) := by
      refine ⟨((z₁ : ℤ) : ZMod q)⁻¹, ?_⟩
      have hinv : ((z₁ : ℤ) : ZMod q) * ((z₁ : ℤ) : ZMod q)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ (isUnit_iff_ne_zero.mpr hz1_ne)
      have hmod' : ((-(δ₁ : ℤ) : ℤ) : ZMod q) * ((z₁ : ℤ) : ZMod q) ^ 2 = 1 := by
        rw [Int.cast_neg, neg_mul]; exact hmod
      calc ((-(δ₁ : ℤ) : ℤ) : ZMod q) = ((-(δ₁ : ℤ) : ℤ) : ZMod q) * (((z₁ : ℤ) : ZMod q) * ((z₁ : ℤ) : ZMod q)⁻¹) ^ 2 := by
            rw [hinv, one_pow, mul_one]
        _ = (((-(δ₁ : ℤ) : ℤ) : ZMod q) * ((z₁ : ℤ) : ZMod q) ^ 2) * (((z₁ : ℤ) : ZMod q)⁻¹) ^ 2 := by ring
        _ = (((z₁ : ℤ) : ZMod q)⁻¹) * (((z₁ : ℤ) : ZMod q)⁻¹) := by rw [hmod', one_mul, sq]
    have h_leg1 : chiLegendre (-(δ₁ : ℤ)) q = 1 := by
      unfold chiLegendre; simp only [dif_pos hq_pr]
      exact (legendreSym.eq_one_iff q hd1_ne).mpr hsq
    rw [h_leg1, one_mul] at h_leg_prod
    exact h_leg_prod
  rcases hq_pr.dvd_mul.mp hq_dvd_z1z2 with h1 | h2
  · have h2_nd : ¬ q ∣ z₂ := fun h2 => hq_not_both ⟨h1, h2⟩
    have hleg := hz1_imp h1
    constructor
    · exact ⟨fun _ => hleg, fun _ => h1⟩
    · exact ⟨fun h => absurd h h2_nd, fun h => by rw [hleg] at h; omega⟩
  · have h1_nd : ¬ q ∣ z₁ := fun h1 => hq_not_both ⟨h1, h2⟩
    have hleg := hz2_imp h2
    constructor
    · exact ⟨fun h => absurd h h1_nd, fun h => by rw [hleg] at h; omega⟩
    · exact ⟨fun _ => hleg, fun _ => h2⟩

/-- **Theorem 5.3(ii), part 2 — Reduced Dual Quartic Laws (eq. 5.10)**:
Writing `u₁ = Btilde₁ W₁^2` and `u₂ = Btilde₂ W₂^2` where `W_i = ∏_{q ∈ 𝒫_even^+(n), q ∣ z_i} q^{v_q(n!)/2}`,
we have `(W₁ W₂)^2 = A_{n,+}^*` and the dual quartic equations:
`Btilde₂ A_{n,+}^* = Btilde₁ W₁^4 + W₁^2` and `Btilde₁ A_{n,+}^* = Btilde₂ W₂^4 - W₂^2`. -/
theorem thm_5_3_part2_dual_quartic {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    let u₁ := (m - 1) / 2
    let u₂ := (m + 1) / 2
    let z₁ := sqPartNat u₁
    let z₂ := sqPartNat u₂
    let W₁ := W_split n z₁
    let W₂ := W_split n z₂
    let Btilde₁ := B_tilde n u₁ z₁
    let Btilde₂ := B_tilde n u₂ z₂
    u₁ = Btilde₁ * W₁ ^ 2 ∧
    u₂ = Btilde₂ * W₂ ^ 2 ∧
    (W₁ * W₂) ^ 2 = A_plus_star n ∧
    Btilde₂ * A_plus_star n = Btilde₁ * W₁ ^ 4 + W₁ ^ 2 ∧
    Btilde₁ * A_plus_star n = Btilde₂ * W₂ ^ 4 - W₂ ^ 2 := by
  have ⟨hu₁_pos, hu₂_pos, hu_diff, hcop_u, h4mul, hu_qs, h2_dvd_sn⟩ := brocard_u1_u2_rel hn hm
  have ⟨hδ_prod, _, hz_prod, _, _, _⟩ := thm_5_2_part1_bipartition hn hm
  set u₁ := (m - 1) / 2
  set u₂ := (m + 1) / 2
  set δ₁ := coreNat u₁
  set δ₂ := coreNat u₂
  set z₁ := sqPartNat u₁
  set z₂ := sqPartNat u₂
  set W₁ := W_split n z₁
  set W₂ := W_split n z₂
  set Btilde₁ := B_tilde n u₁ z₁
  set Btilde₂ := B_tilde n u₂ z₂
  have hz₁_pos : 0 < z₁ := sqPartNat_pos u₁
  have hz₂_pos : 0 < z₂ := sqPartNat_pos u₂
  have h1_eq : δ₁ * z₁ ^ 2 = u₁ := coreNat_mul_sqPartNat_sq hu₁_pos
  have h2_eq : δ₂ * z₂ ^ 2 = u₂ := coreNat_mul_sqPartNat_sq hu₂_pos
  have hz1_u1 : z₁ ∣ u₁ := h1_eq ▸ dvd_mul_of_dvd_right (dvd_pow_self z₁ (by norm_num)) δ₁
  have hz2_u2 : z₂ ∣ u₂ := h2_eq ▸ dvd_mul_of_dvd_right (dvd_pow_self z₂ (by norm_num)) δ₂
  have hcop_z : Nat.Coprime z₁ z₂ := (hcop_u.coprime_dvd_left hz1_u1).coprime_dvd_right hz2_u2
  have h_val_z : ∀ q : ℕ, q ∈ PevenPlus n →
      (q ∣ z₁ → padicValNat q z₁ = padicValNat q (Nat.factorial n) / 2) ∧
      (q ∣ z₂ → padicValNat q z₂ = padicValNat q (Nat.factorial n) / 2) ∧
      (q ∣ z₁ ∨ q ∣ z₂) := by
    intro q hq
    have hq_mem := Finset.mem_filter.mp hq
    have hq_pe := Finset.mem_filter.mp hq_mem.1
    have hq_le_n : q ≤ n := (Finset.mem_Icc.mp hq_pe.1).2
    have hq_pr : q.Prime := hq_pe.2.1
    have hq_even : padicValNat q (Nat.factorial n) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hq_pe.2.2
    have hq3 : 3 ≤ q := hq_mem.2.1
    haveI : Fact q.Prime := ⟨hq_pr⟩
    have hq_dvd_fac : q ∣ Nat.factorial n := hq_pr.dvd_factorial.mpr hq_le_n
    have hq_val_ge2 : 2 ≤ padicValNat q (Nat.factorial n) := by
      have := one_le_padicValNat_of_dvd (Nat.factorial_pos n).ne' hq_dvd_fac
      omega
    have hfac_qs := factorial_eq_q_n_mul_s_n_sq n
    have hq_nd_qn : ¬ q ∣ q_n n := by
      intro hqd
      have hq_pos : 0 < q_n n := (q_n_squarefree n).ne_zero |> Nat.pos_of_ne_zero
      have hs_pos : 0 < s_n n := Nat.pos_of_ne_zero (fun h0 => by
        rw [h0] at hfac_qs; simp at hfac_qs; exact (Nat.factorial_pos n).ne' hfac_qs)
      have hv := congrArg (padicValNat q) hfac_qs
      rw [padicValNat.mul hq_pos.ne' (pow_ne_zero 2 hs_pos.ne'), padicValNat_pow_eq] at hv
      have hvpq1 : padicValNat q (q_n n) = 1 := by
        have h1 := one_le_padicValNat_of_dvd hq_pos.ne' hqd
        have hle1 : padicValNat q (q_n n) ≤ 1 := by
          by_contra hgt
          exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) q hq_pr
            (by rw [← sq]; exact dvd_trans (pow_dvd_pow q (by omega : 2 ≤ padicValNat q (q_n n))) pow_padicValNat_dvd)
        omega
      omega
    have hq_dvd_sn : q ∣ s_n n := by
      have hq2_dvd_fac : q ^ 2 ∣ Nat.factorial n :=
        (padicValNat_dvd_iff_le (Nat.factorial_pos n).ne').mpr hq_val_ge2
      have hq2_dvd_qs : q ^ 2 ∣ q_n n * (s_n n) ^ 2 := hfac_qs ▸ hq2_dvd_fac
      have hcop : Nat.Coprime (q ^ 2) (q_n n) :=
        ((hq_pr.coprime_iff_not_dvd).mpr hq_nd_qn).pow_left 2
      exact hq_pr.dvd_of_dvd_pow (dvd_trans (dvd_pow_self q (by norm_num)) (hcop.dvd_of_dvd_mul_left hq2_dvd_qs))
    have hq_dvd_z1z2 : q ∣ z₁ * z₂ := by
      rw [hz_prod]
      have h2q : Nat.Coprime q 2 := (Nat.coprime_primes hq_pr Nat.prime_two).mpr (by omega)
      have hs_eq : 2 * (s_n n / 2) = s_n n := Nat.mul_div_cancel' h2_dvd_sn
      exact h2q.dvd_of_dvd_mul_left (hs_eq.symm ▸ hq_dvd_sn)
    have h_or := hq_pr.dvd_mul.mp hq_dvd_z1z2
    have h4u : 4 * (u₁ * u₂) = Nat.factorial n := by linarith
    have hv_fac_4u := congrArg (padicValNat q) h4u
    have hq_nd4 : ¬ q ∣ 4 := fun hd =>
      (by omega : q ≠ 2) ((Nat.prime_dvd_prime_iff_eq hq_pr Nat.prime_two).mp
        (hq_pr.dvd_of_dvd_pow (show q ∣ 2 ^ 2 by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hd)))
    rw [padicValNat.mul (by norm_num) (mul_pos hu₁_pos hu₂_pos).ne',
        padicValNat.eq_zero_of_not_dvd hq_nd4,
        zero_add, padicValNat.mul hu₁_pos.ne' hu₂_pos.ne'] at hv_fac_4u
    refine ⟨fun hqz1 => ?_, fun hqz2 => ?_, h_or⟩
    · have hqz2_nd : ¬ q ∣ z₂ := fun h2 =>
        hq_pr.ne_one (Nat.dvd_one.mp (hcop_z.gcd_eq_one ▸ Nat.dvd_gcd hqz1 h2))
      have hqu1 : q ∣ u₁ := h1_eq ▸ dvd_mul_of_dvd_right (dvd_pow hqz1 (by norm_num)) _
      have hqu2_nd : ¬ q ∣ u₂ := fun h2 =>
        hq_pr.ne_one (Nat.dvd_one.mp (hcop_u.gcd_eq_one ▸ Nat.dvd_gcd hqu1 h2))
      have hv0 : padicValNat q u₂ = 0 := padicValNat.eq_zero_of_not_dvd hqu2_nd
      rw [padicValNat_sqPartNat hq_pr, ← hv_fac_4u, hv0, add_zero]
    · have hqz1_nd : ¬ q ∣ z₁ := fun h1 =>
        hq_pr.ne_one (Nat.dvd_one.mp (hcop_z.gcd_eq_one ▸ Nat.dvd_gcd h1 hqz2))
      have hqu2 : q ∣ u₂ := h2_eq ▸ dvd_mul_of_dvd_right (dvd_pow hqz2 (by norm_num)) _
      have hqu1_nd : ¬ q ∣ u₁ := fun h1 =>
        hq_pr.ne_one (Nat.dvd_one.mp (hcop_u.gcd_eq_one ▸ Nat.dvd_gcd h1 hqu2))
      have hv0 : padicValNat q u₁ = 0 := padicValNat.eq_zero_of_not_dvd hqu1_nd
      rw [padicValNat_sqPartNat hq_pr, ← hv_fac_4u, hv0, zero_add]
  have h_prod_dvd_nat : ∀ (z : ℕ) (S : Finset ℕ) (f : ℕ → ℕ),
      (∀ q ∈ S, q.Prime ∧ q ^ f q ∣ z) → (∏ q ∈ S, q ^ f q) ∣ z := by
    intro z S f hS
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a s has ih =>
      rw [Finset.prod_insert has]
      have ha := hS a (Finset.mem_insert_self a s)
      have hs := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
      have hcop : Nat.Coprime (a ^ f a) (∏ q ∈ s, q ^ f q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        have hq_pr := (hS q (Finset.mem_insert_of_mem hq)).1
        exact ((Nat.coprime_primes ha.1 hq_pr).mpr (fun h => has (h ▸ hq))).pow _ _
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop ha.2 hs
  have hW1_dvd_z1 : W₁ ∣ z₁ := by
    unfold W₁ W_split
    apply h_prod_dvd_nat
    intro q hq
    have hq_mem := Finset.mem_filter.mp hq
    have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq_mem.1).1).2.1
    haveI : Fact q.Prime := ⟨hq_pr⟩
    refine ⟨hq_pr, ?_⟩
    rw [← (h_val_z q hq_mem.1).1 hq_mem.2]
    exact pow_padicValNat_dvd
  have hW2_dvd_z2 : W₂ ∣ z₂ := by
    unfold W₂ W_split
    apply h_prod_dvd_nat
    intro q hq
    have hq_mem := Finset.mem_filter.mp hq
    have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hq_mem.1).1).2.1
    haveI : Fact q.Prime := ⟨hq_pr⟩
    refine ⟨hq_pr, ?_⟩
    rw [← (h_val_z q hq_mem.1).2.1 hq_mem.2]
    exact pow_padicValNat_dvd
  have hW1_sq_u1 : W₁ ^ 2 ∣ u₁ := h1_eq ▸ dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hW1_dvd_z1 2) _
  have hW2_sq_u2 : W₂ ^ 2 ∣ u₂ := h2_eq ▸ dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hW2_dvd_z2 2) _
  have hu1_eq : u₁ = Btilde₁ * W₁ ^ 2 := (Nat.div_mul_cancel hW1_sq_u1).symm
  have hu2_eq : u₂ = Btilde₂ * W₂ ^ 2 := (Nat.div_mul_cancel hW2_sq_u2).symm
  have h_disj : Disjoint ((PevenPlus n).filter (· ∣ z₁)) ((PevenPlus n).filter (· ∣ z₂)) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    have hq_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq1).1).1).2.1
    have h1 := (Finset.mem_filter.mp hq1).2
    have h2 := (Finset.mem_filter.mp hq2).2
    exact hq_pr.ne_one (Nat.dvd_one.mp (hcop_z.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))
  have h_union : (PevenPlus n).filter (· ∣ z₁) ∪ (PevenPlus n).filter (· ∣ z₂) = PevenPlus n := by
    ext q
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
    · intro hq
      rcases (h_val_z q hq).2.2 with h1 | h2
      · exact Or.inl ⟨hq, h1⟩
      · exact Or.inr ⟨hq, h2⟩
  have hW_sq_eq : (W₁ * W₂) ^ 2 = A_plus_star n := by
    unfold W₁ W₂ W_split A_plus_star
    rw [← Finset.prod_union h_disj, h_union, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro q hq
    have hq_even : padicValNat q (Nat.factorial n) % 2 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.2
    rw [← pow_mul]
    congr 1
    omega
  have h_diff_B : (Btilde₂ : ℤ) * (W₂ : ℤ) ^ 2 - (Btilde₁ : ℤ) * (W₁ : ℤ) ^ 2 = 1 := by
    have h1z : (Btilde₁ : ℤ) * (W₁ : ℤ) ^ 2 = (u₁ : ℤ) := by exact_mod_cast hu1_eq.symm
    have h2z : (Btilde₂ : ℤ) * (W₂ : ℤ) ^ 2 = (u₂ : ℤ) := by exact_mod_cast hu2_eq.symm
    have hdz : (u₂ : ℤ) = (u₁ : ℤ) + 1 := by exact_mod_cast hu_diff
    linarith
  have hq1_z : (Btilde₂ : ℤ) * (A_plus_star n : ℤ) = (Btilde₁ : ℤ) * (W₁ : ℤ) ^ 4 + (W₁ : ℤ) ^ 2 := by
    have hA_z : (A_plus_star n : ℤ) = ((W₁ : ℤ) * (W₂ : ℤ)) ^ 2 := by exact_mod_cast hW_sq_eq.symm
    rw [hA_z]
    have hmul := congrArg (· * (W₁ : ℤ) ^ 2) h_diff_B
    linarith
  have hq2_z : (Btilde₁ : ℤ) * (A_plus_star n : ℤ) = (Btilde₂ : ℤ) * (W₂ : ℤ) ^ 4 - (W₂ : ℤ) ^ 2 := by
    have hA_z : (A_plus_star n : ℤ) = ((W₁ : ℤ) * (W₂ : ℤ)) ^ 2 := by exact_mod_cast hW_sq_eq.symm
    rw [hA_z]
    have hmul := congrArg (· * (W₂ : ℤ) ^ 2) h_diff_B
    linarith
  have hq1 : Btilde₂ * A_plus_star n = Btilde₁ * W₁ ^ 4 + W₁ ^ 2 := by exact_mod_cast hq1_z
  have hq2 : Btilde₁ * A_plus_star n = Btilde₂ * W₂ ^ 4 - W₂ ^ 2 := by
    have hq2_nat : Btilde₁ * A_plus_star n + W₂ ^ 2 = Btilde₂ * W₂ ^ 4 := by
      have : ((Btilde₁ * A_plus_star n + W₂ ^ 2 : ℕ) : ℤ) = ((Btilde₂ * W₂ ^ 4 : ℕ) : ℤ) := by
        push_cast; linarith [hq2_z]
      exact_mod_cast this
    omega
  exact ⟨hu1_eq, hu2_eq, hW_sq_eq, hq1, hq2⟩

end GrasGreenbergBrocard
