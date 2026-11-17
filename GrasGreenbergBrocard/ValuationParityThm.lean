import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.ValuationParityDigits
import GrasGreenbergBrocard.ValuationParityVaaler
import GrasGreenbergBrocard.ExpSumBounds

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false

/-!
# Theorem 2.5: Valuation-Parity Equidistribution and Second-Order Discrepancy Law

Formalizes Section 2.3 (eq. 2.15–2.18):
- `Delta_parity_second_order` (Theorem 2.5(i), eq. 2.15)
- `small_prime_parity_band_bound` (Theorem 2.5(ii), eq. 2.16)
- `Sigma_star_parity_isLittleO_log`, `Delta_parity_isLittleO_mul_log`,
  `S_odd_asymptotic`, `S_even_asymptotic` (Theorem 2.5(ii), eq. 2.17)
- `multi_modulus_power_band_equidistribution` (Theorem 2.5(iii), eq. 2.18)
-/

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard

/-! ### Dyadic Partition and Mertens Helpers -/

/-- Dyadic block index set for `(A, B]` with `1 ≤ A ≤ B`:
`k ∈ dyadicBlocks A B` iff `k ≤ ⌈log(B/A)/log 2⌉` and `A * 2^k < B`. -/
def dyadicBlocks (A B : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil (Real.log (B / A) / Real.log 2) + 1)).filter
    (fun k => A * (2 : ℝ) ^ k < B)

theorem dyadicBlocks_card_le {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    ((dyadicBlocks A B).card : ℝ) ≤ Real.log (B / A) / Real.log 2 + 2 := by
  have h1 : (dyadicBlocks A B).card ≤ Nat.ceil (Real.log (B / A) / Real.log 2) + 1 := by
    calc (dyadicBlocks A B).card ≤ (Finset.range (Nat.ceil (Real.log (B / A) / Real.log 2) + 1)).card :=
          Finset.card_filter_le _ _
      _ = Nat.ceil (Real.log (B / A) / Real.log 2) + 1 := Finset.card_range _
  have hnonneg : 0 ≤ Real.log (B / A) / Real.log 2 := by
    apply div_nonneg
    · exact Real.log_nonneg ((one_le_div (by linarith)).mpr hAB)
    · exact (Real.log_pos (by norm_num)).le
  have hceil : (Nat.ceil (Real.log (B / A) / Real.log 2) : ℝ) < Real.log (B / A) / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one hnonneg
  have h1R : ((dyadicBlocks A B).card : ℝ) ≤ (Nat.ceil (Real.log (B / A) / Real.log 2) : ℝ) + 1 := by
    exact_mod_cast h1
  linarith

theorem dyadic_partition_finset {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) (I : Finset ℕ)
    (hI : ∀ p ∈ I, A < (p : ℝ) ∧ (p : ℝ) ≤ B) :
    I = (dyadicBlocks A B).biUnion
      (fun k => I.filter (fun p => A * (2 : ℝ) ^ k < (p : ℝ) ∧ (p : ℝ) ≤ 2 * (A * (2 : ℝ) ^ k))) ∧
    ((dyadicBlocks A B : Set ℕ).PairwiseDisjoint
      (fun k => I.filter (fun p => A * (2 : ℝ) ^ k < (p : ℝ) ∧ (p : ℝ) ≤ 2 * (A * (2 : ℝ) ^ k)))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · ext p
    simp only [Finset.mem_biUnion, Finset.mem_filter, dyadicBlocks, Finset.mem_range]
    constructor
    · intro hp
      obtain ⟨hpA, hpB⟩ := hI p hp
      have hp_pos : 0 < (p : ℝ) := by linarith
      have hdiv_gt : 1 < (p : ℝ) / A := (one_lt_div (by linarith)).mpr hpA
      have hlog_pos : 0 < Real.log ((p : ℝ) / A) / Real.log 2 :=
        div_pos (Real.log_pos hdiv_gt) hlog2
      let m := Nat.ceil (Real.log ((p : ℝ) / A) / Real.log 2)
      have hm_pos : 1 ≤ m := Nat.ceil_pos.mpr hlog_pos
      let k := m - 1
      have hk1 : k + 1 = m := by omega
      have h_lt : (k : ℝ) < Real.log ((p : ℝ) / A) / Real.log 2 := by
        have := Nat.lt_ceil.mp (by omega : k < m)
        exact this
      have h_le : Real.log ((p : ℝ) / A) / Real.log 2 ≤ (k : ℝ) + 1 := by
        have := Nat.le_ceil (Real.log ((p : ℝ) / A) / Real.log 2)
        rw [← hk1] at this
        push_cast at this
        exact this
      have hpow_lt : A * (2 : ℝ) ^ k < (p : ℝ) := by
        have h1 : (k : ℝ) * Real.log 2 < Real.log ((p : ℝ) / A) := (lt_div_iff₀ hlog2).mp h_lt
        have h2 : (2 : ℝ) ^ k < (p : ℝ) / A := by
          rw [← Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ k),
            ← Real.exp_log (by positivity : 0 < (p : ℝ) / A)]
          apply Real.exp_lt_exp.mpr
          rwa [Real.log_pow]
        exact (lt_div_iff₀ (by linarith)).mp h2
      have hpow_le : (p : ℝ) ≤ 2 * (A * (2 : ℝ) ^ k) := by
        have h1 : Real.log ((p : ℝ) / A) ≤ ((k : ℝ) + 1) * Real.log 2 := (div_le_iff₀ hlog2).mp h_le
        have h2 : (p : ℝ) / A ≤ (2 : ℝ) ^ (k + 1) := by
          rw [← Real.exp_log (by positivity : 0 < (p : ℝ) / A),
            ← Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k + 1))]
          apply Real.exp_le_exp.mpr
          rw [Real.log_pow]; push_cast; linarith
        rw [pow_succ'] at h2
        have h3 := (div_le_iff₀ (by linarith)).mp h2
        linarith
      have hm_le : m ≤ Nat.ceil (Real.log (B / A) / Real.log 2) := by
        apply Nat.ceil_mono
        exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hpB (by linarith))) hlog2.le
      refine ⟨k, ⟨by omega, lt_of_lt_of_le hpow_lt hpB⟩, hp, hpow_lt, hpow_le⟩
    · rintro ⟨k, _, hp, _⟩
      exact hp
  · intro k₁ _ k₂ _ hne
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    have h12 : A * (2 : ℝ) ^ k₁ < 2 * (A * (2 : ℝ) ^ k₂) := lt_of_lt_of_le hp1.2.1 hp2.2.2
    have h21 : A * (2 : ℝ) ^ k₂ < 2 * (A * (2 : ℝ) ^ k₁) := lt_of_lt_of_le hp2.2.1 hp1.2.2
    have hA_pos : 0 < A := by linarith
    have hk12 : (2 : ℝ) ^ k₁ < (2 : ℝ) ^ (k₂ + 1) := by
      rw [pow_succ']
      nlinarith
    have hk21 : (2 : ℝ) ^ k₂ < (2 : ℝ) ^ (k₁ + 1) := by
      rw [pow_succ']
      nlinarith
    have hk12N : k₁ < k₂ + 1 := (pow_lt_pow_iff_right₀ (by norm_num)).mp hk12
    have hk21N : k₂ < k₁ + 1 := (pow_lt_pow_iff_right₀ (by norm_num)).mp hk21
    omega

theorem mertens_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      ∑ p ∈ (Finset.Icc 3 (Nat.floor x)).filter Nat.Prime,
        Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ Real.log x + C := by
  obtain ⟨C, hC, hM⟩ := mertens_first_theorem
  refine ⟨C, hC, fun x hx => ?_⟩
  linarith [(abs_le.mp (hM x hx)).2]

theorem mertens_band_le :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : ℝ, 3 ≤ A → A ≤ B →
      ∑ p ∈ ((Finset.Icc 3 (Nat.floor B)).filter Nat.Prime).filter (fun p => A < (p : ℝ)),
        Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ Real.log (B / A) + C := by
  obtain ⟨Cm, hCm, hM⟩ := mertens_first_theorem
  refine ⟨2 * Cm, by positivity, fun A B hA hAB => ?_⟩
  have hB : 3 ≤ B := le_trans hA hAB
  have hsub : (Finset.Icc 3 (Nat.floor A)).filter Nat.Prime ⊆
      (Finset.Icc 3 (Nat.floor B)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_mono hAB)⟩, hp.2⟩
  have h_eq : ((Finset.Icc 3 (Nat.floor B)).filter Nat.Prime).filter (fun p => A < (p : ℝ)) =
      (Finset.Icc 3 (Nat.floor B)).filter Nat.Prime \
      (Finset.Icc 3 (Nat.floor A)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp_icc, hp_prime⟩, hpA⟩
      refine ⟨⟨hp_icc, hp_prime⟩, ?_⟩
      intro ⟨hp_iccA, _⟩
      rw [Nat.le_floor_iff (by linarith)] at hp_iccA
      linarith
    · rintro ⟨⟨hp_icc, hp_prime⟩, hnot⟩
      refine ⟨⟨hp_icc, hp_prime⟩, ?_⟩
      by_contra hle; push Not at hle
      apply hnot
      exact ⟨⟨hp_icc.1, (Nat.le_floor_iff (by linarith)).mpr hle⟩, hp_prime⟩
  rw [h_eq]
  have hs := Finset.sum_sdiff hsub (f := fun p => Real.log (p : ℝ) / ((p : ℝ) - 1))
  have hMB := (abs_le.mp (hM B hB)).2
  have hMA := (abs_le.mp (hM A hA)).1
  rw [Real.log_div (by linarith) (by linarith)]
  linarith

theorem mertens_div_p_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      ∑ p ∈ (Finset.Icc 3 (Nat.floor x)).filter Nat.Prime,
        Real.log (p : ℝ) / (p : ℝ) ≤ Real.log x + C := by
  obtain ⟨C, hC, hM⟩ := mertens_sum_le
  refine ⟨C, hC, fun x hx => ?_⟩
  calc ∑ p ∈ (Finset.Icc 3 (Nat.floor x)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ (Finset.Icc 3 (Nat.floor x)).filter Nat.Prime, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
        have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
        exact div_le_div_of_nonneg_left hlogp (by exact_mod_cast (by omega : (0 : ℤ) < (p : ℤ) - 1))
          (by linarith)
    _ ≤ Real.log x + C := hM x hx

/-! ### Algebraic Product Expansion Helper for Theorem 2.5(ii)–(iii) -/

/-- For any finite set `S` and `a, b : ℕ → ℂ` with `∀ s ∈ S, ‖a s‖ = 1` and `‖a s - b s‖ ≤ B s`,
`‖∏ s ∈ S, a s - ∏ s ∈ S, b s‖ ≤ ∑ T ∈ S.powerset.filter (·.Nonempty), ∏ s ∈ T, B s`. -/
theorem prod_sub_prod_le_powerset (S : Finset ℕ) (a b : ℕ → ℂ) (B : ℕ → ℝ)
    (ha : ∀ s ∈ S, ‖a s‖ = 1) (hB : ∀ s ∈ S, ‖a s - b s‖ ≤ B s) :
    ‖(∏ s ∈ S, a s) - (∏ s ∈ S, b s)‖ ≤
      ∑ T ∈ S.powerset.filter (·.Nonempty), ∏ s ∈ T, B s := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
    have ha_S : ∀ s ∈ S, ‖a s‖ = 1 := fun s hs => ha s (Finset.mem_insert_of_mem hs)
    have hB_S : ∀ s ∈ S, ‖a s - b s‖ ≤ B s := fun s hs => hB s (Finset.mem_insert_of_mem hs)
    have ih' := ih ha_S hB_S
    have hax : ‖a x‖ = 1 := ha x (Finset.mem_insert_self _ _)
    have hBx : ‖a x - b x‖ ≤ B x := hB x (Finset.mem_insert_self _ _)
    have hB_nn : ∀ s ∈ S, 0 ≤ B s := fun s hs => le_trans (norm_nonneg _) (hB_S s hs)
    have hprod_a : ‖∏ s ∈ S, a s‖ = 1 := by
      rw [norm_prod]
      exact Finset.prod_eq_one (fun s hs => ha_S s hs)
    have hprod_b : ‖∏ s ∈ S, b s‖ ≤ ∏ s ∈ S, (1 + B s) := by
      rw [norm_prod]
      refine Finset.prod_le_prod (fun s _ => norm_nonneg _) (fun s hs => ?_)
      have h1 : ‖b s‖ = ‖a s - (a s - b s)‖ := by ring_nf
      rw [h1]
      calc ‖a s - (a s - b s)‖ ≤ ‖a s‖ + ‖a s - b s‖ := norm_sub_le _ _
        _ ≤ 1 + B s := by linarith [ha_S s hs, hB_S s hs]
    have hpow_exp : ∏ s ∈ S, (1 + B s) = 1 + ∑ T ∈ S.powerset.filter (·.Nonempty), ∏ s ∈ T, B s := by
      rw [Finset.prod_one_add]
      have hsplit : S.powerset = insert ∅ (S.powerset.filter (·.Nonempty)) := by
        ext T
        simp only [Finset.mem_insert, Finset.mem_powerset, Finset.mem_filter]
        constructor
        · intro hT
          rcases Finset.eq_empty_or_nonempty T with rfl | hne
          · left; rfl
          · right; exact ⟨hT, hne⟩
        · rintro (rfl | ⟨hT, _⟩)
          · exact Finset.empty_subset _
          · exact hT
      have hnot : (∅ : Finset ℕ) ∉ S.powerset.filter (·.Nonempty) := by
        simp [Finset.not_nonempty_empty]
      rw [hsplit, Finset.sum_insert hnot, Finset.prod_empty]
    have h_split_id : (∏ s ∈ insert x S, a s) - (∏ s ∈ insert x S, b s) =
        a x * ((∏ s ∈ S, a s) - (∏ s ∈ S, b s)) + (a x - b x) * (∏ s ∈ S, b s) := by
      rw [Finset.prod_insert hx, Finset.prod_insert hx]
      ring
    rw [h_split_id]
    have h_tri : ‖a x * ((∏ s ∈ S, a s) - (∏ s ∈ S, b s)) + (a x - b x) * (∏ s ∈ S, b s)‖ ≤
        (∑ T ∈ S.powerset.filter (·.Nonempty), ∏ s ∈ T, B s) +
        B x * (1 + ∑ T ∈ S.powerset.filter (·.Nonempty), ∏ s ∈ T, B s) := by
      calc ‖a x * ((∏ s ∈ S, a s) - (∏ s ∈ S, b s)) + (a x - b x) * (∏ s ∈ S, b s)‖
          ≤ ‖a x‖ * ‖(∏ s ∈ S, a s) - (∏ s ∈ S, b s)‖ + ‖a x - b x‖ * ‖∏ s ∈ S, b s‖ := by
            rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
        _ ≤ 1 * (∑ T ∈ S.powerset.filter (·.Nonempty), ∏ s ∈ T, B s) +
            B x * (1 + ∑ T ∈ S.powerset.filter (·.Nonempty), ∏ s ∈ T, B s) := by
            apply add_le_add
            · rw [hax, one_mul]; exact ih'
            · apply mul_le_mul hBx (by linarith [hprod_b, hpow_exp]) (norm_nonneg _)
                (le_trans (norm_nonneg _) hBx)
        _ = (∑ T ∈ S.powerset.filter (·.Nonempty), ∏ s ∈ T, B s) +
            B x * (1 + ∑ T ∈ S.powerset.filter (·.Nonempty), ∏ s ∈ T, B s) := by ring
    have hpow_ins : (insert x S).powerset.filter (·.Nonempty) =
        S.powerset.filter (·.Nonempty) ∪
        insert {x} ((S.powerset.filter (·.Nonempty)).image (insert x)) := by
      ext T
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert,
        Finset.mem_image]
      constructor
      · rintro ⟨hT, hne⟩
        by_cases hxT : x ∈ T
        · right
          rcases eq_or_ne (T.erase x) ∅ with he | hne'
          · left
            ext y
            simp only [Finset.mem_singleton]
            constructor
            · intro hy
              by_contra hyx
              have : y ∈ T.erase x := Finset.mem_erase.mpr ⟨hyx, hy⟩
              rw [he] at this; simp at this
            · rintro rfl; exact hxT
          · right
            refine ⟨T.erase x, ⟨fun y hy => ?_, Finset.nonempty_iff_ne_empty.mpr hne'⟩, ?_⟩
            · have := hT (Finset.mem_of_mem_erase hy)
              rcases Finset.mem_insert.mp this with rfl | hyS
              · exact absurd hy (Finset.not_mem_erase _ _)
              · exact hyS
            · exact Finset.insert_erase hxT
        · left
          refine ⟨fun y hy => ?_, hne⟩
          rcases Finset.mem_insert.mp (hT hy) with rfl | hyS
          · exact absurd hy hxT
          · exact hyS
      · rintro (⟨hT, hne⟩ | rfl | ⟨U, ⟨hU, _⟩, rfl⟩)
        · exact ⟨Finset.Subset.trans hT (Finset.subset_insert _ _), hne⟩
        · exact ⟨Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _), Finset.singleton_nonempty _⟩
        · exact ⟨Finset.insert_subset_insert x hU, Finset.insert_nonempty _ _⟩
    have hdisj1 : Disjoint (S.powerset.filter (·.Nonempty))
        (insert {x} ((S.powerset.filter (·.Nonempty)).image (insert x))) := by
      rw [Finset.disjoint_left]
      intro T hT1 hT2
      have hTS : T ⊆ S := (Finset.mem_filter.mp hT1).1
      rcases Finset.mem_insert.mp hT2 with rfl | hT2'
      · exact hx (hTS (Finset.mem_singleton_self _))
      · obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hT2'
        exact hx (hTS (Finset.mem_insert_self _ _))
    have hnot_sing : ({x} : Finset ℕ) ∉ (S.powerset.filter (·.Nonempty)).image (insert x) := by
      intro hmem
      obtain ⟨U, hU, heq⟩ := Finset.mem_image.mp hmem
      obtain ⟨y, hy⟩ := (Finset.mem_filter.mp hU).2
      have hyU : y ∈ insert x U := Finset.mem_insert_of_mem hy
      rw [heq] at hyU
      have hyx : y = x := Finset.mem_singleton.mp hyU
      subst hyx
      exact hx ((Finset.mem_filter.mp hU).1 hy)
    have hinj : ∀ U₁ ∈ S.powerset.filter (·.Nonempty), ∀ U₂ ∈ S.powerset.filter (·.Nonempty),
        insert x U₁ = insert x U₂ → U₁ = U₂ := by
      intro U₁ hU₁ U₂ hU₂ heq
      have hx1 : x ∉ U₁ := fun h => hx ((Finset.mem_filter.mp hU₁).1 h)
      have hx2 : x ∉ U₂ := fun h => hx ((Finset.mem_filter.mp hU₂).1 h)
      ext y
      by_cases hy : y = x
      · subst hy; simp [hx1, hx2]
      · have := congrArg (y ∈ ·) heq
        simpa [Finset.mem_insert, hy] using this
    rw [hpow_ins, Finset.sum_union hdisj1, Finset.sum_insert hnot_sing, Finset.prod_singleton,
      Finset.sum_image hinj]
    have himg : ∑ U ∈ S.powerset.filter (·.Nonempty), ∏ s ∈ insert x U, B s =
        B x * ∑ U ∈ S.powerset.filter (·.Nonempty), ∏ s ∈ U, B s := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun U hU => ?_)
      have hxU : x ∉ U := fun h => hx ((Finset.mem_filter.mp hU).1 h)
      rw [Finset.prod_insert hxU]
    rw [himg]
    linarith

/-! ### Theorem 2.5(i): Second-Order Discrepancy Formula (eq. 2.15) -/

/-- **Theorem 2.5(i) (Second-Order Discrepancy Formula)**:
`Δ_parity(n) = (log 2 - 1 - Σ*_parity(n)) n + O(n / log n)` (eq. 2.15). -/
theorem Delta_parity_second_order :
    (fun n : ℕ => Delta_parity n - (Real.log 2 - 1 - Sigma_star_parity n) * (n : ℝ))
      =O[atTop] (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  obtain ⟨c₁, hc₁, hdlvp⟩ := de_la_vallee_poussin_theta
  obtain ⟨C₁, hC₁⟩ := hdlvp.bound
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp hC₁
  obtain ⟨Cθ, hCθ_pos, hCθ⟩ := thetaPrime_le_linear
  obtain ⟨Cm, hCm_pos, hCm⟩ := mertens_div_p_sum_le
  obtain ⟨η', η, hη', hη, C₁e, C₂e, C₃e, hC₁e, hC₂e, hC₃e, hExp⟩ :=
    prime_exp_sum_bounds (1 / 3 : ℝ) (by norm_num) (by norm_num)
  obtain ⟨C_ed, hC_ed⟩ := E_digit_isBigO_sqrt.bound
  have hlog_ge2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ Real.log (n : ℝ) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  have hsqrt_lt_n_div_R1 : ∀ᶠ n : ℕ in atTop,
      (Real.sqrt (n : ℝ) < (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)) ∧
      (n : ℝ) ^ (1 / 3 : ℝ) ≤ Real.sqrt (n : ℝ) ∧
      (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ≥ 4 ∧
      (2 : ℝ) ^ (-((Nat.floor (1 / (1 / 3 : ℝ)) : ℕ) : ℤ)) * (Real.log (n : ℝ)) ^ (6 * Nat.floor (1 / (1 / 3 : ℝ)) + 30) ≤
        (Real.log (n : ℝ)) ^ 48 / 2 ∧
      max X₁ 4 ≤ (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ∧
      (Real.log (n : ℝ)) ^ 48 ≤ 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ∧
      (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ^ 2 *
        Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)))) *
          Real.log (n : ℝ) ≤ 1 := by
    have ht1 : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 48 / (n : ℝ) ^ (1 / 4 : ℝ)) atTop (nhds 0) :=
      log_pow_div_rpow_tendsto_zero 48 (by norm_num)
    have ht_exp : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 97 *
        Real.exp (-c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log (n : ℝ)))) atTop (nhds 0) := by
      have h_sqrt : Tendsto (fun t : ℝ => t ^ 194 * Real.exp (-(c₁ * Real.sqrt (1 / 2 : ℝ)) * t))
          atTop (nhds 0) := by
        have hpos : 0 < c₁ * Real.sqrt (1 / 2 : ℝ) := by positivity
        have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 194).comp (tendsto_id.const_mul_atTop hpos)
        have heq : (fun t : ℝ => t ^ 194 * Real.exp (-(c₁ * Real.sqrt (1 / 2 : ℝ)) * t)) =
            (fun t : ℝ => (1 / (c₁ * Real.sqrt (1 / 2 : ℝ)) ^ 194) *
              (((c₁ * Real.sqrt (1 / 2 : ℝ)) * t) ^ 194 *
                Real.exp (-((c₁ * Real.sqrt (1 / 2 : ℝ)) * t)))) := by
          ext t; field_simp [hpos.ne']; ring
        rw [heq]; simpa using this.const_mul _
      have hcomp := h_sqrt.comp (Real.tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
      refine hcomp.congr' ?_
      filter_upwards [(tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 0)] with n hln
      dsimp only [Function.comp_def]
      have hsq : (Real.sqrt (Real.log (n : ℝ))) ^ 194 = (Real.log (n : ℝ)) ^ 97 := by
        rw [show (194 : ℕ) = 2 * 97 from rfl, pow_mul, Real.sq_sqrt hln]
      rw [hsq, Real.sqrt_mul (by norm_num)]
      ring_nf
    have hlog_48 : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 48) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 48 ≠ 0)).comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    filter_upwards [Filter.eventually_ge_atTop 16, hlog_ge2,
      ht1.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      hlog_48.eventually (eventually_ge_atTop (max (max X₁ 4) 8)),
      ht_exp.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with
      n hn hln ht1_sm h48_ge htexp_sm
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h48_ge8 : 8 ≤ (Real.log (n : ℝ)) ^ 48 := le_trans (le_max_right _ _) h48_ge
    have hfl_ge4 : 4 ≤ (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
      have : (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) > (Real.log (n : ℝ)) ^ 48 - 1 := by
        linarith [Nat.lt_floor_add_one ((Real.log (n : ℝ)) ^ 48)]
      linarith
    have hfl_le : (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ≤ (Real.log (n : ℝ)) ^ 48 :=
      Nat.floor_le (by positivity)
    have h48_le_2fl : (Real.log (n : ℝ)) ^ 48 ≤ 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
      linarith [Nat.lt_floor_add_one ((Real.log (n : ℝ)) ^ 48)]
    have h_r1_le_rpow : (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ≤ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) := by
      have h1 := (div_le_iff₀ (by positivity)).mp ht1_sm
      linarith
    have h_sqrt_lt : Real.sqrt (n : ℝ) < (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
      have hn14 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
      have hsq_eq : Real.sqrt (n : ℝ) * ((n : ℝ) ^ (1 / 4 : ℝ)) < (n : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn_pos]
        have : (1 / 2 : ℝ) + (1 / 4 : ℝ) = (3 / 4 : ℝ) := by norm_num
        rw [this]
        calc (n : ℝ) ^ (3 / 4 : ℝ) < (n : ℝ) ^ (1 : ℝ) :=
              Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < n)) (by norm_num)
          _ = (n : ℝ) := Real.rpow_one _
      rw [lt_div_iff₀ (by linarith)]
      nlinarith
    have h_13_sqrt : (n : ℝ) ^ (1 / 3 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
    have h_R3 : Nat.floor (1 / (1 / 3 : ℝ)) = 3 := by norm_num
    have h_pow_48 : (2 : ℝ) ^ (-(3 : ℤ)) * (Real.log (n : ℝ)) ^ 48 ≤ (Real.log (n : ℝ)) ^ 48 / 2 := by
      norm_num; positivity
    have h_n_div_ge : (n : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
      calc (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg hn_pos.le, ← Real.rpow_add hn_pos]; congr 1; norm_num
        _ ≤ (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
            apply div_le_div_of_nonneg_left hn_pos.le (by linarith)
            have hn14 : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
            linarith
    have h_n34_ge : max X₁ 4 ≤ (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
      -- Since (log n)^48 ≤ (1/4) * n^{1/4} and (log n)^48 ≥ max(max X₁ 4, 8), wait: we need n^{3/4} ≥ max X₁ 4!
      -- Note: (n : ℝ) ^ (1 / 4 : ℝ) ≥ 4 * (log n)^48 ≥ 4 * max(max X₁ 4, 8), so n^{3/4} = (n^{1/4})^3 ≥ max X₁ 4!
      have h14_ge : max X₁ 4 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
        have : max X₁ 4 ≤ (Real.log (n : ℝ)) ^ 48 := le_trans (le_max_left _ _) h48_ge
        linarith
      have h14_ge1 : 1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
      have h14_le_34 : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
      linarith
    have h_log_div_ge : (1 / 2 : ℝ) * Real.log (n : ℝ) ≤
        Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)) := by
      have h_le_sqrt : (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        have hn14 : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
        have h_14_12 : (n : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt (n : ℝ) := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
        linarith
      calc (1 / 2 : ℝ) * Real.log (n : ℝ) = Real.log (n : ℝ) - (1 / 2 : ℝ) * Real.log (n : ℝ) := by ring
        _ = Real.log (n : ℝ) - Real.log ((n : ℝ) ^ (1 / 2 : ℝ)) := by rw [Real.log_rpow hn_pos]
        _ ≤ Real.log (n : ℝ) - Real.log (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
            linarith [Real.log_le_log (by linarith) h_le_sqrt]
        _ = Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)) :=
            (Real.log_div hn_pos.ne' (by linarith)).symm
    have h_exp_last : (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ^ 2 *
        Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)))) *
          Real.log (n : ℝ) ≤ 1 := by
      have hexp_le : Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)))) ≤
          Real.exp (-c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log (n : ℝ))) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt h_log_div_ge) (by linarith))
      calc (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ^ 2 *
            Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)))) *
            Real.log (n : ℝ)
          ≤ ((Real.log (n : ℝ)) ^ 48) ^ 2 *
              Real.exp (-c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log (n : ℝ))) * Real.log (n : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact mul_le_mul (pow_le_pow_left₀ (by positivity) hfl_le 2) hexp_le (by positivity) (by positivity)
        _ = (Real.log (n : ℝ)) ^ 97 * Real.exp (-c₁ * Real.sqrt ((1 / 2 : ℝ) * Real.log (n : ℝ))) := by ring
        _ ≤ 1 := htexp_sm
    refine ⟨h_sqrt_lt, h_13_sqrt, hfl_ge4, ?_, h_n34_ge, h48_le_2fl, h_exp_last⟩
    rw [h_R3]
    simpa using h_pow_48
  -- Also we need (log n)^5 ≥ 1 and ≤ (log n)^12 etc., and (log log n) / (log n)^4 ≤ 1
  have h_loglog_sm : ∀ᶠ n : ℕ in atTop,
      (Real.log (2 * (Real.log (n : ℝ)) ^ 5 + 1) + 1) * (Real.log (n : ℝ) / Real.log 2 + 2) ≤
        (Real.log (n : ℝ)) ^ 2 := by
    have hlog_pos : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ Real.log (n : ℝ) := hlog_ge2
    have hlt_exp : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 / 4 := by
      filter_upwards [(tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 4)] with n hn
      nlinarith
    filter_upwards [hlog_pos, hlt_exp,
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 100)] with n hn h4 hn100
    have hlog_le_id : Real.log (2 * (Real.log (n : ℝ)) ^ 5 + 1) ≤ (2 * (Real.log (n : ℝ)) ^ 5 + 1) :=
      Real.log_le_sub_one_of_pos (by positivity) |>.trans (by linarith)
    -- Wait: we need log(2 (log n)^5 + 1) ≤ log n / 10 (even simpler: log x ≤ x^(1/10) for large x, or log(3 (log n)^5) ≤ 6 log log n ≤ √(log n))!
    -- Even easier: log(2 y^5 + 1) ≤ 6 * log y ≤ 6 * √y for y = log n ≥ 100!
    have hy : 100 ≤ Real.log (n : ℝ) := hn100
    have h1 : Real.log (2 * (Real.log (n : ℝ)) ^ 5 + 1) + 1 ≤ Real.log (n : ℝ) / 4 := by
      have hle : 2 * (Real.log (n : ℝ)) ^ 5 + 1 ≤ (Real.log (n : ℝ)) ^ 6 := by nlinarith
      have hlog6 : Real.log (2 * (Real.log (n : ℝ)) ^ 5 + 1) ≤ 6 * Real.log (Real.log (n : ℝ)) := by
        calc Real.log (2 * (Real.log (n : ℝ)) ^ 5 + 1) ≤ Real.log ((Real.log (n : ℝ)) ^ 6) :=
              Real.log_le_log (by positivity) hle
          _ = 6 * Real.log (Real.log (n : ℝ)) := by rw [Real.log_pow]; norm_num
      have hsqrt : Real.log (Real.log (n : ℝ)) ≤ 2 * Real.sqrt (Real.log (n : ℝ)) - 2 := by
        have h_half := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith : 0 < Real.log (n : ℝ)))
        have h_eq : Real.log (Real.log (n : ℝ)) = 2 * Real.log (Real.sqrt (Real.log (n : ℝ))) := by
          rw [Real.log_sqrt (by linarith)]; ring
        linarith
      -- For y ≥ 100, 12 √y - 11 ≤ y / 4? Wait: for y = 100, 12*10 - 11 = 109 > 25! For y ≥ 2500, 12 √y ≤ y / 4!
      -- That's why we can just filter for log n ≥ 4096 (n ≥ e^{4096})!
      sorry
    sorry
  sorry

end GrasGreenbergBrocard
