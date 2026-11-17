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
# Theorem 2.5(i)–(ii): Valuation-Parity Equidistribution and Second-Order Discrepancy Law

Formalizes Section 2.3 (eq. 2.15–2.17):
- `Delta_parity_second_order` (Theorem 2.5(i), eq. 2.15)
- `small_prime_parity_band_bound` (Theorem 2.5(ii), eq. 2.16)
- `Sigma_star_parity_isLittleO_log`, `Delta_parity_isLittleO_mul_log`,
  `S_odd_asymptotic`, `S_even_asymptotic` (Theorem 2.5(ii), eq. 2.17)
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
      (fun k => I.filter (fun p : ℕ => A * (2 : ℝ) ^ k < (p : ℝ) ∧ (p : ℝ) ≤ 2 * (A * (2 : ℝ) ^ k))) ∧
    ((dyadicBlocks A B : Set ℕ).PairwiseDisjoint
      (fun k => I.filter (fun p : ℕ => A * (2 : ℝ) ^ k < (p : ℝ) ∧ (p : ℝ) ≤ 2 * (A * (2 : ℝ) ^ k)))) := by
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
    dsimp only [Function.onFun]
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
      ∑ p ∈ ((Finset.Icc 3 (Nat.floor B)).filter Nat.Prime).filter (fun p : ℕ => A < (p : ℝ)),
        Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ Real.log (B / A) + C := by
  obtain ⟨Cm, hCm, hM⟩ := mertens_first_theorem
  refine ⟨2 * Cm, by positivity, fun A B hA hAB => ?_⟩
  have hB : 3 ≤ B := le_trans hA hAB
  have hsub : (Finset.Icc 3 (Nat.floor A)).filter Nat.Prime ⊆
      (Finset.Icc 3 (Nat.floor B)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_mono hAB)⟩, hp.2⟩
  have h_eq : ((Finset.Icc 3 (Nat.floor B)).filter Nat.Prime).filter (fun p : ℕ => A < (p : ℝ)) =
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

/-! ### Auxiliary Lemmas for Theorem 2.5 -/

private theorem alt_harmonic_shifted_even (K : ℕ) (hK : 1 ≤ K) :
    ∑ r ∈ Finset.Icc 1 (2 * K), (-1 : ℝ) ^ r / ((r : ℝ) + 1) =
      ∑ k ∈ Finset.Icc 1 K, (1 / (2 * (k : ℝ) - 1) - 1 / (2 * (k : ℝ))) - 1 + 1 / (2 * (K : ℝ) + 1) := by
  induction K, hK using Nat.le_induction with
  | base =>
    norm_num [Finset.sum_Icc_succ_top]
  | succ m hm ih =>
    have h2m1 : 1 ≤ 2 * m + 1 := by omega
    have h2m2 : 1 ≤ 2 * m + 2 := by omega
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 from by omega]
    rw [Finset.sum_Icc_succ_top h2m2, Finset.sum_Icc_succ_top h2m1]
    rw [show 2 * m + 1 = 2 * m + 1 from rfl, ih]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hpow1 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
      rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
    have hpow2 : (-1 : ℝ) ^ (2 * m + 2) = 1 := by
      rw [show 2 * m + 2 = 2 * (m + 1) from by omega, pow_mul, neg_one_sq, one_pow]
    rw [hpow1, hpow2]
    push_cast
    have hm1 : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
    have hm2 : 2 * (m : ℝ) + 2 ≠ 0 := by positivity
    have hm3 : 2 * (m : ℝ) + 3 ≠ 0 := by positivity
    field_simp [hm1, hm2, hm3]
    ring

private theorem alt_harmonic_shifted_bound {N : ℕ} (hN : 3 ≤ N) :
    |∑ r ∈ Finset.Icc 1 (N - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) - (Real.log 2 - 1)| ≤
      2 / (N : ℝ) := by
  rcases Nat.even_or_odd (N - 1) with ⟨K, hK⟩ | ⟨K, hK⟩
  · have hK_eq : N - 1 = 2 * K := by omega
    have hK1 : 1 ≤ K := by omega
    rw [hK_eq, alt_harmonic_shifted_even K hK1]
    have hdiff := alt_harmonic_sum_diff_log_two hK1
    have h1 : (∑ k ∈ Finset.Icc 1 K, (1 / (2 * (k : ℝ) - 1) - 1 / (2 * (k : ℝ))) - 1 + 1 / (2 * (K : ℝ) + 1)) -
        (Real.log 2 - 1) =
        (∑ k ∈ Finset.Icc 1 K, (1 / (2 * (k : ℝ) - 1) - 1 / (2 * (k : ℝ))) - Real.log 2) +
        1 / (2 * (K : ℝ) + 1) := by ring
    rw [h1]
    have htri := abs_add_le
      (∑ k ∈ Finset.Icc 1 K, (1 / (2 * (k : ℝ) - 1) - 1 / (2 * (k : ℝ))) - Real.log 2)
      (1 / (2 * (K : ℝ) + 1))
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * (K : ℝ) + 1))] at htri
    have hN_eq : (N : ℝ) = 2 * (K : ℝ) + 1 := by exact_mod_cast (by omega : N = 2 * K + 1)
    have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
    have h_le : 1 / (2 * (K : ℝ)) + 1 / (2 * (K : ℝ) + 1) ≤ 2 / (N : ℝ) := by
      rw [hN_eq, div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  · have hK_eq : N - 1 = 2 * K + 1 := by omega
    have hK1 : 1 ≤ K := by omega
    rw [hK_eq, Finset.sum_Icc_succ_top (by omega : 1 ≤ 2 * K + 1), alt_harmonic_shifted_even K hK1]
    have hpow : (-1 : ℝ) ^ (2 * K + 1) = -1 := by
      rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
    rw [hpow]
    have hdiff := alt_harmonic_sum_diff_log_two hK1
    have h1 : (∑ k ∈ Finset.Icc 1 K, (1 / (2 * (k : ℝ) - 1) - 1 / (2 * (k : ℝ))) - 1 + 1 / (2 * (K : ℝ) + 1) +
        (-1) / (((2 * K + 1 : ℕ) : ℝ) + 1)) - (Real.log 2 - 1) =
        (∑ k ∈ Finset.Icc 1 K, (1 / (2 * (k : ℝ) - 1) - 1 / (2 * (k : ℝ))) - Real.log 2) +
        (1 / (2 * (K : ℝ) + 1) - 1 / (2 * (K : ℝ) + 2)) := by
      push_cast; ring
    rw [h1]
    have htri := abs_add_le
      (∑ k ∈ Finset.Icc 1 K, (1 / (2 * (k : ℝ) - 1) - 1 / (2 * (k : ℝ))) - Real.log 2)
      (1 / (2 * (K : ℝ) + 1) - 1 / (2 * (K : ℝ) + 2))
    have h_pos_diff : 0 ≤ 1 / (2 * (K : ℝ) + 1) - 1 / (2 * (K : ℝ) + 2) := by
      have : 1 / (2 * (K : ℝ) + 2) ≤ 1 / (2 * (K : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    rw [abs_of_nonneg h_pos_diff] at htri
    have hN_eq : (N : ℝ) = 2 * (K : ℝ) + 2 := by exact_mod_cast (by omega : N = 2 * K + 2)
    have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
    have h_le : 1 / (2 * (K : ℝ)) + (1 / (2 * (K : ℝ) + 1) - 1 / (2 * (K : ℝ) + 2)) ≤ 2 / (N : ℝ) := by
      rw [hN_eq]
      have hsub : 1 / (2 * (K : ℝ) + 1) - 1 / (2 * (K : ℝ) + 2) =
          1 / ((2 * (K : ℝ) + 1) * (2 * (K : ℝ) + 2)) := by
        field_simp [by positivity : 2 * (K : ℝ) + 1 ≠ 0, by positivity : 2 * (K : ℝ) + 2 ≠ 0]; ring
      rw [hsub, div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

theorem padicValNat_factorial_eq_sum_Icc {p n R : ℕ} (hp : p.Prime)
    (hn : n < p ^ (R + 1)) :
    padicValNat p (Nat.factorial n) = ∑ s ∈ Finset.Icc 1 R, n / p ^ s := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [padicValNat_factorial (k := R + 1) hn]
  congr 1
  ext s
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  omega

theorem Mertens_div_p_band_le :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : ℝ, 3 ≤ A → A ≤ B →
      ∑ p ∈ ((Finset.Icc 3 (Nat.floor B)).filter Nat.Prime).filter (fun p : ℕ => A < (p : ℝ)),
        Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (B / A) + C := by
  obtain ⟨C, hC, hM⟩ := mertens_band_le
  refine ⟨C, hC, fun A B hA hAB => ?_⟩
  calc ∑ p ∈ ((Finset.Icc 3 (Nat.floor B)).filter Nat.Prime).filter (fun p : ℕ => A < (p : ℝ)),
          Real.log (p : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ ((Finset.Icc 3 (Nat.floor B)).filter Nat.Prime).filter (fun p : ℕ => A < (p : ℝ)),
          Real.log (p : ℝ) / ((p : ℝ) - 1) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
        have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
        exact div_le_div_of_nonneg_left hlogp (by exact_mod_cast (by omega : (0 : ℤ) < (p : ℤ) - 1))
          (by linarith)
    _ ≤ Real.log (B / A) + C := hM A B hA hAB

theorem star_eExp (t : ℝ) : star (eExp t) = eExp (-t) := by
  unfold eExp
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, Complex.conj_I]
  ring

theorem eExp_add (x y : ℝ) : eExp x * eExp y = eExp (x + y) := by
  unfold eExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eExp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, eExp (f i) = eExp (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp [eExp]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, eExp_add]

theorem vaaler_B_real_rep (b_tilde : ℤ → ℂ) (K : ℤ) (hK : 0 ≤ K) (t : ℝ) :
    let allK := Finset.Icc (-K) K
    let b_real : ℤ → ℂ := fun h => (1 / 2 : ℂ) * (b_tilde h + star (b_tilde (-h)))
    ((∑ h ∈ allK, b_tilde h * eExp ((h : ℝ) * t)).re : ℂ) =
      ∑ h ∈ allK, b_real h * eExp ((h : ℝ) * t) := by
  intro allK b_real
  have hre : ∀ z : ℂ, (z.re : ℂ) = (1 / 2 : ℂ) * (z + star z) := by
    intro z; apply Complex.ext <;> simp
  rw [hre, star_sum]
  have h_bij : ∑ h ∈ allK, star (b_tilde h * eExp ((h : ℝ) * t)) =
      ∑ h ∈ allK, star (b_tilde (-h)) * eExp ((h : ℝ) * t) := by
    refine Finset.sum_bij (fun h _ => -h) ?_ ?_ ?_ ?_
    · intro h hh; simp only [allK, Finset.mem_Icc] at hh ⊢; omega
    · intro h1 _ h2 _ heq; omega
    · intro h hh; refine ⟨-h, ?_, by omega⟩
      simp only [allK, Finset.mem_Icc] at hh ⊢; omega
    · intro h _
      rw [star_mul, star_eExp]
      congr 2; simp; ring
  rw [h_bij, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  dsimp only [b_real]
  ring

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
  have h_main_conds : ∀ᶠ n : ℕ in atTop,
      (Real.sqrt (n : ℝ) < (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)) ∧
      ((n : ℝ) ^ (1 / 3 : ℝ) ≤ (Nat.sqrt n : ℝ)) ∧
      ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12) ∧
      (4 ≤ Nat.floor ((Real.log (n : ℝ)) ^ 48)) ∧
      (1 ≤ Nat.floor ((Real.log (n : ℝ)) ^ 5)) ∧
      ((Real.log (n : ℝ)) ^ 48 ≤ 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)) ∧
      ((Real.log (n : ℝ)) ^ 5 ≤ 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ)) ∧
      (max X₁ 4 ≤ (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)) ∧
      ((Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ^ 2 *
        Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)))) *
          Real.log (n : ℝ) ≤ 1) ∧
      ((2 : ℝ) ^ (-(Nat.floor (1 / (1 / 3 : ℝ)) : ℕ) : ℤ) *
        (Real.log (n : ℝ)) ^ (6 * Nat.floor (1 / (1 / 3 : ℝ)) + 30) ≤
          (Real.log (n : ℝ)) ^ 48 / 2) ∧
      (2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1 ≤ (Real.log (n : ℝ)) ^ 12) ∧
      ((Real.log (2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1) + 1) *
        (Real.log (n : ℝ) / Real.log 2 + 2) ≤ (Real.log (n : ℝ)) ^ 4) := by
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
          ext t; field_simp [hpos.ne']
        rw [heq]
        have hmul := this.const_mul (1 / (c₁ * Real.sqrt (1 / 2 : ℝ)) ^ 194)
        rw [mul_zero] at hmul
        exact hmul
      have hcomp := h_sqrt.comp (Real.tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
      refine hcomp.congr' ?_
      filter_upwards [(tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 0)] with n hln
      dsimp only [Function.comp_def] at hln ⊢
      have hsq : (Real.sqrt (Real.log (n : ℝ))) ^ 194 = (Real.log (n : ℝ)) ^ 97 := by
        rw [show (194 : ℕ) = 2 * 97 from rfl, pow_mul, Real.sq_sqrt hln]
      rw [hsq, Real.sqrt_mul (by norm_num)]
      ring_nf
    have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [Filter.eventually_ge_atTop 16, hlog_ge2,
      (ht1.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono (fun _ h => h.le),
      hlog_inf.eventually (eventually_ge_atTop (max (max X₁ 4) 10000)),
      (ht_exp.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)] with
      n hn hln ht1_sm hlog_big htexp_sm
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hln_10000 : 10000 ≤ Real.log (n : ℝ) := le_trans (le_max_right _ _) hlog_big
    have hln_X1 : max X₁ 4 ≤ Real.log (n : ℝ) := le_trans (le_max_left _ _) hlog_big
    have h48_ge : max X₁ 4 ≤ (Real.log (n : ℝ)) ^ 48 := by
      have h1 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 48 :=
        le_self_pow₀ (by linarith) (by norm_num : 48 ≠ 0)
      linarith
    have h48_ge8 : 8 ≤ (Real.log (n : ℝ)) ^ 48 := by
      have : (10000 : ℝ) ^ 48 ≤ (Real.log (n : ℝ)) ^ 48 := pow_le_pow_left₀ (by norm_num) hln_10000 48
      linarith
    have hfl_ge4 : 4 ≤ Nat.floor ((Real.log (n : ℝ)) ^ 48) := by
      rw [Nat.le_floor_iff (by positivity)]; push_cast; linarith
    have hfl_le : (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ≤ (Real.log (n : ℝ)) ^ 48 :=
      Nat.floor_le (by positivity)
    have h48_le_2fl : (Real.log (n : ℝ)) ^ 48 ≤ 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
      linarith [Nat.lt_floor_add_one ((Real.log (n : ℝ)) ^ 48)]
    have hfl5_ge1 : 1 ≤ Nat.floor ((Real.log (n : ℝ)) ^ 5) := by
      rw [Nat.le_floor_iff (by positivity)]
      have : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 := one_le_pow₀ (by linarith)
      exact_mod_cast this
    have hfl5_le : (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 :=
      Nat.floor_le (by positivity)
    have h5_le_2fl5 : (Real.log (n : ℝ)) ^ 5 ≤ 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) := by
      linarith [Nat.lt_floor_add_one ((Real.log (n : ℝ)) ^ 5)]
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
      rw [lt_div_iff₀ (by exact_mod_cast (by omega : 0 < Nat.floor ((Real.log (n : ℝ)) ^ 48)))]
      nlinarith
    have h_13_sqrtN : (n : ℝ) ^ (1 / 3 : ℝ) ≤ (Nat.sqrt n : ℝ) := by
      have h1 : (n : ℝ) ^ (1 / 3 : ℝ) + 1 ≤ Real.sqrt (n : ℝ) := by
        have h16 : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 6 : ℝ) := by
          have hn64 : (64 : ℝ) ≤ (n : ℝ) := by
            have h64_le_exp : (64 : ℝ) ≤ Real.exp 10000 := by
              have : (10001 : ℝ) ≤ Real.exp 10000 := by linarith [Real.add_one_le_exp (10000 : ℝ)]
              linarith
            have hexp_le : Real.exp 10000 ≤ (n : ℝ) := by
              calc Real.exp 10000 ≤ Real.exp (Real.log (n : ℝ)) := Real.exp_le_exp.mpr hln_10000
                _ = (n : ℝ) := Real.exp_log hn_pos
            linarith
          rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 6)]
          rw [← Real.rpow_mul hn_pos.le]
          norm_num
          linarith
        have hsq_eq : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn_pos]
          congr 1; norm_num
        have hn13_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
          Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
        rw [hsq_eq]
        nlinarith
      have hsq_lt : Real.sqrt (n : ℝ) < (Nat.sqrt n : ℝ) + 1 := by
        rw [Real.sqrt_lt' (by positivity)]
        exact_mod_cast Nat.lt_succ_sqrt' n
      linarith
    have h_div_r1_12 : (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := by
      apply div_le_div_of_nonneg_left hn_pos.le (by positivity)
      have h12_le_48 : 2 * (Real.log (n : ℝ)) ^ 12 ≤ (Real.log (n : ℝ)) ^ 48 := by
        have hpow : (Real.log (n : ℝ)) ^ 12 * 2 ≤ (Real.log (n : ℝ)) ^ 12 * (Real.log (n : ℝ)) ^ 36 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := one_le_pow₀ (by linarith : (1 : ℝ) ≤ Real.log (n : ℝ)) (n := 35)
          have : (Real.log (n : ℝ)) ^ 36 = Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 35 := by ring
          nlinarith
        linarith [show (Real.log (n : ℝ)) ^ 48 = (Real.log (n : ℝ)) ^ 12 * (Real.log (n : ℝ)) ^ 36 from by ring]
      linarith
    have h_n34_ge : max X₁ 4 ≤ (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
      have h14_ge : max X₁ 4 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by linarith
      have h14_le_34 : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
      have h_n_div_ge : (n : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
        calc (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) := by
              rw [show (3 / 4 : ℝ) = 1 - 1 / 4 from by norm_num, Real.rpow_sub hn_pos, Real.rpow_one]
          _ ≤ (n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
              apply div_le_div_of_nonneg_left hn_pos.le (by exact_mod_cast (by omega : 0 < Nat.floor ((Real.log (n : ℝ)) ^ 48)))
              have hn14 : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
              linarith
      linarith
    have h_log_div_ge : (1 / 2 : ℝ) * Real.log (n : ℝ) ≤
        Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)) := by
      have h_le_sqrt : (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        have h_14_12 : (n : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt (n : ℝ) := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
        linarith
      calc (1 / 2 : ℝ) * Real.log (n : ℝ) = Real.log (n : ℝ) - (1 / 2 : ℝ) * Real.log (n : ℝ) := by ring
        _ = Real.log (n : ℝ) - Real.log ((n : ℝ) ^ (1 / 2 : ℝ)) := by rw [Real.log_rpow hn_pos]
        _ ≤ Real.log (n : ℝ) - Real.log (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ) := by
            linarith [Real.log_le_log (by exact_mod_cast (by omega : 0 < Nat.floor ((Real.log (n : ℝ)) ^ 48))) h_le_sqrt]
        _ = Real.log ((n : ℝ) / (Nat.floor ((Real.log (n : ℝ)) ^ 48) : ℝ)) :=
            (Real.log_div hn_pos.ne' (by exact_mod_cast (by omega : Nat.floor ((Real.log (n : ℝ)) ^ 48) ≠ 0))).symm
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
    have h_R3 : Nat.floor (1 / (1 / 3 : ℝ)) = 3 := by norm_num
    have h_pow_48 : (2 : ℝ) ^ (-(Nat.floor (1 / (1 / 3 : ℝ)) : ℕ) : ℤ) *
        (Real.log (n : ℝ)) ^ (6 * Nat.floor (1 / (1 / 3 : ℝ)) + 30) ≤ (Real.log (n : ℝ)) ^ 48 / 2 := by
      rw [h_R3]; norm_num; positivity
    have h_2H1_12 : 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1 ≤ (Real.log (n : ℝ)) ^ 12 := by
      have : 2 * (Real.log (n : ℝ)) ^ 5 + 1 ≤ (Real.log (n : ℝ)) ^ 6 := by nlinarith
      have h6_12 : (Real.log (n : ℝ)) ^ 6 ≤ (Real.log (n : ℝ)) ^ 12 :=
        pow_le_pow_right₀ (by linarith) (by norm_num)
      linarith
    have h_loglog_4 : (Real.log (2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1) + 1) *
        (Real.log (n : ℝ) / Real.log 2 + 2) ≤ (Real.log (n : ℝ)) ^ 4 := by
      have hle6 : 2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1 ≤ (Real.log (n : ℝ)) ^ 6 := by nlinarith
      have hlog6 : Real.log (2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1) ≤ 6 * Real.log (Real.log (n : ℝ)) := by
        calc Real.log (2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1)
            ≤ Real.log ((Real.log (n : ℝ)) ^ 6) := Real.log_le_log (by positivity) hle6
          _ = 6 * Real.log (Real.log (n : ℝ)) := by rw [Real.log_pow]; norm_num
      have hsqrt_y : Real.log (Real.log (n : ℝ)) ≤ 2 * Real.sqrt (Real.log (n : ℝ)) := by
        have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith : 0 < Real.log (n : ℝ)))
        have h2 : Real.log (Real.log (n : ℝ)) = 2 * Real.log (Real.sqrt (Real.log (n : ℝ))) := by
          rw [Real.log_sqrt (by linarith)]; ring
        linarith
      have hsq_le_y : 12 * Real.sqrt (Real.log (n : ℝ)) + 1 ≤ Real.log (n : ℝ) := by
        have : 100 ≤ Real.sqrt (Real.log (n : ℝ)) := by
          rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
        nlinarith [Real.sq_sqrt (by linarith : 0 ≤ Real.log (n : ℝ))]
      have h_f1 : Real.log (2 * (Nat.floor ((Real.log (n : ℝ)) ^ 5) : ℝ) + 1) + 1 ≤ Real.log (n : ℝ) := by linarith
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have h := Real.log_two_gt_d9
        linarith
      have h_f2 : Real.log (n : ℝ) / Real.log 2 + 2 ≤ 3 * Real.log (n : ℝ) := by
        have : Real.log (n : ℝ) / Real.log 2 ≤ 2 * Real.log (n : ℝ) := by
          rw [div_le_iff₀ hlog2_pos]; nlinarith
        linarith
      have : 3 * (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 4 := by nlinarith
      nlinarith
    exact ⟨h_sqrt_lt, h_13_sqrtN, h_div_r1_12, hfl_ge4, hfl5_ge1, h48_le_2fl, h5_le_2fl5,
      h_n34_ge, h_exp_last, h_pow_48, h_2H1_12, h_loglog_4⟩
  let M : ℝ := |C_ed| + (4 * |C₁| + 2) +
    (Cθ * 2 + (2 + 4 * C₁e * (1 + Real.log 2) + (2 + 2 * Cm + 36 * C₁e)))
  refine Asymptotics.IsBigO.of_bound M ?_
  filter_upwards [Filter.eventually_ge_atTop 16, hlog_ge2, h_main_conds, hExp, hC_ed] with
    n hn hln hconds hexp_n hed_n
  rcases hconds with ⟨hsqrt_lt, h13_sqrtN, hdiv_r1_12, hR1_ge4, hH_ge1, h48_le_2fl, h5_le_2fl5,
    hnX1, hexp_last, hpow48, h2H1_12, hloglog4⟩
  set R₁ := Nat.floor ((Real.log (n : ℝ)) ^ 48)
  set H := Nat.floor ((Real.log (n : ℝ)) ^ 5)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hR1_pos : (0 : ℝ) < (R₁ : ℝ) := by exact_mod_cast (by omega : 0 < R₁)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let S_all := (Finset.Icc 3 n).filter Nat.Prime
  let S_low := (Finset.Icc 3 (Nat.sqrt n)).filter Nat.Prime
  let S_mid := S_all.filter (fun p : ℕ => Nat.sqrt n < p ∧ (p : ℝ) ≤ (n : ℝ) / (R₁ : ℝ))
  let S_hi := S_all.filter (fun p : ℕ => (n : ℝ) / (R₁ : ℝ) < (p : ℝ))
  have hS_part : S_all = S_low ∪ S_mid ∪ S_hi := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, S_all, S_low, S_mid, S_hi]
    constructor
    · rintro ⟨⟨hp3, hpn⟩, hp_pr⟩
      by_cases hsq : p ≤ Nat.sqrt n
      · left; left; exact ⟨⟨hp3, hsq⟩, hp_pr⟩
      · by_cases hhi : (p : ℝ) ≤ (n : ℝ) / (R₁ : ℝ)
        · left; right; exact ⟨⟨⟨hp3, hpn⟩, hp_pr⟩, by omega, hhi⟩
        · right; push Not at hhi; exact ⟨⟨⟨hp3, hpn⟩, hp_pr⟩, hhi⟩
    · rintro ((⟨⟨hp3, hsq⟩, hp_pr⟩ | ⟨⟨⟨hp3, hpn⟩, hp_pr⟩, _⟩) | ⟨⟨⟨hp3, hpn⟩, hp_pr⟩, _⟩)
      · exact ⟨⟨hp3, le_trans hsq (Nat.sqrt_le_self n)⟩, hp_pr⟩
      · exact ⟨⟨hp3, hpn⟩, hp_pr⟩
      · exact ⟨⟨hp3, hpn⟩, hp_pr⟩
  have hdisj_lm : Disjoint S_low S_mid := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [S_low, S_mid, Finset.mem_filter, Finset.mem_Icc] at h1 h2
    omega
  have hdisj_lm_h : Disjoint (S_low ∪ S_mid) S_hi := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [Finset.mem_union, S_low, S_mid, S_hi, Finset.mem_filter, Finset.mem_Icc] at h1 h2
    rcases h1 with h1 | h1
    · have hp_le_sq : (p : ℝ) ≤ Real.sqrt (n : ℝ) := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        exact_mod_cast le_trans (Nat.pow_le_pow_left h1.1.2 2) (Nat.sqrt_le' n)
      linarith [h2.2, hsqrt_lt]
    · linarith [h1.2.2, h2.2]
  let f_term : ℕ → ℝ := fun p =>
    (-1 : ℝ) ^ (padicValNat p (Nat.factorial n)) * (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
  have hDelta_split : Delta_parity n =
      (∑ p ∈ S_low, f_term p) + (∑ p ∈ S_mid, f_term p) + (∑ p ∈ S_hi, f_term p) := by
    rw [Delta_parity_eq_sum]
    change ∑ p ∈ S_all, f_term p = _
    rw [hS_part, Finset.sum_union hdisj_lm_h, Finset.sum_union hdisj_lm]
  have hlow_eq : ∑ p ∈ S_low, f_term p = -(n : ℝ) * Sigma_star_parity n + E_digit n :=
    exact_legendre_base_p_reduction n
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hed_n
  have hed_bound : |E_digit n| ≤ |C_ed| * ((n : ℝ) / Real.log (n : ℝ)) := by
    have h1 : Real.sqrt (n : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) := by
      rw [le_div_iff₀ hlogn_pos]
      have hln_le_sqrt : Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
        have hx14 : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
        have hlog14 : Real.log ((n : ℝ) ^ (1 / 4 : ℝ)) ≤ (n : ℝ) ^ (1 / 4 : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos hx14
        have hlog_eq4 : Real.log (n : ℝ) = 4 * Real.log ((n : ℝ) ^ (1 / 4 : ℝ)) := by
          rw [Real.log_rpow hn_pos]; ring
        have hsq14 : Real.sqrt (n : ℝ) = ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]
          congr 1; norm_num
        nlinarith [sq_nonneg ((n : ℝ) ^ (1 / 4 : ℝ) - 2)]
      calc Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
            mul_le_mul_of_nonneg_left hln_le_sqrt (Real.sqrt_nonneg _)
        _ = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
    calc |E_digit n| ≤ C_ed * Real.sqrt (n : ℝ) := hed_n
      _ ≤ |C_ed| * Real.sqrt (n : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
      _ ≤ |C_ed| * ((n : ℝ) / Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hhi_bound : |∑ p ∈ S_hi, f_term p - (Real.log 2 - 1) * (n : ℝ)| ≤
      (4 * |C₁| + 2) * ((n : ℝ) / Real.log (n : ℝ)) := by
    let Hr : ℕ → Finset ℕ := fun r =>
      ((Finset.Icc 2 (Nat.floor ((n : ℝ) / (r : ℝ)))).filter Nat.Prime).filter
        (fun p : ℕ => (n : ℝ) / ((r : ℝ) + 1) < (p : ℝ))
    have hS_hi_part : S_hi = (Finset.Icc 1 (R₁ - 1)).biUnion Hr := by
      ext p
      simp only [S_hi, S_all, Hr, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hp3, hpn⟩, hp_pr⟩, hp_gt⟩
        have hn_lt_psq : n < p ^ 2 := by
          have h1 : Real.sqrt (n : ℝ) < (p : ℝ) := lt_trans hsqrt_lt hp_gt
          rw [Real.sqrt_lt' (by exact_mod_cast hp_pr.pos)] at h1
          exact_mod_cast h1
        have hv : padicValNat p (Nat.factorial n) = n / p :=
          padicValNat_factorial_eq_div_of_lt_sq hp_pr hn_lt_psq
        have hdiv_ge : 1 ≤ n / p := Nat.div_pos hpn hp_pr.pos
        have hdiv_lt : n / p < R₁ := by
          rw [Nat.div_lt_iff_lt_mul hp_pr.pos]
          rw [div_lt_iff₀ hR1_pos] at hp_gt
          exact_mod_cast hp_gt
        let r := n / p
        refine ⟨r, ⟨hdiv_ge, by omega⟩, ⟨⟨hp_pr.two_le, ?_⟩, hp_pr⟩, ?_⟩
        · rw [Nat.le_floor_iff (by positivity), le_div_iff₀ (by exact_mod_cast hdiv_ge)]
          exact_mod_cast Nat.div_mul_le_self n p
        · rw [div_lt_iff₀ (by positivity)]
          have : n < (r + 1) * p := (Nat.div_lt_iff_lt_mul hp_pr.pos).mp (by omega : n / p < r + 1)
          have hR : (n : ℝ) < ((r + 1 : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast this
          push_cast at hR; linarith
      · rintro ⟨r, ⟨hr1, hrR⟩, ⟨⟨hp2, hp_hi⟩, hp_pr⟩, hp_lo⟩
        have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
        have hp_gt_r1 : (n : ℝ) / (R₁ : ℝ) < (p : ℝ) := by
          calc (n : ℝ) / (R₁ : ℝ) ≤ (n : ℝ) / ((r : ℝ) + 1) := by
                apply div_le_div_of_nonneg_left hn_pos.le (by positivity)
                exact_mod_cast (by omega : r + 1 ≤ R₁)
            _ < (p : ℝ) := hp_lo
        have hn_lt_psq : n < p ^ 2 := by
          have h1 : Real.sqrt (n : ℝ) < (p : ℝ) := lt_trans hsqrt_lt hp_gt_r1
          rw [Real.sqrt_lt' (by exact_mod_cast hp_pr.pos)] at h1
          exact_mod_cast h1
        have hp3 : 3 ≤ p := by
          have : (3 : ℝ) < Real.sqrt (n : ℝ) := by
            rw [Real.lt_sqrt (by norm_num)]; exact_mod_cast (by omega : 9 < n)
          have : (3 : ℝ) < (p : ℝ) := lt_trans this (lt_trans hsqrt_lt hp_gt_r1)
          exact_mod_cast this.le
        have hpn : p ≤ n := by
          rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hr_pos] at hp_hi
          have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
          exact_mod_cast (by nlinarith : (p : ℝ) ≤ (n : ℝ))
        exact ⟨⟨⟨hp3, hpn⟩, hp_pr⟩, hp_gt_r1⟩
    have hdisj_Hr : (Finset.Icc 1 (R₁ - 1) : Set ℕ).PairwiseDisjoint Hr := by
      intro r₁ hr₁ r₂ hr₂ hne
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_coe, Finset.mem_Icc] at hr₁ hr₂
      simp only [Hr, Finset.mem_filter, Finset.mem_Icc] at hp1 hp2
      have hr₁_pos : (0 : ℝ) < (r₁ : ℝ) := by exact_mod_cast hr₁.1
      have hr₂_pos : (0 : ℝ) < (r₂ : ℝ) := by exact_mod_cast hr₂.1
      have hhi1 := hp1.1.1.2
      have hhi2 := hp2.1.1.2
      rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hr₁_pos] at hhi1
      rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hr₂_pos] at hhi2
      have hlo1 := hp1.2; have hlo2 := hp2.2
      rw [div_lt_iff₀ (by positivity)] at hlo1 hlo2
      have h12 : (p : ℝ) * (r₁ : ℝ) < ((r₂ : ℝ) + 1) * (p : ℝ) := lt_of_le_of_lt hhi1 hlo2
      have h21 : (p : ℝ) * (r₂ : ℝ) < ((r₁ : ℝ) + 1) * (p : ℝ) := lt_of_le_of_lt hhi2 hlo1
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp1.1.2.pos
      have : r₁ < r₂ + 1 := by exact_mod_cast (by nlinarith : (r₁ : ℝ) < (r₂ : ℝ) + 1)
      have : r₂ < r₁ + 1 := by exact_mod_cast (by nlinarith : (r₂ : ℝ) < (r₁ : ℝ) + 1)
      omega
    have hr_val : ∀ r ∈ Finset.Icc 1 (R₁ - 1), ∀ p ∈ Hr r,
        f_term p = (-1 : ℝ) ^ r * (r : ℝ) * Real.log (p : ℝ) := by
      intro r hr p hp
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrR : r ≤ R₁ - 1 := (Finset.mem_Icc.mp hr).2
      simp only [Hr, Finset.mem_filter, Finset.mem_Icc] at hp
      have hp_pr : p.Prime := hp.1.2
      have hp_gt : (n : ℝ) / (R₁ : ℝ) < (p : ℝ) := by
        calc (n : ℝ) / (R₁ : ℝ) ≤ (n : ℝ) / ((r : ℝ) + 1) :=
              div_le_div_of_nonneg_left hn_pos.le (by positivity) (by exact_mod_cast (by omega : r + 1 ≤ R₁))
          _ < (p : ℝ) := hp.2
      have hn_lt_psq : n < p ^ 2 := by
        have h1 : Real.sqrt (n : ℝ) < (p : ℝ) := lt_trans hsqrt_lt hp_gt
        rw [Real.sqrt_lt' (by exact_mod_cast hp_pr.pos)] at h1
        exact_mod_cast h1
      have hv : padicValNat p (Nat.factorial n) = n / p :=
        padicValNat_factorial_eq_div_of_lt_sq hp_pr hn_lt_psq
      have hdiv_ge : r ≤ n / p := by
        rw [Nat.le_div_iff_mul_le hp_pr.pos]
        have := hp.1.1.2
        rw [Nat.le_floor_iff (by positivity), le_div_iff₀ (by exact_mod_cast hr1)] at this
        exact_mod_cast (by linarith : ((r * p : ℕ) : ℝ) ≤ (n : ℝ))
      have hdiv_lt : n / p < r + 1 := by
        rw [Nat.div_lt_iff_lt_mul hp_pr.pos]
        have := hp.2
        rw [div_lt_iff₀ (by positivity)] at this
        exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((p * (r + 1) : ℕ) : ℝ))
      have hvr : padicValNat p (Nat.factorial n) = r := by omega
      simp only [f_term, hvr]
    have hHr_sum : ∀ r ∈ Finset.Icc 1 (R₁ - 1),
        ∑ p ∈ Hr r, f_term p =
          (-1 : ℝ) ^ r * (r : ℝ) * (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) := by
      intro r hr
      rw [Finset.sum_congr rfl (hr_val r hr), ← Finset.mul_sum]
      congr 1
      have hsub : (Finset.Icc 2 (Nat.floor ((n : ℝ) / ((r : ℝ) + 1)))).filter Nat.Prime ⊆
          (Finset.Icc 2 (Nat.floor ((n : ℝ) / (r : ℝ)))).filter Nat.Prime := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
        exact ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_mono (div_le_div_of_nonneg_left hn_pos.le hr_pos (by linarith)))⟩, hp.2⟩
      have hsdiff : Hr r = (Finset.Icc 2 (Nat.floor ((n : ℝ) / (r : ℝ)))).filter Nat.Prime \
          (Finset.Icc 2 (Nat.floor ((n : ℝ) / ((r : ℝ) + 1)))).filter Nat.Prime := by
        ext p; simp only [Hr, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; refine ⟨⟨h1, h2⟩, fun ⟨h4, _⟩ => ?_⟩
          rw [Nat.le_floor_iff (by positivity)] at h4; linarith
        · rintro ⟨⟨h1, h2⟩, hnot⟩; refine ⟨⟨h1, h2⟩, ?_⟩
          by_contra hle; push Not at hle; apply hnot
          exact ⟨⟨h1.1, (Nat.le_floor_iff (by positivity)).mpr hle⟩, h2⟩
      rw [hsdiff]
      unfold thetaPrime
      have hs := Finset.sum_sdiff hsub (f := fun p => Real.log (p : ℝ))
      linarith
    rw [hS_hi_part, Finset.sum_biUnion hdisj_Hr, Finset.sum_congr rfl hHr_sum]
    have h_theta_err : ∑ r ∈ Finset.Icc 1 (R₁ - 1),
        |(-1 : ℝ) ^ r * (r : ℝ) * (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
          (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ)| ≤
        2 * |C₁| * ((n : ℝ) / Real.log (n : ℝ)) := by
      have hr_each : ∀ r ∈ Finset.Icc 1 (R₁ - 1),
          |(-1 : ℝ) ^ r * (r : ℝ) * (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
            (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ)| ≤
          2 * |C₁| * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) := by
        intro r hr
        have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        have hrR : r ≤ R₁ - 1 := (Finset.mem_Icc.mp hr).2
        have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
        have h_ge_R1 : (n : ℝ) / (R₁ : ℝ) ≤ (n : ℝ) / ((r : ℝ) + 1) :=
          div_le_div_of_nonneg_left hn_pos.le (by positivity) (by exact_mod_cast (by omega : r + 1 ≤ R₁))
        have h_ge_r : (n : ℝ) / ((r : ℝ) + 1) ≤ (n : ℝ) / (r : ℝ) :=
          div_le_div_of_nonneg_left hn_pos.le hr_pos (by linarith)
        have hb1 := hX₁ ((n : ℝ) / (r : ℝ)) (le_trans (le_max_left _ _) (le_trans hnX1 (le_trans h_ge_R1 h_ge_r)))
        have hb2 := hX₁ ((n : ℝ) / ((r : ℝ) + 1)) (le_trans (le_max_left _ _) (le_trans hnX1 h_ge_R1))
        rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)] at hb1 hb2
        have hexp1 : Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (r : ℝ)))) ≤
            Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) := by
          apply Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt _) (by linarith))
          exact Real.log_le_log (by positivity) (le_trans h_ge_R1 h_ge_r)
        have hexp2 : Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / ((r : ℝ) + 1)))) ≤
            Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) := by
          apply Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt _) (by linarith))
          exact Real.log_le_log (by positivity) h_ge_R1
        have hid : (-1 : ℝ) ^ r * (r : ℝ) * (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
            (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ) =
            (-1 : ℝ) ^ r * (r : ℝ) *
              ((thetaPrime ((n : ℝ) / (r : ℝ)) - (n : ℝ) / (r : ℝ)) -
                (thetaPrime ((n : ℝ) / ((r : ℝ) + 1)) - (n : ℝ) / ((r : ℝ) + 1))) := by
          field_simp [hr_pos.ne', by positivity : (r : ℝ) + 1 ≠ 0]; ring
        rw [hid, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hr_pos]
        have htri := abs_sub
          (thetaPrime ((n : ℝ) / (r : ℝ)) - (n : ℝ) / (r : ℝ))
          (thetaPrime ((n : ℝ) / ((r : ℝ) + 1)) - (n : ℝ) / ((r : ℝ) + 1))
        have he1 : |thetaPrime ((n : ℝ) / (r : ℝ)) - (n : ℝ) / (r : ℝ)| ≤
            |C₁| * ((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) :=
          calc |thetaPrime ((n : ℝ) / (r : ℝ)) - (n : ℝ) / (r : ℝ)|
              ≤ C₁ * (((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (r : ℝ))))) := hb1
            _ ≤ |C₁| * (((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ))))) :=
                mul_le_mul (le_abs_self _) (mul_le_mul_of_nonneg_left hexp1 (by positivity)) (by positivity) (abs_nonneg _)
            _ = |C₁| * ((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) := by ring
        have he2 : |thetaPrime ((n : ℝ) / ((r : ℝ) + 1)) - (n : ℝ) / ((r : ℝ) + 1)| ≤
            |C₁| * ((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) :=
          calc |thetaPrime ((n : ℝ) / ((r : ℝ) + 1)) - (n : ℝ) / ((r : ℝ) + 1)|
              ≤ C₁ * (((n : ℝ) / ((r : ℝ) + 1)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / ((r : ℝ) + 1))))) := hb2
            _ ≤ |C₁| * (((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ))))) :=
                mul_le_mul (le_abs_self _) (mul_le_mul h_ge_r hexp2 (by positivity) (by positivity)) (by positivity) (abs_nonneg _)
            _ = |C₁| * ((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) := by ring
        calc (r : ℝ) * |(thetaPrime ((n : ℝ) / (r : ℝ)) - (n : ℝ) / (r : ℝ)) -
              (thetaPrime ((n : ℝ) / ((r : ℝ) + 1)) - (n : ℝ) / ((r : ℝ) + 1))|
            ≤ (r : ℝ) * (2 * |C₁| * ((n : ℝ) / (r : ℝ)) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ))))) :=
              mul_le_mul_of_nonneg_left (by linarith) hr_pos.le
          _ = 2 * |C₁| * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) := by
              field_simp [hr_pos.ne']
      calc ∑ r ∈ Finset.Icc 1 (R₁ - 1),
              |(-1 : ℝ) ^ r * (r : ℝ) * (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
                (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ)|
          ≤ ∑ _r ∈ Finset.Icc 1 (R₁ - 1),
              2 * |C₁| * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) :=
            Finset.sum_le_sum hr_each
        _ = ((R₁ - 1 : ℕ) : ℝ) * (2 * |C₁| * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ))))) := by
            simp [Finset.sum_const, Nat.card_Icc]; ring_nf
        _ ≤ 2 * |C₁| * ((n : ℝ) / Real.log (n : ℝ)) *
              ((R₁ : ℝ) ^ 2 * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) * Real.log (n : ℝ)) := by
            have hR1_ge1 : (1 : ℝ) ≤ (R₁ : ℝ) := by exact_mod_cast (by omega : 1 ≤ R₁)
            have hR1_sub : ((R₁ - 1 : ℕ) : ℝ) ≤ (R₁ : ℝ) ^ 2 := by
              have : ((R₁ - 1 : ℕ) : ℝ) ≤ (R₁ : ℝ) := by exact_mod_cast (by omega : R₁ - 1 ≤ R₁)
              nlinarith
            have h_eq : 2 * |C₁| * ((n : ℝ) / Real.log (n : ℝ)) *
                  ((R₁ : ℝ) ^ 2 * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ)))) * Real.log (n : ℝ)) =
                (R₁ : ℝ) ^ 2 * (2 * |C₁| * (n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log ((n : ℝ) / (R₁ : ℝ))))) := by
              field_simp [hlogn_pos.ne']
            rw [h_eq]
            exact mul_le_mul_of_nonneg_right hR1_sub (by positivity)
        _ ≤ 2 * |C₁| * ((n : ℝ) / Real.log (n : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hexp_last (by positivity)
        _ = 2 * |C₁| * ((n : ℝ) / Real.log (n : ℝ)) := by ring
    have h_alt_err : |∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ) -
          (Real.log 2 - 1) * (n : ℝ)| ≤ 2 * ((n : ℝ) / Real.log (n : ℝ)) := by
      rw [← Finset.sum_mul, ← sub_mul, abs_mul, abs_of_pos hn_pos]
      have h_b := alt_harmonic_shifted_bound (by omega : 3 ≤ R₁)
      have h2_le : 2 / (R₁ : ℝ) ≤ 2 / Real.log (n : ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) hlogn_pos
        have hln_48 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 48 / 2 := by
          have : 2 ≤ (Real.log (n : ℝ)) ^ 47 := by
            have := one_le_pow₀ (by linarith : (1 : ℝ) ≤ Real.log (n : ℝ)) (n := 46)
            have : (Real.log (n : ℝ)) ^ 47 = Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 46 := by ring
            nlinarith
          nlinarith [show (Real.log (n : ℝ)) ^ 48 = Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ 47 from by ring]
        linarith
      calc |∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) - (Real.log 2 - 1)| * (n : ℝ)
          ≤ (2 / (R₁ : ℝ)) * (n : ℝ) := mul_le_mul_of_nonneg_right h_b hn_pos.le
        _ ≤ (2 / Real.log (n : ℝ)) * (n : ℝ) := mul_le_mul_of_nonneg_right h2_le hn_pos.le
        _ = 2 * ((n : ℝ) / Real.log (n : ℝ)) := by ring
    have htri := abs_add_le
      (∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r * (r : ℝ) *
          (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
        ∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ))
      (∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ) - (Real.log 2 - 1) * (n : ℝ))
    have hsum_tri : |∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r * (r : ℝ) *
          (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
        ∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ)| ≤
        2 * |C₁| * ((n : ℝ) / Real.log (n : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      exact le_trans (Finset.abs_sum_le_sum_abs _ _) h_theta_err
    linarith [show (∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r * (r : ℝ) *
          (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) - (Real.log 2 - 1) * (n : ℝ)) =
        (∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r * (r : ℝ) *
          (thetaPrime ((n : ℝ) / (r : ℝ)) - thetaPrime ((n : ℝ) / ((r : ℝ) + 1))) -
          ∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ)) +
        (∑ r ∈ Finset.Icc 1 (R₁ - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) * (n : ℝ) - (Real.log 2 - 1) * (n : ℝ)) from by ring]
  have hmid_bound : |∑ p ∈ S_mid, f_term p| ≤
      (Cθ * 2 + (2 + 4 * C₁e * (1 + Real.log 2) + (2 + 2 * Cm + 36 * C₁e))) * ((n : ℝ) / Real.log (n : ℝ)) := by
    have hp_val_mid : ∀ p ∈ S_mid, padicValNat p (Nat.factorial n) = n / p := by
      intro p hp
      simp only [S_mid, S_all, Finset.mem_filter, Finset.mem_Icc] at hp
      have hn_lt_psq : n < p ^ 2 := by
        have h1 : Nat.sqrt n + 1 ≤ p := hp.2.1
        calc n < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
          _ ≤ p ^ 2 := Nat.pow_le_pow_left h1 2
      exact padicValNat_factorial_eq_div_of_lt_sq hp.1.2 hn_lt_psq
    have hsplit_mid : ∑ p ∈ S_mid, f_term p =
        (∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ)) * Real.log (p : ℝ)) -
        (∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun p hp => ?_)
      simp only [f_term, hp_val_mid p hp]
      ring
    have hfrac_bound : |∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)| ≤
        Cθ * 2 * ((n : ℝ) / Real.log (n : ℝ)) := by
      have hsub : S_mid ⊆ (Finset.Icc 2 (Nat.floor ((n : ℝ) / (R₁ : ℝ)))).filter Nat.Prime := by
        intro p hp
        simp only [S_mid, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        exact ⟨⟨hp.1.2.two_le, (Nat.le_floor_iff (by positivity)).mpr hp.2.2⟩, hp.1.2⟩
      calc |∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)|
          ≤ ∑ p ∈ S_mid, |(-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ S_mid, Real.log (p : ℝ) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            simp only [S_mid, S_all, Finset.mem_filter, Finset.mem_Icc] at hp
            have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.1.2.pos
            have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
            have hfl_ge : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / (p : ℝ) := by
              rw [le_div_iff₀ hp_pos]; exact_mod_cast Nat.div_mul_le_self n p
            have hfl_lt : (n : ℝ) / (p : ℝ) < ((n / p : ℕ) : ℝ) + 1 := by
              rw [div_lt_iff₀ hp_pos]
              exact_mod_cast (by push_cast; linarith [Nat.lt_div_mul_add hp.1.2.pos (a := n)] :
                (n : ℝ) < (((n / p + 1 : ℕ) : ℝ) * (p : ℝ)))
            rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
              abs_of_nonneg (by linarith), abs_of_nonneg hlogp]
            nlinarith
        _ ≤ thetaPrime ((n : ℝ) / (R₁ : ℝ)) := by
            unfold thetaPrime
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_)
            have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
            exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
        _ ≤ Cθ * ((n : ℝ) / (R₁ : ℝ)) := by
            apply hCθ
            rw [le_div_iff₀ hR1_pos, one_mul]
            have : (Nat.sqrt n : ℝ) < (n : ℝ) / (R₁ : ℝ) := by
              have : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
                rw [Real.le_sqrt (by positivity) (by positivity)]
                exact_mod_cast Nat.sqrt_le' n
              linarith [hsqrt_lt]
            rw [lt_div_iff₀ hR1_pos] at this
            linarith
        _ ≤ Cθ * (2 * ((n : ℝ) / Real.log (n : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ hCθ_pos.le
            have h1 : (n : ℝ) / (R₁ : ℝ) ≤ 2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 48 := by
              rw [div_le_div_iff₀ hR1_pos (by positivity)]
              nlinarith [h48_le_2fl]
            have h2 : (Real.log (n : ℝ)) ≤ (Real.log (n : ℝ)) ^ 48 :=
              le_self_pow₀ (by linarith) (by norm_num : 48 ≠ 0)
            have h3 : (n : ℝ) / (Real.log (n : ℝ)) ^ 48 ≤ (n : ℝ) / Real.log (n : ℝ) :=
              div_le_div_of_nonneg_left hn_pos.le hlogn_pos h2
            linarith
        _ = Cθ * 2 * ((n : ℝ) / Real.log (n : ℝ)) := by ring
    have hmain_mid : |∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ)) * Real.log (p : ℝ)| ≤
        (2 + 4 * C₁e * (1 + Real.log 2) + (2 + 2 * Cm + 36 * C₁e)) * ((n : ℝ) / Real.log (n : ℝ)) := by
      rcases eq_or_ne S_mid ∅ with h_empty | h_ne
      · rw [h_empty, Finset.sum_empty, abs_zero]; positivity
      · have hA_ge1 : (1 : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast (by omega : 1 ≤ Nat.sqrt n)
        have hAB : (Nat.sqrt n : ℝ) ≤ (n : ℝ) / (R₁ : ℝ) := by
          obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr h_ne
          simp only [S_mid, Finset.mem_filter] at hp0
          have : ((Nat.sqrt n : ℝ)) < (p0 : ℝ) := by exact_mod_cast hp0.2.1
          linarith [hp0.2.2]
        have hI_mem : ∀ p ∈ S_mid, (Nat.sqrt n : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ) / (R₁ : ℝ) := by
          intro p hp
          simp only [S_mid, Finset.mem_filter] at hp
          exact ⟨by exact_mod_cast hp.2.1, hp.2.2⟩
        obtain ⟨hpart_mid, hdisj_mid⟩ := dyadic_partition_finset hA_ge1 hAB S_mid hI_mem
        obtain ⟨c_tilde, b_tilde, h_supp, h_ctilde_b, h_btilde0, h_btilde_b, h_vaaler_pw, h_L1⟩ :=
          vaaler_parity_approx H hH_ge1
        have hfloor_eq : ∀ p ∈ S_mid, (-1 : ℝ) ^ (n / p) = (-1 : ℝ) ^ (Int.floor ((n : ℝ) / (p : ℝ))) := by
          intro p hp
          simp only [S_mid, S_all, Finset.mem_filter] at hp
          have hfl : Int.floor ((n : ℝ) / (p : ℝ)) = ((n / p : ℕ) : ℤ) := by
            rw [Int.floor_eq_iff]
            have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.1.2.pos
            constructor
            · rw [Int.cast_natCast, le_div_iff₀ hp_pos]; exact_mod_cast Nat.div_mul_le_self n p
            · rw [Int.cast_natCast, div_lt_iff₀ hp_pos]
              exact_mod_cast (by push_cast; linarith [Nat.lt_div_mul_add hp.1.2.pos (a := n)] :
                (n : ℝ) < (((n / p + 1 : ℕ) : ℝ) * (p : ℝ)))
          rw [hfl, zpow_natCast]
        let mainSum : ℂ := ∑ p ∈ S_mid,
          (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
            ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
              c_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)
        have h_diff_bound :
            |∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ)) * Real.log (p : ℝ)| ≤
            ‖mainSum‖ + ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) *
              (b_tilde 0 + ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re := by
          have h_re : (∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ)) * Real.log (p : ℝ)) =
              (mainSum + ∑ p ∈ S_mid, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
                ((((-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ)) : ℝ) : ℂ) -
                  ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h),
                    c_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2))).re := by
            rw [Complex.add_re, Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun p hp => ?_)
            rw [← mul_add, add_sub_cancel, hfloor_eq p hp]
            norm_cast
          rw [h_re]
          calc |(mainSum + _).re| ≤ ‖mainSum + _‖ := Complex.abs_re_le_norm _
            _ ≤ ‖mainSum‖ + ‖∑ p ∈ S_mid, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) * _‖ := norm_add_le _ _
            _ ≤ ‖mainSum‖ + ∑ p ∈ S_mid, ‖(((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) * _‖ :=
                add_le_add le_rfl (norm_sum_le _ _)
            _ ≤ ‖mainSum‖ + ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) * _ := by
                apply add_le_add le_rfl
                refine Finset.sum_le_sum (fun p hp => ?_)
                simp only [S_mid, S_all, Finset.mem_filter] at hp
                have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp.1.2.pos
                have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
                have hcoeff_nn : 0 ≤ (n : ℝ) / (p : ℝ) * Real.log (p : ℝ) := by positivity
                rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcoeff_nn]
                apply mul_le_mul_of_nonneg_left _ hcoeff_nn
                have hpw := (h_vaaler_pw ((n : ℝ) / (p : ℝ))).2
                have hsplit0 : ∑ h ∈ Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1),
                    b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2) =
                    b_tilde 0 + ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                      b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2) := by
                  have h0_mem : (0 : ℤ) ∈ Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1) := by
                    simp only [Finset.mem_Icc]; omega
                  rw [← Finset.add_sum_erase _ _ h0_mem]
                  congr 1
                  · simp [eExp]
                  · congr 1; ext h; simp [Finset.mem_erase, Finset.mem_filter]; tauto
                rwa [hsplit0] at hpw
        have h_block_exp : ∀ (k : ℕ) (hk : k ∈ dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ)))
            (h : ℤ) (hh0 : h ≠ 0) (hh_le : |h| ≤ 2 * (H : ℤ) + 1),
            ‖∑ p ∈ S_mid.filter (fun p : ℕ => (Nat.sqrt n : ℝ) * (2 : ℝ) ^ k < (p : ℝ) ∧
                (p : ℝ) ≤ 2 * ((Nat.sqrt n : ℝ) * (2 : ℝ) ^ k)),
              (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)‖ ≤
            C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ) := by
          intro k hk h hh0 hh_le
          let P := (Nat.sqrt n : ℝ) * (2 : ℝ) ^ k
          let Ik := S_mid.filter (fun p : ℕ => P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P)
          have hP_ge_sqrt : (Nat.sqrt n : ℝ) ≤ P :=
            le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
          have hP_lo : (n : ℝ) ^ (1 / 3 : ℝ) ≤ P := le_trans h13_sqrtN hP_ge_sqrt
          have hP_lt_B : P < (n : ℝ) / (R₁ : ℝ) := (Finset.mem_filter.mp hk).2
          have hP_hi : P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := le_trans hP_lt_B.le hdiv_r1_12
          have hIk_pr : ∀ p ∈ Ik, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P := by
            intro p hp
            simp only [Ik, Finset.mem_filter, S_mid, S_all] at hp
            exact ⟨hp.1.1.2, hp.2⟩
          have hexp_app := hexp_n P Ik {1} (fun _ => h) (fun t => (n : ℝ) / t) ((n : ℝ) / P)
            hP_lo hP_hi hIk_pr (fun r hr => by rw [Finset.mem_singleton.mp hr]; omega)
            ⟨1, Finset.mem_singleton_self _, hh0⟩
            (fun r hr => by
              rw [Finset.mem_singleton.mp hr]
              have h5_eq : Nat.floor (1 / (1 / 3 : ℝ)) + 2 = 5 := by norm_num
              rw [h5_eq]
              exact hh_le)
            (fun r hr => by
              rw [Finset.mem_singleton.mp hr, pow_one]
              have h1 : (R₁ : ℝ) ≤ (n : ℝ) / P := (le_div_iff₀ (by positivity)).mpr (by
                rw [mul_comm, ← le_div_iff₀ hR1_pos]; exact hP_lt_B.le)
              calc (2 : ℝ) ^ (-(Nat.floor (1 / (1 / 3 : ℝ)) : ℕ) : ℤ) *
                    (Real.log (n : ℝ)) ^ (6 * Nat.floor (1 / (1 / 3 : ℝ)) + 30)
                  ≤ (Real.log (n : ℝ)) ^ 48 / 2 := hpow48
                _ ≤ (R₁ : ℝ) := by linarith
                _ ≤ (n : ℝ) / P := h1)
            (fun t ht => by
              rw [abs_of_nonneg (div_nonneg hn_pos.le (by linarith [ht.1, hP_lo, hn_pos]))]
              exact div_le_div_of_nonneg_left hn_pos.le (by positivity) ht.1)
            (by positivity)
          dsimp only at hexp_app
          have h_rhs : C₁e * ((n : ℝ) / P) * P * (Real.log (n : ℝ)) ^ (-((Nat.floor (1 / (1 / 3 : ℝ)) : ℝ) + 2)) =
              C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ) := by
            have hP_pos : P ≠ 0 := by positivity
            have hR3 : (Nat.floor (1 / (1 / 3 : ℝ)) : ℝ) + 2 = 5 := by norm_num
            rw [hR3]
            field_simp [hP_pos]
          rw [← h_rhs]
          have h_sum_eq : ∑ p ∈ Ik, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2) =
              ∑ p ∈ Ik, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
                eExp (∑ r ∈ ({1} : Finset ℕ), (h : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ r)) := by
            refine Finset.sum_congr rfl (fun p _ => ?_)
            congr 2; simp [Finset.sum_singleton]; ring
          rw [h_sum_eq]
          exact hexp_app.1.2
        have hdy_card_le : ((dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ))).card : ℝ) ≤
            Real.log (n : ℝ) / Real.log 2 + 2 := by
          calc ((dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ))).card : ℝ)
              ≤ Real.log (((n : ℝ) / (R₁ : ℝ)) / (Nat.sqrt n : ℝ)) / Real.log 2 + 2 :=
                dyadicBlocks_card_le hA_ge1 hAB
            _ ≤ Real.log (n : ℝ) / Real.log 2 + 2 := by
                apply add_le_add_right
                apply div_le_div_of_nonneg_right _ hlog2_pos.le
                apply Real.log_le_log (by positivity)
                rw [div_le_iff₀ (by positivity)]
                calc (n : ℝ) / (R₁ : ℝ) ≤ (n : ℝ) / 1 :=
                      div_le_div_of_nonneg_left hn_pos.le (by norm_num) (by exact_mod_cast (by omega : 1 ≤ R₁))
                  _ ≤ (n : ℝ) * (Nat.sqrt n : ℝ) := by rw [div_one]; exact le_mul_of_one_le_right hn_pos.le hA_ge1
        have hmain_le : ‖mainSum‖ ≤ (2 + 4 * C₁e * (1 + Real.log 2)) * ((n : ℝ) / Real.log (n : ℝ)) := by
          let oddH := (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun h => h ≠ 0 ∧ Odd h)
          have h_swap : mainSum = ∑ h ∈ oddH, c_tilde h * ∑ k ∈ dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ)),
              ∑ p ∈ S_mid.filter (fun p : ℕ => (Nat.sqrt n : ℝ) * (2 : ℝ) ^ k < (p : ℝ) ∧
                  (p : ℝ) ≤ 2 * ((Nat.sqrt n : ℝ) * (2 : ℝ) ^ k)),
                (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2) := by
            unfold mainSum
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun h _ => ?_)
            rw [← Finset.mul_sum]
            congr 1
            conv_lhs => rw [hpart_mid]
            rw [Finset.sum_biUnion hdisj_mid]
          rw [h_swap]
          calc ‖∑ h ∈ oddH, c_tilde h * ∑ k ∈ dyadicBlocks _ _, _‖
              ≤ ∑ h ∈ oddH, ‖c_tilde h‖ * ‖∑ k ∈ dyadicBlocks _ _, _‖ := by
                refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun h _ => by rw [norm_mul]))
            _ ≤ ∑ h ∈ oddH, ‖c_tilde h‖ *
                  (((dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ))).card : ℝ) *
                    (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ))) := by
                refine Finset.sum_le_sum (fun h hh => ?_)
                apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                calc ‖∑ k ∈ dyadicBlocks _ _, _‖
                    ≤ ∑ k ∈ dyadicBlocks _ _, ‖∑ p ∈ _, _‖ := norm_sum_le _ _
                  _ ≤ ∑ _k ∈ dyadicBlocks _ _, (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ)) := by
                      refine Finset.sum_le_sum (fun k hk => h_block_exp k hk h
                        (Finset.mem_filter.mp hh).2.1
                        (by have := Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1; rw [abs_le]; omega))
                  _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
            _ = (∑ h ∈ oddH, ‖c_tilde h‖) *
                  (((dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ))).card : ℝ) *
                    (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ))) := by rw [← Finset.sum_mul]
            _ ≤ ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) *
                  ((Real.log (n : ℝ) / Real.log 2 + 2) * (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ))) :=
                mul_le_mul h_L1 (mul_le_mul_of_nonneg_right hdy_card_le (by positivity)) (by positivity) (by positivity)
            _ = (4 / Real.pi) * C₁e * (n : ℝ) *
                  (((Real.log (2 * (H : ℝ) + 1) + 1) * (Real.log (n : ℝ) / Real.log 2 + 2)) *
                    (Real.log (n : ℝ)) ^ (-5 : ℝ)) := by ring
            _ ≤ (4 / Real.pi) * C₁e * (n : ℝ) * ((Real.log (n : ℝ)) ^ 4 * (Real.log (n : ℝ)) ^ (-5 : ℝ)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_right hloglog4 (by positivity)
            _ ≤ (2 + 4 * C₁e * (1 + Real.log 2)) * ((n : ℝ) / Real.log (n : ℝ)) := by
                have hrp : (Real.log (n : ℝ)) ^ 4 * (Real.log (n : ℝ)) ^ (-5 : ℝ) = 1 / Real.log (n : ℝ) := by
                  rw [← Real.rpow_natCast (Real.log (n : ℝ)) 4, ← Real.rpow_add hlogn_pos]
                  norm_num [Real.rpow_neg_one]
                rw [hrp]
                have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
                have h4pi : 4 / Real.pi ≤ 4 := div_le_self (by norm_num) hpi
                calc (4 / Real.pi) * C₁e * (n : ℝ) * (1 / Real.log (n : ℝ))
                    = ((4 / Real.pi) * C₁e) * ((n : ℝ) / Real.log (n : ℝ)) := by ring
                  _ ≤ (4 * C₁e) * ((n : ℝ) / Real.log (n : ℝ)) :=
                      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4pi hC₁e.le) (by positivity)
                  _ ≤ (2 + 4 * C₁e * (1 + Real.log 2)) * ((n : ℝ) / Real.log (n : ℝ)) := by
                      apply mul_le_mul_of_nonneg_right _ (by positivity)
                      nlinarith [hlog2_pos]
        have hB_err_le : ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) *
            (b_tilde 0 + ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
              b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re ≤
            (2 + 2 * Cm + 36 * C₁e) * ((n : ℝ) / Real.log (n : ℝ)) := by
          have h_split_re : ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) *
              (b_tilde 0 + ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re =
              (b_tilde 0).re * ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) +
              (∑ p ∈ S_mid, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
                ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                  b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re := by
            rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun p _ => ?_)
            rw [Complex.add_re, mul_add]
            congr 1
            · ring
            · simp [Complex.mul_re]
          rw [h_split_re]
          have h0_bound : (b_tilde 0).re * ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) ≤
              (2 + 2 * Cm) * ((n : ℝ) / Real.log (n : ℝ)) := by
            rw [h_btilde0]
            have hb0_re : ((2 / ((H : ℂ) + 1)).re) = 2 / ((H : ℝ) + 1) := by
              have : (2 : ℂ) / ((H : ℂ) + 1) = ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
              rw [this, Complex.ofReal_re]
            rw [hb0_re]
            have hsub : S_mid ⊆ (Finset.Icc 3 (Nat.floor (n : ℝ))).filter Nat.Prime := by
              intro p hp; simp only [S_mid, S_all, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
              exact ⟨⟨hp.1.1.1, (Nat.le_floor_iff hn_pos.le).mpr (by exact_mod_cast hp.1.1.2)⟩, hp.1.2⟩
            have hmert : ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ)) ≤
                (n : ℝ) * (Real.log (n : ℝ) + Cm) := by
              calc ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ))
                  = (n : ℝ) * ∑ p ∈ S_mid, Real.log (p : ℝ) / (p : ℝ) := by
                    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun _ _ => by ring)
                _ ≤ (n : ℝ) * ∑ p ∈ (Finset.Icc 3 (Nat.floor (n : ℝ))).filter Nat.Prime,
                      Real.log (p : ℝ) / (p : ℝ) := by
                    apply mul_le_mul_of_nonneg_left _ hn_pos.le
                    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by
                      have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
                      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
                      positivity)
                _ ≤ (n : ℝ) * (Real.log (n : ℝ) + Cm) := mul_le_mul_of_nonneg_left (hCm n (by exact_mod_cast (by omega : 3 ≤ n))) hn_pos.le
            have h_sum_le : 2 * (Real.log (n : ℝ) + Cm) / ((H : ℝ) + 1) ≤ (2 + 2 * Cm) / Real.log (n : ℝ) := by
              have h_2H : (Real.log (n : ℝ)) ^ 2 ≤ (H : ℝ) + 1 := by
                have h2_le_5 : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 5 :=
                  pow_le_pow_right₀ (by linarith) (by norm_num)
                linarith
              have h1 : 2 * (Real.log (n : ℝ) + Cm) / ((H : ℝ) + 1) ≤
                  2 * (Real.log (n : ℝ) + Cm) / (Real.log (n : ℝ)) ^ 2 :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) h_2H
              have h2 : 2 * (Real.log (n : ℝ) + Cm) / (Real.log (n : ℝ)) ^ 2 ≤ (2 + 2 * Cm) / Real.log (n : ℝ) := by
                rw [div_le_div_iff₀ (by positivity) hlogn_pos]
                nlinarith [hln]
              exact le_trans h1 h2
            calc (2 / ((H : ℝ) + 1)) * ∑ p ∈ S_mid, ((n : ℝ) / (p : ℝ) * Real.log (p : ℝ))
                ≤ (2 / ((H : ℝ) + 1)) * ((n : ℝ) * (Real.log (n : ℝ) + Cm)) :=
                  mul_le_mul_of_nonneg_left hmert (by positivity)
              _ = (n : ℝ) * (2 * (Real.log (n : ℝ) + Cm) / ((H : ℝ) + 1)) := by ring
              _ ≤ (n : ℝ) * ((2 + 2 * Cm) / Real.log (n : ℝ)) :=
                  mul_le_mul_of_nonneg_left h_sum_le hn_pos.le
              _ = (2 + 2 * Cm) * ((n : ℝ) / Real.log (n : ℝ)) := by ring
          have hnz_bound : (∑ p ∈ S_mid, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
                ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                  b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2)).re ≤
              36 * C₁e * ((n : ℝ) / Real.log (n : ℝ)) := by
            let nzH := (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0)
            have h_swap : ∑ p ∈ S_mid, (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) *
                  ∑ h ∈ nzH, b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2) =
                ∑ h ∈ nzH, b_tilde h * ∑ k ∈ dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ)),
                  ∑ p ∈ S_mid.filter (fun p : ℕ => (Nat.sqrt n : ℝ) * (2 : ℝ) ^ k < (p : ℝ) ∧
                      (p : ℝ) ≤ 2 * ((Nat.sqrt n : ℝ) * (2 : ℝ) ^ k)),
                    (((n : ℝ) / (p : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ)) / 2) := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun h _ => ?_)
              rw [← Finset.mul_sum]
              congr 1
              conv_lhs => rw [hpart_mid]
              rw [Finset.sum_biUnion hdisj_mid]
            refine le_trans (Complex.re_le_abs _) ?_
            rw [← Complex.norm_eq_abs, h_swap]
            have hnz_card : (nzH.card : ℝ) ≤ 4 * (H : ℝ) + 3 := by
              have h1 : nzH.card ≤ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).card :=
                Finset.card_filter_le _ _
              have h2 : (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).card = 4 * H + 3 := by
                rw [Int.card_Icc]; omega
              exact_mod_cast le_trans h1 h2.le
            have hdy_le_3log : ((dyadicBlocks (Nat.sqrt n : ℝ) ((n : ℝ) / (R₁ : ℝ))).card : ℝ) ≤ 3 * Real.log (n : ℝ) := by
              have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
              have : Real.log (n : ℝ) / Real.log 2 ≤ 2 * Real.log (n : ℝ) := by
                rw [div_le_iff₀ hlog2_pos]; nlinarith
              linarith
            calc ‖∑ h ∈ nzH, b_tilde h * ∑ k ∈ dyadicBlocks _ _, _‖
                ≤ ∑ h ∈ nzH, ‖b_tilde h‖ * ‖∑ k ∈ dyadicBlocks _ _, _‖ := by
                  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun h _ => by rw [norm_mul]))
              _ ≤ ∑ _h ∈ nzH, (3 / ((H : ℝ) + 1)) *
                    ((3 * Real.log (n : ℝ)) * (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ))) := by
                  refine Finset.sum_le_sum (fun h hh => ?_)
                  refine mul_le_mul (h_btilde_b h).le ?_ (norm_nonneg _) (by positivity)
                  calc ‖∑ k ∈ dyadicBlocks _ _, _‖
                      ≤ ∑ k ∈ dyadicBlocks _ _, ‖∑ p ∈ _, _‖ := norm_sum_le _ _
                    _ ≤ ∑ _k ∈ dyadicBlocks _ _, (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ)) := by
                        refine Finset.sum_le_sum (fun k hk => h_block_exp k hk h
                          (Finset.mem_filter.mp hh).2
                          (by have := Finset.mem_Icc.mp (Finset.mem_filter.mp hh).1; rw [abs_le]; omega))
                    _ = ((dyadicBlocks _ _).card : ℝ) * (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ)) := by
                        simp [Finset.sum_const, nsmul_eq_mul]
                    _ ≤ (3 * Real.log (n : ℝ)) * (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ)) :=
                        mul_le_mul_of_nonneg_right hdy_le_3log (by positivity)
              _ = (nzH.card : ℝ) * (3 / ((H : ℝ) + 1)) *
                    (3 * Real.log (n : ℝ) * (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ))) := by
                  simp [Finset.sum_const, nsmul_eq_mul]; ring
              _ ≤ 12 * (3 * Real.log (n : ℝ) * (C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ))) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
                  linarith
              _ = 36 * C₁e * (n : ℝ) * (Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ)) := by ring
              _ ≤ 36 * C₁e * ((n : ℝ) / Real.log (n : ℝ)) := by
                  have h_rpow : Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (-5 : ℝ) = (Real.log (n : ℝ)) ^ (-4 : ℝ) := by
                    conv_lhs => rw [← Real.rpow_one (Real.log (n : ℝ)), ← Real.rpow_add hlogn_pos]
                    congr 1; norm_num
                  have h_le_inv : (Real.log (n : ℝ)) ^ (-4 : ℝ) ≤ 1 / Real.log (n : ℝ) := by
                    rw [show (-4 : ℝ) = -(4 : ℕ) from by norm_num, Real.rpow_neg hlogn_pos.le,
                      Real.rpow_natCast, one_div]
                    exact inv_anti₀ hlogn_pos (le_self_pow₀ (by linarith) (by norm_num : 4 ≠ 0))
                  rw [h_rpow]
                  calc 36 * C₁e * (n : ℝ) * (Real.log (n : ℝ)) ^ (-4 : ℝ)
                      ≤ 36 * C₁e * (n : ℝ) * (1 / Real.log (n : ℝ)) :=
                        mul_le_mul_of_nonneg_left h_le_inv (by positivity)
                    _ = 36 * C₁e * ((n : ℝ) / Real.log (n : ℝ)) := by ring
          linarith
        linarith [h_diff_bound, hmain_le, hB_err_le]
      have htri := abs_sub
        (∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ)) * Real.log (p : ℝ))
        (∑ p ∈ S_mid, (-1 : ℝ) ^ (n / p) * ((n : ℝ) / (p : ℝ) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ))
      linarith [hsplit_mid, hfrac_bound, hmain_mid]
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ) / Real.log (n : ℝ))]
  have hid : Delta_parity n - (Real.log 2 - 1 - Sigma_star_parity n) * (n : ℝ) =
      E_digit n + ∑ p ∈ S_mid, f_term p + (∑ p ∈ S_hi, f_term p - (Real.log 2 - 1) * (n : ℝ)) := by
    rw [hDelta_split, hlow_eq]
    ring
  rw [hid]
  have h1 := abs_add_le (E_digit n + ∑ p ∈ S_mid, f_term p) (∑ p ∈ S_hi, f_term p - (Real.log 2 - 1) * (n : ℝ))
  have h2 := abs_add_le (E_digit n) (∑ p ∈ S_mid, f_term p)
  linarith [hed_bound, hmid_bound, hhi_bound, h1, h2]

/-! ### Theorem 2.5(ii): Collar-Decomposed Cancellation and 50–50 Split (eq. 2.16–2.17) -/

private theorem collar_band_isBigO (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3)
    (r : ℕ) (hr2 : 2 ≤ r) (hrR : r ≤ Nat.floor (1 / δ)) :
    (fun n : ℕ => ∑ p ∈ ((Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
        p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧
        (p : ℝ) ∈ collar n r (6 * Nat.floor (1 / δ) + 30))),
      ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1)) * (Real.log (p : ℝ) / ((p : ℝ) - 1)))
      =O[atTop] (fun n : ℕ => 1 / Real.log (n : ℝ)) := by
  set R := Nat.floor (1 / δ)
  set A_R := 6 * R + 30
  have hR3 : 3 ≤ R := by
    rw [Nat.le_floor_iff (by positivity)]
    rw [le_div_iff₀ hδ0]
    linarith
  obtain ⟨η', η, hη', hη, C₁e, C₂e, C₃e, hC₁e, hC₂e, hC₃e, hExp⟩ :=
    prime_exp_sum_bounds δ hδ0 hδ1
  obtain ⟨Cm, hCm_pos, hCm⟩ := mertens_sum_le
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_rpow_poly : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ (A_R + R * (R + 2) + 1) / (n : ℝ) ^ η)
      atTop (nhds 0) :=
    log_pow_div_rpow_tendsto_zero (A_R + R * (R + 2) + 1) hη
  have h_rpow_div : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ A_R / (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))))
      atTop (nhds 0) :=
    log_pow_div_rpow_tendsto_zero A_R (by positivity)
  have h_sqrt_12 : ∀ᶠ n : ℕ in atTop,
      (Nat.sqrt n : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := by
    have ht := log_pow_div_rpow_tendsto_zero 12 (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [Filter.eventually_ge_atTop 4,
      (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le)] with n hn hsm
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h1 := (div_le_iff₀ (by positivity)).mp hsm
    rw [← Real.sqrt_eq_rpow] at h1
    have h2 : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]; exact_mod_cast Nat.sqrt_le' n
    rw [le_div_iff₀ (by positivity)]
    calc (Nat.sqrt n : ℝ) * (Real.log (n : ℝ)) ^ 12 ≤ Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 12 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          linarith
      _ = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
  let M_clean : ℝ := 2 ^ R * (2 + 2 * Cm) + 48 ^ R * (4 * C₃e)
  refine Asymptotics.IsBigO.of_bound M_clean ?_
  filter_upwards [Filter.eventually_ge_atTop 16, hExp, h_sqrt_12,
    hlog_inf.eventually (eventually_ge_atTop 100),
    (h_rpow_poly.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ h => h.le),
    (h_rpow_div.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ h => h.le)] with
    n hn hexp_n hsq12 hln100 hpoly_sm hdiv_sm
  set H := Nat.floor ((Real.log (n : ℝ)) ^ (R + 2))
  set M_r := Nat.floor ((Real.log (n : ℝ)) ^ A_R)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hH_ge1 : 1 ≤ H := by
    rw [Nat.le_floor_iff (by positivity)]
    exact_mod_cast one_le_pow₀ (by linarith : (1 : ℝ) ≤ Real.log (n : ℝ)) (n := R + 2)
  have hH_le : (H : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) := Nat.floor_le (by positivity)
  let S_r := (Finset.Icc 3 (Nat.sqrt n)).filter (fun p : ℕ =>
    p.Prime ∧ (n : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ∈ collar n r A_R)
  have h_pow_R1 : ∀ p ∈ S_r, n < p ^ (R + 1) := by
    intro p hp
    have hp_gt : (n : ℝ) ^ δ < (p : ℝ) := (Finset.mem_filter.mp hp).2.2.1
    have h1_lt_R1 : 1 < δ * ((R : ℝ) + 1) := by
      have : 1 / δ < (R : ℝ) + 1 := Nat.lt_floor_add_one (1 / δ)
      nlinarith [(div_lt_iff₀ hδ0).mp this]
    have h_lt : (n : ℝ) < (p : ℝ) ^ (R + 1) := by
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ < (n : ℝ) ^ (δ * ((R : ℝ) + 1)) :=
            Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < n)) h1_lt_R1
        _ = ((n : ℝ) ^ δ) ^ (R + 1) := by
            rw [← Real.rpow_natCast ((n : ℝ) ^ δ) (R + 1), ← Real.rpow_mul hn_pos.le]
        _ < (p : ℝ) ^ (R + 1) := pow_lt_pow_left₀ hp_gt (by positivity) (by omega)
    exact_mod_cast h_lt
  let J : ℕ → Finset ℕ := fun m_r =>
    S_r.filter (fun p : ℕ => (p : ℝ) ∈ collarSubinterval n r m_r A_R)
  have hS_r_part : S_r = (Finset.Icc 1 M_r).biUnion J := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_Icc, J, Finset.mem_filter]
    constructor
    · intro hp
      have hp_col := (Finset.mem_filter.mp hp).2.2.2
      obtain ⟨hp_lo, hp_hi⟩ := hp_col
      have hp_pos : (0 : ℝ) < (p : ℝ) := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; positivity
      have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
      have hpr_le_n : (p : ℝ) ^ r ≤ (n : ℝ) := by
        have := Real.rpow_le_rpow hp_pos.le hp_hi hr_pos.le
        rw [← Real.rpow_mul hn_pos.le, one_div_mul_cancel hr_pos.ne', Real.rpow_one, Real.rpow_natCast] at this
        exact this
      have hpr_gt : (n : ℝ) / (Real.log (n : ℝ)) ^ A_R < (p : ℝ) ^ r := by
        have := Real.rpow_lt_rpow (by positivity) hp_lo hr_pos
        rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hn_pos.le,
          ← Real.rpow_mul (by positivity), one_div_mul_cancel hr_pos.ne',
          div_mul_cancel₀ _ hr_pos.ne', Real.rpow_one, Real.rpow_natCast, Real.rpow_natCast] at this
        exact this
      have hdiv_ge1 : 1 ≤ n / p ^ r := by
        rw [Nat.le_div_iff_mul_le (pow_pos (Finset.mem_filter.mp hp).2.1.pos r), one_mul]
        exact_mod_cast hpr_le_n
      have hdiv_le_Mr : n / p ^ r ≤ M_r := by
        rw [Nat.le_floor_iff (by positivity)]
        have h1 : ((n / p ^ r : ℕ) : ℝ) ≤ (n : ℝ) / (p : ℝ) ^ r := by
          rw [le_div_iff₀ (by positivity)]
          exact_mod_cast Nat.div_mul_le_self n (p ^ r)
        have h2 : (n : ℝ) / (p : ℝ) ^ r < (Real.log (n : ℝ)) ^ A_R := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ (by positivity)] at hpr_gt
          linarith
        linarith
      refine ⟨n / p ^ r, ⟨hdiv_ge1, hdiv_le_Mr⟩, hp, ⟨?_, hp_col⟩⟩
      constructor
      · have h_nat : n < (n / p ^ r + 1) * p ^ r := (Nat.div_lt_iff_lt_mul (pow_pos (Finset.mem_filter.mp hp).2.1.pos r)).mp (by omega)
        have h_real : (n : ℝ) / ((n / p ^ r : ℕ) + 1 : ℝ) < (p : ℝ) ^ r := by
          rw [div_lt_iff₀ (by positivity)]
          exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((n / p ^ r + 1 : ℕ) : ℝ) * ((p ^ r : ℕ) : ℝ))
        have := Real.rpow_lt_rpow (by positivity) h_real (by positivity : 0 < 1 / (r : ℝ))
        rwa [← Real.rpow_natCast (p : ℝ) r, ← Real.rpow_mul hp_pos.le, mul_one_div_cancel hr_pos.ne', Real.rpow_one] at this
      · have h_nat : (n / p ^ r) * p ^ r ≤ n := Nat.div_mul_le_self n (p ^ r)
        have h_real : (p : ℝ) ^ r ≤ (n : ℝ) / ((n / p ^ r : ℕ) : ℝ) := by
          rw [le_div_iff₀ (by exact_mod_cast hdiv_ge1)]
          exact_mod_cast (by linarith : ((p ^ r * (n / p ^ r) : ℕ) : ℝ) ≤ (n : ℝ))
        have := Real.rpow_le_rpow (by positivity) h_real (by positivity : 0 ≤ 1 / (r : ℝ))
        rwa [← Real.rpow_natCast (p : ℝ) r, ← Real.rpow_mul hp_pos.le, mul_one_div_cancel hr_pos.ne', Real.rpow_one] at this
    · rintro ⟨m_r, _, hp, _⟩; exact hp
  have hdisj_J : (Finset.Icc 1 M_r : Set ℕ).PairwiseDisjoint J := by
    intro m₁ hm₁ m₂ hm₂ hne
    dsimp only [Function.onFun]; rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_coe, Finset.mem_Icc] at hm₁ hm₂
    simp only [J, Finset.mem_filter, collarSubinterval] at hp1 hp2
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp1.1).2.1.pos
    have h1 := Real.rpow_lt_rpow (by positivity) hp1.2.1.1 hr_pos
    have h2 := Real.rpow_le_rpow (by positivity) hp2.2.1.2 hr_pos.le
    have h3 := Real.rpow_lt_rpow (by positivity) hp2.2.1.1 hr_pos
    have h4 := Real.rpow_le_rpow (by positivity) hp1.2.1.2 hr_pos.le
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hr_pos.ne', Real.rpow_one] at h1 h2 h3 h4
    rw [← Real.rpow_natCast (p : ℝ) r, ← Real.rpow_mul hp_pos.le, mul_one_div_cancel hr_pos.ne', Real.rpow_one] at h1 h2 h3 h4
    have hm₁_pos : (0 : ℝ) < (m₁ : ℝ) := by exact_mod_cast hm₁.1
    have hm₂_pos : (0 : ℝ) < (m₂ : ℝ) := by exact_mod_cast hm₂.1
    have h12 : (n : ℝ) / ((m₁ : ℝ) + 1) < (n : ℝ) / (m₂ : ℝ) := lt_of_lt_of_le h1 h2
    have h21 : (n : ℝ) / ((m₂ : ℝ) + 1) < (n : ℝ) / (m₁ : ℝ) := lt_of_lt_of_le h3 h4
    have : m₂ < m₁ + 1 := by exact_mod_cast (by rw [div_lt_div_iff₀ (by positivity) hm₂_pos] at h12; nlinarith : (m₂ : ℝ) < (m₁ : ℝ) + 1)
    have : m₁ < m₂ + 1 := by exact_mod_cast (by rw [div_lt_div_iff₀ (by positivity) hm₁_pos] at h21; nlinarith : (m₁ : ℝ) < (m₂ : ℝ) + 1)
    omega
  have hv_on_J : ∀ m_r ∈ Finset.Icc 1 M_r, ∀ p ∈ J m_r,
      (-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1) =
        -(-1 : ℝ) ^ m_r * ∏ s ∈ Finset.Icc 1 (r - 1), (-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ) ^ s) := by
    intro m_r hm_r p hp
    have hpS := (Finset.mem_filter.mp hp).1
    have hp_pr := (Finset.mem_filter.mp hpS).2.1
    have hp_col := (Finset.mem_filter.mp hp).2
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pr.pos
    have h_v : padicValNat p (Nat.factorial n) = ∑ s ∈ Finset.Icc 1 R, n / p ^ s :=
      padicValNat_factorial_eq_sum_Icc hp_pr (h_pow_R1 p hpS)
    have h_div_mr : n / p ^ r = m_r := by
      have h1 := Real.rpow_lt_rpow (by positivity) hp_col.1.1 hr_pos
      have h2 := Real.rpow_le_rpow (by positivity) hp_col.1.2 hr_pos.le
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hr_pos.ne', Real.rpow_one] at h1 h2
      rw [← Real.rpow_natCast (p : ℝ) r, ← Real.rpow_mul hp_pos.le, mul_one_div_cancel hr_pos.ne', Real.rpow_one] at h1 h2
      have hm_pos : (0 : ℝ) < (m_r : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm_r).1
      rw [div_lt_iff₀ (by positivity)] at h1
      rw [le_div_iff₀ hm_pos] at h2
      have h_ltN : n < (m_r + 1) * p ^ r := by exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((m_r + 1 : ℕ) : ℝ) * ((p ^ r : ℕ) : ℝ))
      have h_leN : m_r * p ^ r ≤ n := by exact_mod_cast (by linarith : ((m_r * p ^ r : ℕ) : ℝ) ≤ (n : ℝ))
      have := (Nat.le_div_iff_mul_le (pow_pos hp_pr.pos r)).mpr h_leN
      have := (Nat.div_lt_iff_lt_mul (pow_pos hp_pr.pos r)).mpr h_ltN
      omega
    have h_gt_r_zero : ∀ s ∈ Finset.Icc (r + 1) R, n / p ^ s = 0 := by
      intro s hs
      have hs1 : r + 1 ≤ s := (Finset.mem_Icc.mp hs).1
      apply Nat.div_eq_of_lt
      have h_lt_n : (n : ℝ) < (p : ℝ) ^ (r + 1) := by
        have h_col_lo := hp_col.2.1
        have h_gap : (n : ℝ) ^ (1 / ((r : ℝ) + 1)) < (n : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)) := by
          rw [lt_div_iff₀ (by positivity)]
          have hpow_gt : (Real.log (n : ℝ)) ^ ((A_R : ℝ) / (r : ℝ)) ≤ (Real.log (n : ℝ)) ^ A_R := by
            rw [← Real.rpow_natCast (Real.log (n : ℝ)) A_R]
            apply Real.rpow_le_rpow_of_exponent_le (by linarith)
            exact div_le_self (by positivity) (by exact_mod_cast (by omega : 1 ≤ r))
          have h1 : (Real.log (n : ℝ)) ^ A_R < (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) := by
            have := (div_lt_iff₀ (by positivity)).mp hdiv_sm
            linarith
          have h2 : (n : ℝ) ^ (1 / ((r : ℝ) + 1)) * (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) = (n : ℝ) ^ (1 / (r : ℝ)) := by
            rw [← Real.rpow_add hn_pos]
            congr 1; field_simp [hr_pos.ne', by positivity : (r : ℝ) + 1 ≠ 0]; ring
          nlinarith [Real.rpow_pos_of_pos hn_pos (1 / ((r : ℝ) + 1))]
        have hlt_p := lt_trans h_gap h_col_lo
        have := Real.rpow_lt_rpow (by positivity) hlt_p (by positivity : (0 : ℝ) < (r : ℝ) + 1)
        rw [← Real.rpow_mul hn_pos.le, one_div_mul_cancel (by positivity : (r : ℝ) + 1 ≠ 0), Real.rpow_one,
          ← Real.rpow_natCast (p : ℝ) (r + 1)] at this
        exact this
      have h_le_s : (p : ℝ) ^ (r + 1) ≤ (p : ℝ) ^ s := pow_le_pow_right₀ (by exact_mod_cast hp_pr.one_lt.le) hs1
      exact_mod_cast lt_of_lt_of_le h_lt_n h_le_s
    have h_sum_split : ∑ s ∈ Finset.Icc 1 R, n / p ^ s =
        (∑ s ∈ Finset.Icc 1 (r - 1), n / p ^ s) + m_r := by
      have h1 : Finset.Icc 1 R = Finset.Icc 1 r ∪ Finset.Icc (r + 1) R := by
        ext s; simp only [Finset.mem_union, Finset.mem_Icc]; omega
      have h2 : Disjoint (Finset.Icc 1 r) (Finset.Icc (r + 1) R) := by
        rw [Finset.disjoint_left]; intro s hs1 hs2
        simp only [Finset.mem_Icc] at hs1 hs2; omega
      rw [h1, Finset.sum_union h2, Finset.sum_eq_zero h_gt_r_zero, add_zero]
      rw [show r = (r - 1) + 1 from by omega, Finset.sum_Icc_succ_top (by omega : 1 ≤ r), h_div_mr]
    have hv_pos : 1 ≤ padicValNat p (Nat.factorial n) := by rw [h_v, h_sum_split]; omega
    have hpow_neg : (-1 : ℝ) ^ (padicValNat p (Nat.factorial n) - 1) =
        -((-1 : ℝ) ^ padicValNat p (Nat.factorial n)) := by
      have : padicValNat p (Nat.factorial n) = (padicValNat p (Nat.factorial n) - 1) + 1 := by omega
      conv_rhs => rw [this, pow_succ]
      ring
    rw [hpow_neg, h_v, h_sum_split, pow_add, ← Finset.prod_pow_eq_pow_sum]
    have h_fl_eq : ∏ s ∈ Finset.Icc 1 (r - 1), (-1 : ℝ) ^ (n / p ^ s) =
        ∏ s ∈ Finset.Icc 1 (r - 1), (-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ) ^ s) := by
      refine Finset.prod_congr rfl (fun s _ => ?_)
      have hps_pos : (0 : ℝ) < (p : ℝ) ^ s := by positivity
      have hfl : Int.floor ((n : ℝ) / (p : ℝ) ^ s) = ((n / p ^ s : ℕ) : ℤ) := by
        rw [Int.floor_eq_iff]
        constructor
        · rw [Int.cast_natCast, le_div_iff₀ hps_pos]; exact_mod_cast Nat.div_mul_le_self n (p ^ s)
        · rw [Int.cast_natCast, div_lt_iff₀ hps_pos]
          have h_nat : n < (n / p ^ s + 1) * p ^ s := Nat.lt_div_mul_add (pow_pos hp_pr.pos s)
          exact_mod_cast (by push_cast; linarith : (n : ℝ) < ((n / p ^ s + 1 : ℕ) : ℝ) * ((p ^ s : ℕ) : ℝ))
      rw [hfl, zpow_natCast]
    rw [h_fl_eq]
    ring
  obtain ⟨c_tilde, b_tilde, h_supp, h_ctilde_b, h_btilde0, h_btilde_b, h_vaaler_pw, h_L1⟩ :=
    vaaler_parity_approx H hH_ge1
  let allH := Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)
  let oddH := allH.filter (fun h => h ≠ 0 ∧ Odd h)
  let nzH := allH.filter (· ≠ 0)
  let b_real : ℤ → ℂ := fun h => (1 / 2 : ℂ) * (b_tilde h + star (b_tilde (-h)))
  have hb_real_0 : b_real 0 = ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) := by
    dsimp only [b_real]
    rw [neg_zero, h_btilde0]
    apply Complex.ext <;> simp <;> norm_cast
  have hb_real_norm : ∀ h : ℤ, ‖b_real h‖ ≤ 3 / ((H : ℝ) + 1) := by
    intro h
    dsimp only [b_real]
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 from by norm_num]
    have h1 := h_btilde_b h
    have h2 : ‖star (b_tilde (-h))‖ ≤ 3 / ((H : ℝ) + 1) := by
      rw [norm_star]; exact (h_btilde_b (-h)).le
    linarith [norm_add_le (b_tilde h) (star (b_tilde (-h)))]
  have h_J_exp : ∀ (m_r : ℕ) (hm_r : m_r ∈ Finset.Icc 1 M_r) (A : Finset ℕ) (hA_sub : A ⊆ Finset.Icc 1 (r - 1))
      (h_fn : ℕ → ℤ) (hA_nz : ∃ s ∈ A, h_fn s ≠ 0) (hh_le : ∀ s ∈ A, |h_fn s| ≤ 2 * (H : ℤ) + 1),
      ‖∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
          eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s))‖ ≤
        4 * C₃e * (n : ℝ) ^ (-η) := by
    intro m_r hm_r A hA_sub h_fn hA_nz hh_le
    rcases eq_or_ne (J m_r) ∅ with h_emp | h_ne
    · rw [h_emp, Finset.sum_empty, norm_zero]; positivity
    · let P := max ((n : ℝ) ^ δ) (((n : ℝ) / ((m_r : ℝ) + 1)) ^ (1 / (r : ℝ)))
      have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
      have hm_pos : (0 : ℝ) < (m_r : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm_r).1
      have hP_lo : (n : ℝ) ^ δ ≤ P := le_max_left _ _
      have hP_pos : 0 < P := lt_of_lt_of_le (by positivity) hP_lo
      have hP_le_n1r : P ≤ (n : ℝ) ^ (1 / (r : ℝ)) := by
        apply max_le
        · apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
          rw [le_div_iff₀ hr_pos]
          have : (r : ℝ) ≤ 1 / δ := (Nat.le_floor_iff (by positivity)).mp hrR
          nlinarith [(div_le_iff₀ hδ0).mp this]
        · apply Real.rpow_le_rpow (by positivity) _ (by positivity)
          exact div_le_self hn_pos.le (by linarith)
      have hP_hi : P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 := by
        obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr h_ne
        have hp0_S := (Finset.mem_filter.mp hp0).1
        have hp0_col := (Finset.mem_filter.mp hp0).2
        have hp0_le_sq : (p0 : ℝ) ≤ (Nat.sqrt n : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp0_S).1).2
        have hp0_gt_lo : ((n : ℝ) / ((m_r : ℝ) + 1)) ^ (1 / (r : ℝ)) < (p0 : ℝ) := hp0_col.1.1
        have hp0_gt_d : (n : ℝ) ^ δ < (p0 : ℝ) := (Finset.mem_filter.mp hp0_S).2.2.1
        have hP_lt_p0 : P < (p0 : ℝ) := max_lt hp0_gt_d hp0_gt_lo
        linarith [hsq12]
      have hJ_pr : ∀ p ∈ J m_r, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P := by
        intro p hp
        have hpS := (Finset.mem_filter.mp hp).1
        have hp_col := (Finset.mem_filter.mp hp).2
        refine ⟨(Finset.mem_filter.mp hpS).2.1, max_lt (Finset.mem_filter.mp hpS).2.2.1 hp_col.1.1, ?_⟩
        calc (p : ℝ) ≤ ((n : ℝ) / (m_r : ℝ)) ^ (1 / (r : ℝ)) := hp_col.1.2
          _ = (((m_r : ℝ) + 1) / (m_r : ℝ)) ^ (1 / (r : ℝ)) *
                (((n : ℝ) / ((m_r : ℝ) + 1)) ^ (1 / (r : ℝ))) := by
              rw [← Real.mul_rpow (by positivity) (by positivity)]
              congr 1; field_simp [hm_pos.ne']
          _ ≤ 2 * (((n : ℝ) / ((m_r : ℝ) + 1)) ^ (1 / (r : ℝ))) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              calc (((m_r : ℝ) + 1) / (m_r : ℝ)) ^ (1 / (r : ℝ))
                  ≤ (2 : ℝ) ^ (1 / (r : ℝ)) := by
                    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
                    rw [div_le_iff₀ hm_pos]
                    have : (1 : ℝ) ≤ (m_r : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm_r).1
                    linarith
                _ ≤ 2 := by
                    calc (2 : ℝ) ^ (1 / (r : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                          Real.rpow_le_rpow_of_exponent_le (by norm_num) (div_le_self (by norm_num) (by exact_mod_cast (by omega : 1 ≤ r)))
                      _ = 2 := Real.rpow_one _
          _ ≤ 2 * P := mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
      have hA_range : ∀ s ∈ A, 1 ≤ s ∧ s ≤ R := by
        intro s hs
        have := Finset.mem_Icc.mp (hA_sub hs)
        omega
      have h_log_nδ : (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) ^ δ := by
        have h1 : (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) ^ (1 / ((r : ℝ) * ((r : ℝ) + 1))) := by
          have := (div_lt_iff₀ (by positivity)).mp hdiv_sm
          linarith
        have h2 : 1 / ((r : ℝ) * ((r : ℝ) + 1)) ≤ δ := by
          have h_1R1_d : 1 / ((R : ℝ) + 1) < δ := by
            rw [div_lt_iff₀ (by positivity)]
            have := Nat.lt_floor_add_one (1 / δ)
            nlinarith [(div_lt_iff₀ hδ0).mp this]
          have h_rr1 : 1 / ((r : ℝ) * ((r : ℝ) + 1)) ≤ 1 / ((R : ℝ) + 1) := by
            apply one_div_le_one_div_of_le (by positivity)
            have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
            have hrR' : (r : ℝ) ≤ (R : ℝ) := by exact_mod_cast hrR
            nlinarith
          linarith
        exact le_trans h1 (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) h2)
      have hPhase : ∀ s ∈ A, (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ (n : ℝ) / P ^ s := by
        intro s hs
        have hs_mem := Finset.mem_Icc.mp (hA_sub hs)
        have hPs_le : P ^ s ≤ (n : ℝ) ^ ((s : ℝ) / (r : ℝ)) := by
          calc P ^ s ≤ ((n : ℝ) ^ (1 / (r : ℝ))) ^ s := pow_le_pow_left₀ hP_pos.le hP_le_n1r s
            _ = (n : ℝ) ^ ((s : ℝ) / (r : ℝ)) := by
                rw [← Real.rpow_natCast _ s, ← Real.rpow_mul hn_pos.le]; congr 1; ring
        have h_n_div : (n : ℝ) ^ (1 - (s : ℝ) / (r : ℝ)) ≤ (n : ℝ) / P ^ s := by
          calc (n : ℝ) ^ (1 - (s : ℝ) / (r : ℝ)) = (n : ℝ) / (n : ℝ) ^ ((s : ℝ) / (r : ℝ)) := by
                rw [Real.rpow_sub hn_pos, Real.rpow_one]
            _ ≤ (n : ℝ) / P ^ s := div_le_div_of_nonneg_left hn_pos.le (by positivity) hPs_le
        have h_exp_ge : (n : ℝ) ^ δ ≤ (n : ℝ) ^ (1 - (s : ℝ) / (r : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
          have hs_le : (s : ℝ) ≤ (r : ℝ) - 1 := by exact_mod_cast (by omega : s ≤ r - 1)
          have h1 : 1 / (r : ℝ) ≤ 1 - (s : ℝ) / (r : ℝ) := by
            rw [le_sub_iff_add_le, ← add_div, div_le_one hr_pos]
            linarith
          have h_d_1r : δ ≤ 1 / (r : ℝ) := by
            rw [le_div_iff₀ hr_pos]
            have : (r : ℝ) ≤ 1 / δ := (Nat.le_floor_iff (by positivity)).mp hrR
            nlinarith [(div_le_iff₀ hδ0).mp this]
          linarith
        have h2R_le1 : (2 : ℝ) ^ (-(R : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
        calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ 1 * (Real.log (n : ℝ)) ^ A_R :=
              mul_le_mul_of_nonneg_right h2R_le1 (by positivity)
          _ = (Real.log (n : ℝ)) ^ A_R := one_mul _
          _ ≤ (n : ℝ) ^ δ := h_log_nδ
          _ ≤ (n : ℝ) ^ (1 - (s : ℝ) / (r : ℝ)) := h_exp_ge
          _ ≤ (n : ℝ) / P ^ s := h_n_div
      have hP_ge2 : 2 ≤ P := by
        have : (2 : ℝ) ≤ (Real.log (n : ℝ)) ^ A_R := by
          have := one_le_pow₀ (by linarith : (1 : ℝ) ≤ Real.log (n : ℝ)) (n := A_R - 1)
          have hA1 : 1 ≤ A_R := by omega
          have hpow : (Real.log (n : ℝ)) ^ A_R = Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (A_R - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel hA1]
          nlinarith
        linarith
      have hW_b : ∀ t ∈ Set.Icc P (2 * P), |1 / (t - 1)| ≤ 2 / P := by
        intro t ht
        have ht1 : 0 < t - 1 := by linarith [ht.1]
        rw [abs_of_pos (one_div_pos.mpr ht1)]
        exact one_div_le_div_of_le (by positivity) (by linarith [ht.1])
      have hexp_app := hexp_n P (J m_r) A h_fn (fun t => 1 / (t - 1)) (2 / P)
        hA_nz hP_lo hP_hi hJ_pr hA_range hh_le hPhase hW_b (by positivity)
      dsimp only at hexp_app
      have hT₀_ge : (n : ℝ) ^ (δ / 2) ≤ |(h_fn ((A.filter (fun s => h_fn s ≠ 0)).min' _ : ℕ) : ℝ)| * (n : ℝ) /
          P ^ ((A.filter (fun s => h_fn s ≠ 0)).min' _) := by
        set r₀ := (A.filter (fun s => h_fn s ≠ 0)).min' (by
          obtain ⟨s, hsA, hs0⟩ := hA_nz; exact ⟨s, Finset.mem_filter.mpr ⟨hsA, hs0⟩⟩)
        have hr₀_flt := Finset.min'_mem (A.filter (fun s => h_fn s ≠ 0)) _
        have hr₀_mem : r₀ ∈ A := (Finset.mem_filter.mp hr₀_flt).1
        have hr₀_ne : h_fn r₀ ≠ 0 := (Finset.mem_filter.mp hr₀_flt).2
        have hh1 : (1 : ℝ) ≤ |(h_fn r₀ : ℝ)| := by exact_mod_cast Int.one_le_abs hr₀_ne
        have hr₀_le : r₀ ≤ r - 1 := (Finset.mem_Icc.mp (hA_sub hr₀_mem)).2
        have hPr₀ : P ^ r₀ ≤ (n : ℝ) ^ ((r₀ : ℝ) / (r : ℝ)) := by
          calc P ^ r₀ ≤ ((n : ℝ) ^ (1 / (r : ℝ))) ^ r₀ := pow_le_pow_left₀ hP_pos.le hP_le_n1r r₀
            _ = (n : ℝ) ^ ((r₀ : ℝ) / (r : ℝ)) := by
                rw [← Real.rpow_natCast _ r₀, ← Real.rpow_mul hn_pos.le]; congr 1; ring
        have h_n_div : (n : ℝ) ^ δ ≤ (n : ℝ) / P ^ r₀ := by
          have h1 : 1 - (r₀ : ℝ) / (r : ℝ) ≥ 1 / (r : ℝ) := by
            have : (r₀ : ℝ) ≤ (r : ℝ) - 1 := by exact_mod_cast hr₀_le
            rw [ge_iff_le, le_sub_iff_add_le, ← add_div, div_le_one hr_pos]; linarith
          have h2 : δ ≤ 1 / (r : ℝ) := by
            rw [le_div_iff₀ hr_pos]
            have : (r : ℝ) ≤ 1 / δ := (Nat.le_floor_iff (by positivity)).mp hrR
            nlinarith [(div_le_iff₀ hδ0).mp this]
          calc (n : ℝ) ^ δ ≤ (n : ℝ) ^ (1 - (r₀ : ℝ) / (r : ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (le_trans h2 h1)
            _ = (n : ℝ) / (n : ℝ) ^ ((r₀ : ℝ) / (r : ℝ)) := by rw [Real.rpow_sub hn_pos, Real.rpow_one]
            _ ≤ (n : ℝ) / P ^ r₀ := div_le_div_of_nonneg_left hn_pos.le (by positivity) hPr₀
        have h_nδ_half : (n : ℝ) ^ (δ / 2) ≤ (n : ℝ) ^ δ :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
        calc (n : ℝ) ^ (δ / 2) ≤ (n : ℝ) ^ δ := h_nδ_half
          _ ≤ (n : ℝ) / P ^ r₀ := h_n_div
          _ = 1 * ((n : ℝ) / P ^ r₀) := (one_mul _).symm
          _ ≤ |(h_fn r₀ : ℝ)| * ((n : ℝ) / P ^ r₀) := mul_le_mul_of_nonneg_right hh1 (by positivity)
          _ = |(h_fn r₀ : ℝ)| * (n : ℝ) / P ^ r₀ := by ring
      have h_app2 := hexp_app.2 hT₀_ge
      have hP_cancel : C₃e * (2 / P) * P * (n : ℝ) ^ (-η) ≤ 4 * C₃e * (n : ℝ) ^ (-η) := by
        have hP_ne : P ≠ 0 := hP_pos.ne'
        calc C₃e * (2 / P) * P * (n : ℝ) ^ (-η) = 2 * C₃e * (n : ℝ) ^ (-η) := by field_simp [hP_ne]
          _ ≤ 4 * C₃e * (n : ℝ) ^ (-η) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              linarith [hC₃e]
      have hsum_eq : ∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) *
            eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s)) =
          ∑ p ∈ J m_r, ((1 / ((p : ℝ) - 1) * Real.log (p : ℝ) : ℝ) : ℂ) *
            eExp (∑ s ∈ A, (h_fn s : ℝ) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        congr 2; ring
      rw [hsum_eq]
      exact le_trans h_app2 hP_cancel
  let a_fn : ℕ → ℕ → ℂ := fun s p => (((-1 : ℝ) ^ Int.floor ((n : ℝ) / (p : ℝ) ^ s) : ℝ) : ℂ)
  let b_fn : ℕ → ℕ → ℂ := fun s p =>
    ∑ h ∈ oddH, c_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / 2)
  let B_fn : ℕ → ℕ → ℝ := fun s p =>
    (∑ h ∈ allH, b_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / 2)).re
  have ha_norm : ∀ s p, ‖a_fn s p‖ = 1 := fun s p => by
    dsimp only [a_fn]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_zpow, abs_neg, abs_one, one_zpow]
  have hB_pw : ∀ s p, ‖a_fn s p - b_fn s p‖ ≤ B_fn s p := fun s p => by
    dsimp only [a_fn, b_fn, B_fn]
    exact (h_vaaler_pw ((n : ℝ) / (p : ℝ) ^ s)).2
  let S_idx := Finset.Icc 1 (r - 1)
  have hS_idx_ne : S_idx.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hS_idx_card : S_idx.card ≤ R := by
    rw [Nat.card_Icc]; omega
  have h_prod_J : ∀ m_r ∈ Finset.Icc 1 M_r,
      ‖∑ p ∈ J m_r, ((Real.log (p : ℝ) / ((p : ℝ) - 1) : ℝ) : ℂ) * ∏ s ∈ S_idx, a_fn s p‖ ≤
      (∑ T ∈ S_idx.powerset.filter (·.Nonempty),
        (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, Real.log (p : ℝ) / ((p : ℝ) - 1)) +
      48 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) := by
    intro m_r hm_r
    let w_p : ℕ → ℝ := fun p => Real.log (p : ℝ) / ((p : ℝ) - 1)
    have hw_nn : ∀ p ∈ J m_r, 0 ≤ w_p p := fun p hp => by
      have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by exact_mod_cast (by omega : 1 < p)
      exact div_nonneg hlogp hp1.le
    have h_split : ‖∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ S_idx, a_fn s p‖ ≤
        ‖∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ S_idx, b_fn s p‖ +
        ∑ p ∈ J m_r, w_p p * ∑ T ∈ S_idx.powerset.filter (·.Nonempty), ∏ s ∈ T, B_fn s p := by
      have hid : ∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ S_idx, a_fn s p =
          (∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ S_idx, b_fn s p) +
          ∑ p ∈ J m_r, (w_p p : ℂ) * (∏ s ∈ S_idx, a_fn s p - ∏ s ∈ S_idx, b_fn s p) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun p _ => by ring)
      rw [hid]
      refine le_trans (norm_add_le _ _) (add_le_add le_rfl ?_)
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun p hp => ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw_nn p hp)]
      exact mul_le_mul_of_nonneg_left
        (prod_sub_prod_le_powerset _ (fun s => a_fn s p) (fun s => b_fn s p) (fun s => B_fn s p)
          (fun s _ => ha_norm s p) (fun s _ => hB_pw s p))
        (hw_nn p hp)
    have h_main_b : ‖∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ S_idx, b_fn s p‖ ≤
        6 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) := by
      have h_prod_exp : ∀ p ∈ J m_r,
          ∏ s ∈ S_idx, b_fn s p =
            ∑ g ∈ Fintype.piFinset (fun _ : S_idx => oddH),
              (∏ s : S_idx, c_tilde (g s)) *
                eExp (∑ s ∈ S_idx, (if hs : s ∈ S_idx then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
        intro p _
        dsimp only [b_fn]
        rw [← Finset.prod_coe_sort S_idx]
        rw [Fintype.prod_sum (fun (s : S_idx) (h : ℤ) => c_tilde h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ) ^ (s : ℕ)) / 2)) (fun _ => oddH)]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [Finset.prod_mul_distrib, eExp_sum]
        congr 2
        rw [← Finset.sum_coe_sort S_idx]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        simp only [s.2, ↓reduceDIte]
        ring
      rw [Finset.sum_congr rfl (fun p hp => by rw [h_prod_exp p hp, Finset.mul_sum])]
      rw [Finset.sum_comm]
      have h_each_g : ∀ g ∈ Fintype.piFinset (fun _ : S_idx => oddH),
          ‖∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s : S_idx, c_tilde (g s)) *
            eExp (∑ s ∈ S_idx, (if hs : s ∈ S_idx then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s)))‖ ≤
          (∏ s : S_idx, ‖c_tilde (g s)‖) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
        intro g hg
        have hpull : ∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s : S_idx, c_tilde (g s)) *
              eExp (∑ s ∈ S_idx, (if hs : s ∈ S_idx then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s))) =
            (∏ s : S_idx, c_tilde (g s)) * ∑ p ∈ J m_r, (w_p p : ℂ) *
              eExp (∑ s ∈ S_idx, (if hs : s ∈ S_idx then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p _ => by ring)
        rw [hpull, norm_mul, norm_prod]
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
        have hg_mem : ∀ s : S_idx, g s ∈ oddH := fun s => Fintype.mem_piFinset.mp hg s
        obtain ⟨s0, hs0⟩ := hS_idx_ne
        have hnz : ∃ s ∈ S_idx, (if hs : s ∈ S_idx then g ⟨s, hs⟩ else 0) ≠ 0 := by
          refine ⟨s0, hs0, ?_⟩
          simp only [hs0, ↓reduceDIte]
          exact (Finset.mem_filter.mp (hg_mem ⟨s0, hs0⟩)).2.1
        have hle : ∀ s ∈ S_idx, |if hs : s ∈ S_idx then g ⟨s, hs⟩ else 0| ≤ 2 * (H : ℤ) + 1 := by
          intro s hs
          simp only [hs, ↓reduceDIte]
          have := Finset.mem_Icc.mp (Finset.mem_filter.mp (hg_mem ⟨s, hs⟩)).1
          rw [abs_le]; omega
        exact h_J_exp m_r hm_r S_idx le_rfl (fun s => if hs : s ∈ S_idx then g ⟨s, hs⟩ else 0) hnz hle
      calc ‖∑ g ∈ Fintype.piFinset (fun _ : S_idx => oddH), ∑ p ∈ J m_r, _‖
          ≤ ∑ g ∈ Fintype.piFinset (fun _ : S_idx => oddH), ‖∑ p ∈ J m_r, _‖ := norm_sum_le _ _
        _ ≤ ∑ g ∈ Fintype.piFinset (fun _ : S_idx => oddH),
              (∏ s : S_idx, ‖c_tilde (g s)‖) * (4 * C₃e * (n : ℝ) ^ (-η)) :=
            Finset.sum_le_sum h_each_g
        _ = (∑ g ∈ Fintype.piFinset (fun _ : S_idx => oddH), ∏ s : S_idx, ‖c_tilde (g s)‖) *
              (4 * C₃e * (n : ℝ) ^ (-η)) := by rw [← Finset.sum_mul]
        _ = (∏ _s : S_idx, ∑ h ∈ oddH, ‖c_tilde h‖) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
            congr 1
            exact (Fintype.prod_sum (fun (_s : S_idx) (h : ℤ) => ‖c_tilde h‖) (fun _ => oddH)).symm
        _ ≤ ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ S_idx.card * (4 * C₃e * (n : ℝ) ^ (-η)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
            exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) h_L1 _
        _ ≤ (6 * (Real.log (n : ℝ)) ^ (R + 2)) ^ R * (4 * C₃e * (n : ℝ) ^ (-η)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hL1_le : (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1) ≤ 6 * (Real.log (n : ℝ)) ^ (R + 2) := by
              have h4pi : 4 / Real.pi ≤ 2 := by
                rw [div_le_iff₀ Real.pi_pos]
                linarith [Real.pi_gt_three]
              have hlog_le : Real.log (2 * (H : ℝ) + 1) + 1 ≤ 3 * (Real.log (n : ℝ)) ^ (R + 2) := by
                have h1 : Real.log (2 * (H : ℝ) + 1) ≤ 2 * (H : ℝ) := by
                  linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * (H : ℝ) + 1)]
                have h2 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) := one_le_pow₀ (by linarith)
                linarith
              nlinarith
            have h6_ge1 : (1 : ℝ) ≤ 6 * (Real.log (n : ℝ)) ^ (R + 2) := by
              have : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ (R + 2) := one_le_pow₀ (by linarith)
              linarith
            calc ((4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1)) ^ S_idx.card
                ≤ (6 * (Real.log (n : ℝ)) ^ (R + 2)) ^ S_idx.card :=
                  pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hL1_le _
              _ ≤ (6 * (Real.log (n : ℝ)) ^ (R + 2)) ^ R :=
                  pow_le_pow_right₀ h6_ge1 hS_idx_card
        _ = 6 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) := by
            rw [mul_pow, ← pow_mul]
            ring
    have h_B_err : ∑ p ∈ J m_r, w_p p * ∑ T ∈ S_idx.powerset.filter (·.Nonempty), ∏ s ∈ T, B_fn s p ≤
        (∑ T ∈ S_idx.powerset.filter (·.Nonempty),
          (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p) +
        42 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) := by
      rw [Finset.sum_congr rfl (fun p _ => Finset.mul_sum _ _ _)]
      rw [Finset.sum_comm]
      have h_each_T : ∀ T ∈ S_idx.powerset.filter (·.Nonempty),
          ∑ p ∈ J m_r, w_p p * ∏ s ∈ T, B_fn s p ≤
            (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p +
            24 ^ R * (4 * C₃e * (n : ℝ) ^ (-η)) := by
        intro T hT
        have hT_sub : T ⊆ S_idx := (Finset.mem_filter.mp hT).1
        let Z : ℕ → ℕ → ℂ := fun s p =>
          ∑ h ∈ nzH, b_real h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / 2)
        have hB_eq_C : ∀ s p, (B_fn s p : ℂ) = Z s p + ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) := by
          intro s p
          dsimp only [B_fn]
          have hrep := vaaler_B_real_rep b_tilde (2 * (H : ℤ) + 1) (by positivity) (((n : ℝ) / (p : ℝ) ^ s) / 2)
          dsimp only at hrep
          have h_arg : ∀ h : ℤ, (h : ℝ) * ((n : ℝ) / (p : ℝ) ^ s) / 2 = (h : ℝ) * (((n : ℝ) / (p : ℝ) ^ s) / 2) := by
            intro h; ring
          simp_rw [h_arg]
          rw [hrep]
          have h0_mem : (0 : ℤ) ∈ allH := by simp only [allH, Finset.mem_Icc]; omega
          rw [← Finset.add_sum_erase _ _ h0_mem]
          have h0_term : b_real 0 * eExp ((0 : ℝ) * (((n : ℝ) / (p : ℝ) ^ s) / 2)) = ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) := by
            rw [hb_real_0, zero_mul, show eExp 0 = 1 from by unfold eExp; simp, mul_one]
          have h_nz_eq : allH.erase 0 = nzH := by
            ext h; simp [nzH, allH, Finset.mem_erase, Finset.mem_filter]; tauto
          rw [h0_term, h_nz_eq, add_comm]
          rfl
        have h_re_eq : ∑ p ∈ J m_r, w_p p * ∏ s ∈ T, B_fn s p =
            (∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ T, (Z s p + ((2 / ((H : ℝ) + 1) : ℝ) : ℂ))).re := by
          rw [Complex.re_sum]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          have hprod_C : ∏ s ∈ T, (Z s p + ((2 / ((H : ℝ) + 1) : ℝ) : ℂ)) =
              ((∏ s ∈ T, B_fn s p : ℝ) : ℂ) := by
            push_cast
            exact Finset.prod_congr rfl (fun s _ => (hB_eq_C s p).symm)
          rw [hprod_C, ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [h_re_eq]
        refine le_trans (Complex.re_le_abs _) ?_
        rw [← Complex.norm_eq_abs]
        have h_prod_T : ∀ p ∈ J m_r,
            ∏ s ∈ T, (Z s p + ((2 / ((H : ℝ) + 1) : ℝ) : ℂ)) =
              ∑ U ∈ T.powerset, (∏ s ∈ U, Z s p) * ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ U).card := by
          intro p _
          rw [Finset.prod_add]
          refine Finset.sum_congr rfl (fun U _ => ?_)
          rw [Finset.prod_const]
        rw [Finset.sum_congr rfl (fun p hp => by rw [h_prod_T p hp, Finset.mul_sum])]
        rw [Finset.sum_comm]
        have hU_split : T.powerset = insert ∅ (T.powerset.filter (·.Nonempty)) := by
          ext U
          simp only [Finset.mem_insert, Finset.mem_powerset, Finset.mem_filter]
          constructor
          · intro hU
            rcases Finset.eq_empty_or_nonempty U with rfl | hne
            · left; rfl
            · right; exact ⟨hU, hne⟩
          · rintro (rfl | ⟨hU, _⟩)
            · exact Finset.empty_subset _
            · exact hU
        have hnot_emp : (∅ : Finset ℕ) ∉ T.powerset.filter (·.Nonempty) := by
          simp [Finset.not_nonempty_empty]
        rw [hU_split, Finset.sum_insert hnot_emp]
        refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
        · have h_emp_eq : ∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s ∈ (∅ : Finset ℕ), Z s p) *
                ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ ∅).card) =
              (((2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p : ℝ) : ℂ) := by
            simp only [Finset.prod_empty, one_mul, Finset.sdiff_empty]
            push_cast
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun p _ => by ring)
          rw [h_emp_eq, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg hw_nn))]
        · have h_each_U : ∀ U ∈ T.powerset.filter (·.Nonempty),
              ‖∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s ∈ U, Z s p) *
                ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ U).card)‖ ≤
              12 ^ R * (4 * C₃e * (n : ℝ) ^ (-η)) := by
            intro U hU
            have hU_sub : U ⊆ S_idx := Finset.Subset.trans (Finset.mem_filter.mp hU).1 hT_sub
            have hU_ne : U.Nonempty := (Finset.mem_filter.mp hU).2
            have hU_card : U.card ≤ R := le_trans (Finset.card_le_card hU_sub) hS_idx_card
            have hpull : ∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s ∈ U, Z s p) *
                  ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ U).card) =
                ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) ^ (T \ U).card *
                  ∑ p ∈ J m_r, (w_p p : ℂ) * ∏ s ∈ U, Z s p := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun p _ => by ring)
            rw [hpull, norm_mul, norm_pow, Complex.norm_real,
              Real.norm_of_nonneg (by positivity : 0 ≤ 2 / ((H : ℝ) + 1))]
            have h_pow_le1 : (2 / ((H : ℝ) + 1)) ^ (T \ U).card ≤ 1 := by
              apply pow_le_one₀ (by positivity)
              rw [div_le_one (by positivity)]
              have : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH_ge1
              linarith
            refine le_trans (mul_le_mul_of_nonneg_right h_pow_le1 (norm_nonneg _)) ?_
            rw [one_mul]
            have hZ_exp : ∀ p ∈ J m_r,
                ∏ s ∈ U, Z s p =
                  ∑ g ∈ Fintype.piFinset (fun _ : U => nzH),
                    (∏ s : U, b_real (g s)) *
                      eExp (∑ s ∈ U, (if hs : s ∈ U then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
              intro p _
              dsimp only [Z]
              rw [← Finset.prod_coe_sort U]
              rw [Fintype.prod_sum (fun (s : U) (h : ℤ) => b_real h * eExp ((h : ℝ) * ((n : ℝ) / (p : ℝ) ^ (s : ℕ)) / 2)) (fun _ => nzH)]
              refine Finset.sum_congr rfl (fun g _ => ?_)
              rw [Finset.prod_mul_distrib, eExp_sum]
              congr 2
              rw [← Finset.sum_coe_sort U]
              refine Finset.sum_congr rfl (fun s _ => ?_)
              simp only [s.2, ↓reduceDIte]
              ring
            rw [Finset.sum_congr rfl (fun p hp => by rw [hZ_exp p hp, Finset.mul_sum])]
            rw [Finset.sum_comm]
            have h_each_g : ∀ g ∈ Fintype.piFinset (fun _ : U => nzH),
                ‖∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s : U, b_real (g s)) *
                  eExp (∑ s ∈ U, (if hs : s ∈ U then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s)))‖ ≤
                (∏ s : U, ‖b_real (g s)‖) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
              intro g hg
              have hpull_g : ∑ p ∈ J m_r, (w_p p : ℂ) * ((∏ s : U, b_real (g s)) *
                    eExp (∑ s ∈ U, (if hs : s ∈ U then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s))) =
                  (∏ s : U, b_real (g s)) * ∑ p ∈ J m_r, (w_p p : ℂ) *
                    eExp (∑ s ∈ U, (if hs : s ∈ U then (g ⟨s, hs⟩ : ℝ) else 0) * (n : ℝ) / (2 * (p : ℝ) ^ s)) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun p _ => by ring)
              rw [hpull_g, norm_mul, norm_prod]
              apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
              have hg_mem : ∀ s : U, g s ∈ nzH := fun s => Fintype.mem_piFinset.mp hg s
              obtain ⟨s0, hs0⟩ := hU_ne
              have hnz : ∃ s ∈ U, (if hs : s ∈ U then g ⟨s, hs⟩ else 0) ≠ 0 := by
                refine ⟨s0, hs0, ?_⟩
                simp only [hs0, ↓reduceDIte]
                exact (Finset.mem_filter.mp (hg_mem ⟨s0, hs0⟩)).2
              have hle : ∀ s ∈ U, |if hs : s ∈ U then g ⟨s, hs⟩ else 0| ≤ 2 * (H : ℤ) + 1 := by
                intro s hs
                simp only [hs, ↓reduceDIte]
                have := Finset.mem_Icc.mp (Finset.mem_filter.mp (hg_mem ⟨s, hs⟩)).1
                rw [abs_le]; omega
              exact h_J_exp m_r hm_r U hU_sub (fun s => if hs : s ∈ U then g ⟨s, hs⟩ else 0) hnz hle
            have h_nz_sum_le : ∑ h ∈ nzH, ‖b_real h‖ ≤ 12 := by
              have hnz_card : (nzH.card : ℝ) ≤ 4 * (H : ℝ) + 3 := by
                have h1 : nzH.card ≤ allH.card := Finset.card_filter_le _ _
                have h2 : allH.card = 4 * H + 3 := by dsimp only [allH]; rw [Int.card_Icc]; omega
                exact_mod_cast le_trans h1 h2.le
              calc ∑ h ∈ nzH, ‖b_real h‖ ≤ ∑ _h ∈ nzH, (3 / ((H : ℝ) + 1)) :=
                    Finset.sum_le_sum (fun h _ => hb_real_norm h)
                _ = (nzH.card : ℝ) * (3 / ((H : ℝ) + 1)) := by simp [Finset.sum_const, nsmul_eq_mul]
                _ ≤ (4 * (H : ℝ) + 3) * (3 / ((H : ℝ) + 1)) :=
                    mul_le_mul_of_nonneg_right hnz_card (by positivity)
                _ ≤ 12 := by
                    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
                    linarith
            calc ‖∑ g ∈ Fintype.piFinset (fun _ : U => nzH), ∑ p ∈ J m_r, _‖
                ≤ ∑ g ∈ Fintype.piFinset (fun _ : U => nzH), ‖∑ p ∈ J m_r, _‖ := norm_sum_le _ _
              _ ≤ ∑ g ∈ Fintype.piFinset (fun _ : U => nzH),
                    (∏ s : U, ‖b_real (g s)‖) * (4 * C₃e * (n : ℝ) ^ (-η)) :=
                  Finset.sum_le_sum h_each_g
              _ = (∑ g ∈ Fintype.piFinset (fun _ : U => nzH), ∏ s : U, ‖b_real (g s)‖) *
                    (4 * C₃e * (n : ℝ) ^ (-η)) := by rw [← Finset.sum_mul]
              _ = (∏ _s : U, ∑ h ∈ nzH, ‖b_real h‖) * (4 * C₃e * (n : ℝ) ^ (-η)) := by
                  congr 1
                  exact (Fintype.prod_sum (fun (_s : U) (h : ℤ) => ‖b_real h‖) (fun _ => nzH)).symm
              _ ≤ 12 ^ U.card * (4 * C₃e * (n : ℝ) ^ (-η)) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
                  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) h_nz_sum_le _
              _ ≤ 12 ^ R * (4 * C₃e * (n : ℝ) ^ (-η)) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact pow_le_pow_right₀ (by norm_num) hU_card
          calc ‖∑ U ∈ T.powerset.filter (·.Nonempty), ∑ p ∈ J m_r, _‖
              ≤ ∑ U ∈ T.powerset.filter (·.Nonempty), ‖∑ p ∈ J m_r, _‖ := norm_sum_le _ _
            _ ≤ ∑ _U ∈ T.powerset.filter (·.Nonempty), 12 ^ R * (4 * C₃e * (n : ℝ) ^ (-η)) :=
                Finset.sum_le_sum h_each_U
            _ = ((T.powerset.filter (·.Nonempty)).card : ℝ) * (12 ^ R * (4 * C₃e * (n : ℝ) ^ (-η))) := by
                simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 2 ^ R * (12 ^ R * (4 * C₃e * (n : ℝ) ^ (-η))) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                have h1 : (T.powerset.filter (·.Nonempty)).card ≤ T.powerset.card := Finset.card_filter_le _ _
                have h2 : T.powerset.card = 2 ^ T.card := Finset.card_powerset T
                have h3 : T.card ≤ R := le_trans (Finset.card_le_card hT_sub) hS_idx_card
                have h4 : (2 : ℕ) ^ T.card ≤ 2 ^ R := Nat.pow_le_pow_right (by norm_num) h3
                exact_mod_cast le_trans h1 (by rw [h2]; exact h4)
            _ = 24 ^ R * (4 * C₃e * (n : ℝ) ^ (-η)) := by rw [← mul_pow]; norm_num
      calc ∑ T ∈ S_idx.powerset.filter (·.Nonempty), ∑ p ∈ J m_r, w_p p * ∏ s ∈ T, B_fn s p
          ≤ ∑ T ∈ S_idx.powerset.filter (·.Nonempty),
              ((2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p + 24 ^ R * (4 * C₃e * (n : ℝ) ^ (-η))) :=
            Finset.sum_le_sum h_each_T
        _ = (∑ T ∈ S_idx.powerset.filter (·.Nonempty), (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p) +
              ((S_idx.powerset.filter (·.Nonempty)).card : ℝ) * (24 ^ R * (4 * C₃e * (n : ℝ) ^ (-η))) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        _ ≤ (∑ T ∈ S_idx.powerset.filter (·.Nonempty), (2 / ((H : ℝ) + 1)) ^ T.card * ∑ p ∈ J m_r, w_p p) +
              42 ^ R * (4 * C₃e) * (Real.log (n : ℝ)) ^ (R * (R + 2)) * (n : ℝ) ^ (-η) := by
            apply add_le_add le_rfl
            have hcard_le : ((S_idx.powerset.filter (·.Nonempty)).card : ℝ) ≤ 2 ^ R := by
              have h1 : (S_idx.powerset.filter (·.Nonempty)).card ≤ S_idx.powerset.card := Finset.card_filter_le _ _
              have h2 : S_idx.powerset.card = 2 ^ S_idx.card := Finset.card_powerset S_idx
              exact_mod_cast le_trans h1 (by rw [h2]; exact Nat.pow_le_pow_right (by norm_num) hS_idx_card)
            have hlog_ge1 : 1 ≤ (Real.log (n : ℝ)) ^ (R * (R + 2)) := one_le_pow₀ (by linarith)
            calc ((S_idx.powerset.filter (·.Nonempty)).card : ℝ) * (24 ^ R * (4 * C₃e * (n : ℝ) ^ (-η)))
                ≤ 2 ^ R * (24 ^ R * (4 * C₃e * (n : ℝ) ^ (-η))) :=
                  mul_le_mul_of_nonneg_right hcard_le (by positivity)
              _ ≤ 42 ^ R * (4 * C₃e * (n : ℝ) ^ (-η)) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  rw [← mul_assoc, ← mul_pow]
                  have : (2 * 24 : ℝ) = 48 := by norm_num
                  -- Wait: 42^R vs 48^R! Let's just bound 2*24 = 48? No, 42 < 48! Wait: we want 6^R + 42^R ≤ 48^R!
                  -- Let's change 24^R in h_each_T? Wait: 2^R * 12^R = 24^R, and 2^R * 24^R = 48^R!
                  -- So 48^R in h_each_T would give 6^R + 48^R, or we can use `48^R` in h_prod_J and `54^R` in M_clean!
                  sorry
            sorry
    sorry
  sorry
