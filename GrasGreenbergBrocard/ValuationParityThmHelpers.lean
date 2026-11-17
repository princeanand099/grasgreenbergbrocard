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
        rw [show (m : ℝ) = (k : ℝ) + 1 from by exact_mod_cast hk1.symm] at this
        exact this
      have hpow_lt : A * (2 : ℝ) ^ k < (p : ℝ) := by
        have h1 : (k : ℝ) * Real.log 2 < Real.log ((p : ℝ) / A) := (lt_div_iff₀ hlog2).mp h_lt
        have h2 : (2 : ℝ) ^ k < (p : ℝ) / A := by
          rw [← Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ k),
            ← Real.exp_log (by positivity : 0 < (p : ℝ) / A)]
          apply Real.exp_lt_exp.mpr
          rwa [Real.log_pow]
        rw [mul_comm]; exact (lt_div_iff₀ (by linarith)).mp h2
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
  rw [h_eq, Finset.sum_sdiff_eq_sub hsub]
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

theorem prod_sub_prod_le_powerset (S : Finset ℕ) (a b : ℕ → ℂ) (B : ℕ → ℝ)
    (ha : ∀ s ∈ S, ‖a s‖ = 1) (hB : ∀ s ∈ S, ‖a s - b s‖ ≤ B s) :
    ‖(∏ s ∈ S, a s) - (∏ s ∈ S, b s)‖ ≤
      ∑ T ∈ S.powerset.filter (·.Nonempty), ∏ s ∈ T, B s := by
  induction S using Finset.induction_on with
  | empty => simp [Finset.sum_filter, Finset.powerset_empty]
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
      have hprod_gen : ∀ T : Finset ℕ, (∀ s ∈ T, ‖a s‖ = 1) → (∀ s ∈ T, ‖a s - b s‖ ≤ B s) →
          ‖∏ s ∈ T, b s‖ ≤ ∏ s ∈ T, (1 + B s) := by
        intro T
        induction T using Finset.induction_on with
        | empty => intro _ _; simp
        | @insert y U hy ihU =>
          intro haU hBU
          have hy1 : ‖b y‖ ≤ 1 + B y := by
            have h1 : ‖b y‖ = ‖a y - (a y - b y)‖ := by ring_nf
            rw [h1]
            calc ‖a y - (a y - b y)‖ ≤ ‖a y‖ + ‖a y - b y‖ := norm_sub_le _ _
              _ ≤ 1 + B y := by linarith [haU y (Finset.mem_insert_self _ _), hBU y (Finset.mem_insert_self _ _)]
          rw [Finset.prod_insert hy, Finset.prod_insert hy, norm_mul]
          exact mul_le_mul hy1
            (ihU (fun s hs => haU s (Finset.mem_insert_of_mem hs)) (fun s hs => hBU s (Finset.mem_insert_of_mem hs)))
            (norm_nonneg _) (le_trans (norm_nonneg _) hy1)
      exact hprod_gen S ha_S hB_S
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
      conv_lhs => rw [hsplit, Finset.sum_insert hnot, Finset.prod_empty]
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
            · rw [hax, one_mul, one_mul]; exact ih'
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
              · exact absurd hy (Finset.notMem_erase _ _)
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
      have hTS : T ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hT1).1
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
      exact hx (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1 hy)
    have hinj : ∀ U₁ ∈ S.powerset.filter (·.Nonempty), ∀ U₂ ∈ S.powerset.filter (·.Nonempty),
        insert x U₁ = insert x U₂ → U₁ = U₂ := by
      intro U₁ hU₁ U₂ hU₂ heq
      have hx1 : x ∉ U₁ := fun h => hx (Finset.mem_powerset.mp (Finset.mem_filter.mp hU₁).1 h)
      have hx2 : x ∉ U₂ := fun h => hx (Finset.mem_powerset.mp (Finset.mem_filter.mp hU₂).1 h)
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
      have hxU : x ∉ U := fun h => hx (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1 h)
      rw [Finset.prod_insert hxU]
    rw [himg]
    linarith

/-! ### Auxiliary Lemmas for Theorem 2.5 -/

theorem alt_harmonic_shifted_even (K : ℕ) (hK : 1 ≤ K) :
    ∑ r ∈ Finset.Icc 1 (2 * K), (-1 : ℝ) ^ r / ((r : ℝ) + 1) =
      ∑ k ∈ Finset.Icc 1 K, (1 / (2 * (k : ℝ) - 1) - 1 / (2 * (k : ℝ))) - 1 + 1 / (2 * (K : ℝ) + 1) := by
  induction K, hK using Nat.le_induction with
  | base =>
    rw [show 2 * 1 = 2 from rfl, Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 2), Finset.Icc_self, Finset.sum_singleton, Finset.sum_singleton]
    norm_num
  | succ m hm ih =>
    have h2m1 : 1 ≤ 2 * m + 1 := by omega
    have h2m2 : 1 ≤ 2 * m + 2 := by omega
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 from by omega]
    rw [Finset.sum_Icc_succ_top h2m2, Finset.sum_Icc_succ_top h2m1]
    rw [show 2 * m + 1 = 2 * m + 1 from rfl, ih]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hpow1 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
      rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
    have hpow2 : (-1 : ℝ) ^ ((2 * m + 1) + 1) = 1 := by
      rw [show (2 * m + 1) + 1 = 2 * (m + 1) from by omega, pow_mul, neg_one_sq, one_pow]
    rw [hpow1, hpow2]
    push_cast
    rw [show (2 : ℝ) * ((m : ℝ) + 1) - 1 = 2 * (m : ℝ) + 1 from by ring,
        show (2 : ℝ) * ((m : ℝ) + 1) = 2 * (m : ℝ) + 2 from by ring]
    field_simp
    ring

theorem alt_harmonic_shifted_bound {N : ℕ} (hN : 3 ≤ N) :
    |∑ r ∈ Finset.Icc 1 (N - 1), (-1 : ℝ) ^ r / ((r : ℝ) + 1) - (Real.log 2 - 1)| ≤
      3 / (N : ℝ) := by
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
    have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    have h_le : 1 / (2 * (K : ℝ)) + 1 / (2 * (K : ℝ) + 1) ≤ 3 / (N : ℝ) := by
      rw [hN_eq, div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hK1R]
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
    have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    have h_le : 1 / (2 * (K : ℝ)) + (1 / (2 * (K : ℝ) + 1) - 1 / (2 * (K : ℝ) + 2)) ≤ 3 / (N : ℝ) := by
      rw [hN_eq]
      have hsub : 1 / (2 * (K : ℝ) + 1) - 1 / (2 * (K : ℝ) + 2) =
          1 / ((2 * (K : ℝ) + 1) * (2 * (K : ℝ) + 2)) := by
        field_simp [(by positivity : (2 * (K : ℝ) + 1) ≠ 0), (by positivity : (2 * (K : ℝ) + 2) ≠ 0)]; ring
      rw [hsub, div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      have hquad : 0 ≤ 8 * (K : ℝ) ^ 2 - 2 * (K : ℝ) - 2 := by nlinarith [hK1R]
      have hmul : 0 ≤ (2 * (K : ℝ) + 2) * (8 * (K : ℝ) ^ 2 - 2 * (K : ℝ) - 2) := by positivity
      linarith
    linarith

theorem padicValNat_factorial_eq_sum_Icc {p n R : ℕ} (hp : p.Prime)
    (hn : n < p ^ (R + 1)) :
    padicValNat p (Nat.factorial n) = ∑ s ∈ Finset.Icc 1 R, n / p ^ s := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p n < R + 1 := by
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · by_contra h; push Not at h
      exact absurd (le_trans (Nat.pow_le_pow_right hp.pos h) (Nat.pow_log_le_self p hn0)) (not_le_of_gt hn)
  rw [padicValNat_factorial (b := R + 1) hlog, Nat.Ico_succ_right]

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
  apply Complex.ext <;> simp <;> ring

theorem eExp_add (x y : ℝ) : eExp x * eExp y = eExp (x + y) := by
  unfold eExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eExp_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) :
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
    intro z; apply Complex.ext <;> simp <;> ring
  rw [hre, star_sum]
  have h_bij : ∑ h ∈ allK, star (b_tilde h * eExp ((h : ℝ) * t)) =
      ∑ h ∈ allK, star (b_tilde (-h)) * eExp ((h : ℝ) * t) := by
    refine Finset.sum_bij (fun h _ => -h) ?_ ?_ ?_ ?_
    · intro h hh; simp only [allK, Finset.mem_Icc] at hh ⊢; omega
    · intro h1 _ h2 _ heq; omega
    · intro h hh; refine ⟨-h, ?_, by omega⟩
      simp only [allK, Finset.mem_Icc] at hh ⊢; omega
    · intro h _
      rw [star_mul, star_eExp, mul_comm]
      congr 1
      · rw [neg_neg]
      · congr 1; push_cast; ring
  rw [h_bij, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  dsimp only [b_real]
  ring


end GrasGreenbergBrocard
