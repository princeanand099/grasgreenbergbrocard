import GrasGreenbergBrocard.Prop6_1FourGCD
import GrasGreenbergBrocard.ValuationParityThmHelpers

open scoped BigOperators
open Real Finset Filter

namespace GrasGreenbergBrocard

set_option maxHeartbeats 8000000

lemma val_factorial_le_two_div {n p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    (padicValNat p (Nat.factorial n) : ℝ) ≤ 2 * (n : ℝ) / (p : ℝ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : padicValNat p (Nat.factorial n) * (p - 1) ≤ n := by
    rw [mul_comm]
    exact le_trans (sub_one_mul_padicValNat_factorial (p := p) n).le (Nat.sub_le n _)
  have h1r : (padicValNat p (Nat.factorial n) : ℝ) * ((p : ℝ) - 1) ≤ (n : ℝ) := by
    have h1n : (padicValNat p (Nat.factorial n) : ℝ) * ((p - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    rwa [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at h1n
  have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hv : (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) :=
    (le_div_iff₀ (by linarith)).mpr h1r
  have hp_half : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
  calc (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := hv
    _ ≤ (n : ℝ) / ((p : ℝ) / 2) := by gcongr
    _ = 2 * (n : ℝ) / (p : ℝ) := by ring

lemma val_factorial_sub_div_abs_le {n p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    |(padicValNat p (Nat.factorial n) : ℝ) - (n : ℝ) / (p : ℝ)| ≤
      2 * (n : ℝ) / (p : ℝ) ^ 2 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [abs_le]
  constructor
  · have hge : n / p ≤ padicValNat p (Nat.factorial n) := by
      have hleg := padicValNat_factorial (p := p) (n := n) (b := Nat.log p n + 1) (Nat.lt_succ_self _)
      rw [hleg]
      rcases Nat.eq_zero_or_pos (Nat.log p n) with h0 | hpos
      · have hlt : n < p := by
          by_contra hge'; rw [not_lt] at hge'
          exact absurd (Nat.log_pos hp.one_lt hge') (by rw [h0]; exact lt_irrefl 0)
        rw [Nat.div_eq_of_lt hlt]; exact Nat.zero_le _
      · have hs := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _)
          (Finset.mem_Ico.mpr ⟨le_refl 1, (Nat.add_lt_add_right hpos 1 : 1 < Nat.log p n + 1)⟩)
        rwa [pow_one] at hs
    have hdiv_lt : (n : ℝ) / (p : ℝ) - 1 < ((n / p : ℕ) : ℝ) := by
      have hlt : n < (n / p + 1) * p := by rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hp.pos
      have hltr : (n : ℝ) < (((n / p : ℕ) : ℝ) + 1) * (p : ℝ) := by exact_mod_cast hlt
      have hdiv : (n : ℝ) / (p : ℝ) < ((n / p : ℕ) : ℝ) + 1 := (div_lt_iff₀ hp_pos).mpr hltr
      linarith
    have hger : ((n / p : ℕ) : ℝ) ≤ (padicValNat p (Nat.factorial n) : ℝ) := by exact_mod_cast hge
    have hnn : 0 ≤ 2 * (n : ℝ) / (p : ℝ) ^ 2 := by positivity
    linarith
  · have h1 : padicValNat p (Nat.factorial n) * (p - 1) ≤ n := by
      rw [mul_comm]
      exact le_trans (sub_one_mul_padicValNat_factorial (p := p) n).le (Nat.sub_le n _)
    have h1r : (padicValNat p (Nat.factorial n) : ℝ) * ((p : ℝ) - 1) ≤ (n : ℝ) := by
      have h1n : (padicValNat p (Nat.factorial n) : ℝ) * ((p - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      rwa [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at h1n
    have hv : (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) :=
      (le_div_iff₀ hp1_pos).mpr h1r
    have hdiff : (n : ℝ) / ((p : ℝ) - 1) - (n : ℝ) / (p : ℝ) = (n : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp [hp_pos.ne', hp1_pos.ne']; ring
    have hle : (n : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 * (n : ℝ) / (p : ℝ) ^ 2 := by
      have hhalf : (p : ℝ) ^ 2 / 2 ≤ (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
      calc (n : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ (n : ℝ) / ((p : ℝ) ^ 2 / 2) := by gcongr
        _ = 2 * (n : ℝ) / (p : ℝ) ^ 2 := by ring
    linarith

private lemma norm_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f g : ι → ℂ) (M : ℝ) (hM : 1 ≤ M)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ 1) (hg : ∀ i ∈ S, ‖g i‖ ≤ M) :
    ‖∏ i ∈ S, f i - ∏ i ∈ S, g i‖ ≤ M ^ S.card * ∑ i ∈ S, ‖f i - g i‖ := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have hfa : ‖f a‖ ≤ 1 := hf a (Finset.mem_insert_self a s)
    have hga : ‖g a‖ ≤ M := hg a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, ‖f i‖ ≤ 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, ‖g i‖ ≤ M := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hprod_f : ‖∏ i ∈ s, f i‖ ≤ 1 := by
      rw [norm_prod]
      calc ∏ i ∈ s, ‖f i‖ ≤ ∏ _i ∈ s, (1 : ℝ) := by gcongr with i hi; exact hfs i hi
        _ = 1 := by simp
    have hid : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        (f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by ring
    rw [hid]
    have hih := ih hfs hgs
    have hM_pow : 1 ≤ M ^ (s.card + 1) := one_le_pow₀ hM
    calc ‖(f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)‖
        ≤ ‖(f a - g a) * ∏ i ∈ s, f i‖ + ‖g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)‖ := norm_add_le _ _
      _ = ‖f a - g a‖ * ‖∏ i ∈ s, f i‖ + ‖g a‖ * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖f a - g a‖ * 1 + M * (M ^ s.card * ∑ i ∈ s, ‖f i - g i‖) := by
          gcongr
      _ ≤ M ^ (s.card + 1) * ‖f a - g a‖ + M ^ (s.card + 1) * ∑ i ∈ s, ‖f i - g i‖ := by
          rw [mul_one, ← mul_assoc, ← pow_succ']
          gcongr
          nlinarith [norm_nonneg (f a - g a)]
      _ = M ^ (s.card + 1) * (‖f a - g a‖ + ∑ i ∈ s, ‖f i - g i‖) := by ring

private def removeOneIoc (c d : ℝ) (iv : ℝ × ℝ) : List (ℝ × ℝ) :=
  [(iv.1, min iv.2 c), (max iv.1 d, iv.2)]

private def removeIocs : List (ℝ × ℝ) → List (ℝ × ℝ) → List (ℝ × ℝ)
  | [], cur => cur
  | cd :: rest, cur => removeIocs rest (cur.flatMap (removeOneIoc cd.1 cd.2))

private lemma removeIocs_length (ex cur : List (ℝ × ℝ)) :
    (removeIocs ex cur).length = 2 ^ ex.length * cur.length := by
  induction ex generalizing cur with
  | nil => simp [removeIocs]
  | cons cd rest ih =>
    simp only [removeIocs, List.length_cons, ih]
    have hlen : (cur.flatMap (removeOneIoc cd.1 cd.2)).length = 2 * cur.length := by
      induction cur with
      | nil => simp
      | cons x xs ihx => simp [removeOneIoc, ihx]; omega
    rw [hlen, pow_succ]; ring

private lemma removeIocs_props (ex cur : List (ℝ × ℝ))
    (hex : ∀ cd ∈ ex, cd.1 ≤ cd.2)
    (hpw : cur.Pairwise (fun u v => Disjoint (Set.Ioc u.1 u.2) (Set.Ioc v.1 v.2))) :
    let L := removeIocs ex cur
    L.Pairwise (fun u v => Disjoint (Set.Ioc u.1 u.2) (Set.Ioc v.1 v.2)) ∧
    (∀ u ∈ L, ∃ v ∈ cur, Set.Ioc u.1 u.2 ⊆ Set.Ioc v.1 v.2) ∧
    (∀ u ∈ L, ∀ cd ∈ ex, Disjoint (Set.Ioc u.1 u.2) (Set.Ioc cd.1 cd.2)) ∧
    (∀ x : ℝ, (∃ v ∈ cur, x ∈ Set.Ioc v.1 v.2) → (∀ cd ∈ ex, x ∉ Set.Ioc cd.1 cd.2) →
      ∃ u ∈ L, x ∈ Set.Ioc u.1 u.2) := by
  induction ex generalizing cur with
  | nil =>
    refine ⟨hpw, fun u hu => ⟨u, hu, subset_rfl⟩, fun _ _ _ h => by simp at h, fun x hx _ => hx⟩
  | cons cd rest ih =>
    have hcd : cd.1 ≤ cd.2 := hex cd (by simp)
    have hrest : ∀ e ∈ rest, e.1 ≤ e.2 := fun e he => hex e (by simp [he])
    let cur' := cur.flatMap (removeOneIoc cd.1 cd.2)
    have hsub1 : ∀ u ∈ cur', ∃ v ∈ cur, Set.Ioc u.1 u.2 ⊆ Set.Ioc v.1 v.2 := by
      intro u hu
      rw [List.mem_flatMap] at hu
      obtain ⟨v, hv, huv⟩ := hu
      refine ⟨v, hv, ?_⟩
      simp only [removeOneIoc, List.mem_cons, List.not_mem_nil, or_false] at huv
      rcases huv with rfl | rfl
      · intro x hx; exact ⟨hx.1, le_trans hx.2 (min_le_left _ _)⟩
      · intro x hx; exact ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩
    have hdisj1 : ∀ u ∈ cur', Disjoint (Set.Ioc u.1 u.2) (Set.Ioc cd.1 cd.2) := by
      intro u hu
      rw [List.mem_flatMap] at hu
      obtain ⟨v, _, huv⟩ := hu
      simp only [removeOneIoc, List.mem_cons, List.not_mem_nil, or_false] at huv
      rw [Set.disjoint_left]
      rcases huv with rfl | rfl
      · intro x hx1 hx2; linarith [le_trans hx1.2 (min_le_right _ _), hx2.1]
      · intro x hx1 hx2; linarith [lt_of_le_of_lt (le_max_right _ _) hx1.1, hx2.2]
    have hpw1 : cur'.Pairwise (fun u v => Disjoint (Set.Ioc u.1 u.2) (Set.Ioc v.1 v.2)) := by
      clear hsub1 hdisj1
      dsimp only [cur']
      induction cur with
      | nil => simp
      | cons a as iha =>
        rw [List.pairwise_cons] at hpw
        simp only [List.flatMap_cons, removeOneIoc, List.cons_append, List.nil_append, List.pairwise_cons]
        refine ⟨?_, ?_, iha hpw.2⟩
        · intro u hu
          simp only [List.mem_cons] at hu
          rcases hu with rfl | hu
          · rw [Set.disjoint_left]; intro x hx1 hx2
            linarith [le_trans hx1.2 (min_le_right _ _), lt_of_le_of_lt (le_max_right _ _) hx2.1]
          · rw [List.mem_flatMap] at hu
            obtain ⟨b, hb, hub⟩ := hu
            have hda := hpw.1 b hb
            refine Disjoint.mono ?_ ?_ hda
            · intro x hx; exact ⟨hx.1, le_trans hx.2 (min_le_left _ _)⟩
            · simp only [removeOneIoc, List.mem_cons, List.not_mem_nil, or_false] at hub
              rcases hub with rfl | rfl
              · intro x hx; exact ⟨hx.1, le_trans hx.2 (min_le_left _ _)⟩
              · intro x hx; exact ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩
        · intro u hu
          rw [List.mem_flatMap] at hu
          obtain ⟨b, hb, hub⟩ := hu
          have hda := hpw.1 b hb
          refine Disjoint.mono ?_ ?_ hda
          · intro x hx; exact ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩
          · simp only [removeOneIoc, List.mem_cons, List.not_mem_nil, or_false] at hub
            rcases hub with rfl | rfl
            · intro x hx; exact ⟨hx.1, le_trans hx.2 (min_le_left _ _)⟩
            · intro x hx; exact ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, hx.2⟩
    obtain ⟨hpw_out, hsub_out, hdisj_out, hcov_out⟩ := ih cur' hrest hpw1
    refine ⟨hpw_out, ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨w, hw, huw⟩ := hsub_out u hu
      obtain ⟨v, hv, hwv⟩ := hsub1 w hw
      exact ⟨v, hv, Set.Subset.trans huw hwv⟩
    · intro u hu e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · obtain ⟨w, hw, huw⟩ := hsub_out u hu
        exact Disjoint.mono_left huw (hdisj1 w hw)
      · exact hdisj_out u hu e he
    · intro x ⟨v, hv, hxv⟩ hnot
      have hnot_cd : x ∉ Set.Ioc cd.1 cd.2 := hnot cd (by simp)
      have hmem_cur' : ∃ w ∈ cur', x ∈ Set.Ioc w.1 w.2 := by
        by_cases hxc : x ≤ cd.1
        · refine ⟨(v.1, min v.2 cd.1), List.mem_flatMap.mpr ⟨v, hv, by simp [removeOneIoc]⟩,
            ⟨hxv.1, le_min hxv.2 hxc⟩⟩
        · push_neg at hxc
          have hxd : cd.2 < x := by
            by_contra hle; push_neg at hle
            exact hnot_cd ⟨hxc, hle⟩
          refine ⟨(max v.1 cd.2, v.2), List.mem_flatMap.mpr ⟨v, hv, by simp [removeOneIoc]⟩,
            ⟨max_lt hxv.1 hxd, hxv.2⟩⟩
      exact hcov_out x hmem_cur' (fun e he => hnot e (by simp [he]))

private lemma disjoint_Ioc_cases {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hdisj : Disjoint (Set.Ioc a b) (Set.Ioc c d)) : b ≤ c ∨ d ≤ a := by
  by_contra h
  push_neg at h
  have hlt : max a c < min b d := max_lt (lt_min hab h.2) (lt_min h.1 hcd)
  let x := (max a c + min b d) / 2
  have hx_gt : max a c < x := by dsimp [x]; linarith
  have hx_le : x ≤ min b d := by dsimp [x]; linarith
  have hx1 : x ∈ Set.Ioc a b := ⟨lt_of_le_of_lt (le_max_left a c) hx_gt, le_trans hx_le (min_le_left b d)⟩
  have hx2 : x ∈ Set.Ioc c d := ⟨lt_of_le_of_lt (le_max_right a c) hx_gt, le_trans hx_le (min_le_right b d)⟩
  exact Set.disjoint_left.mp hdisj hx1 hx2

private lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℝ}
    (hf : ∀ x ∈ s ∪ t, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ (∑ x ∈ s, f x) + (∑ x ∈ t, f x) := by
  have h1 := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have hnn : 0 ≤ ∑ x ∈ s ∩ t, f x :=
    Finset.sum_nonneg fun x hx => hf x (Finset.mem_union_left _ (Finset.mem_inter.mp hx).1)
  linarith

private lemma sum_biUnion_le_of_nonneg {ι α : Type*} [DecidableEq α] {s : Finset ι} {t : ι → Finset α}
    {f : α → ℝ} (hf : ∀ x ∈ s.biUnion t, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hnn_u : ∀ x ∈ t a ∪ s.biUnion t, 0 ≤ f x := fun x hx =>
      hf x (by rwa [Finset.biUnion_insert])
    have h1 := sum_union_le_of_nonneg hnn_u
    have h2 := ih (fun x hx => hnn_u x (Finset.mem_union_right _ hx))
    linarith

private lemma vaaler_btilde_dyadic_sum_bound_inv
    (H : ℕ) (hH : 1 ≤ H) (b_tilde : ℤ → ℂ)
    (h_btilde0 : b_tilde 0 = (2 / ((H : ℝ) + 1) : ℂ))
    (h_btilde_b : ∀ h : ℤ, ‖b_tilde h‖ < 3 / ((H : ℝ) + 1))
    (n₁ m j : ℕ) (P : ℝ) (hP_pos : 0 < P) (hP_ge1 : 1 ≤ 2 * P) (I : Finset ℕ)
    (hI : ∀ p ∈ I, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P)
    (C_exp : ℝ) (hC_exp : 0 ≤ C_exp) (R_exp : ℕ)
    (hExp : ∀ (h : ℤ), h ≠ 0 → |h| ≤ 2 * (H : ℤ) + 1 →
      ‖∑ p ∈ I, ((1 / (p : ℝ)) * Real.log (p : ℝ) : ℂ) * eExp ((h : ℝ) * (m : ℝ) / (2 * (p : ℝ) ^ j))‖ ≤
        C_exp * (Real.log (n₁ : ℝ)) ^ (-((R_exp : ℝ) + 2))) :
    ∑ p ∈ I, (Real.log (p : ℝ) / (p : ℝ)) *
      (b_tilde 0 + ∑ h ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
        b_tilde h * eExp ((h : ℝ) * ((m : ℝ) / (p : ℝ) ^ j) / 2)).re ≤
      (4 * Real.log (2 * P)) / ((H : ℝ) + 1) +
        12 * C_exp * (Real.log (n₁ : ℝ)) ^ (-((R_exp : ℝ) + 2)) := by
  have hI_card : (I.card : ℝ) ≤ 2 * P := by
    have hsub : I ⊆ Finset.Icc 1 (Nat.floor (2 * P)) := fun p hp =>
      Finset.mem_Icc.mpr ⟨(hI p hp).1.pos, Nat.le_floor (hI p hp).2.2⟩
    have hcard : I.card ≤ Nat.floor (2 * P) :=
      le_trans (Finset.card_le_card hsub) (by simp)
    exact le_trans (by exact_mod_cast hcard) (Nat.floor_le (by positivity))
  have hsum_main : ∑ p ∈ I, (Real.log (p : ℝ) / (p : ℝ)) * (b_tilde 0).re ≤
      (4 * Real.log (2 * P)) / ((H : ℝ) + 1) := by
    rw [h_btilde0, show (2 / ((H : ℝ) + 1) : ℂ) = ((2 / ((H : ℝ) + 1) : ℝ) : ℂ) by push_cast; rfl,
      Complex.ofReal_re]
    have hterm : ∀ p ∈ I, (Real.log (p : ℝ) / (p : ℝ)) * (2 / ((H : ℝ) + 1)) ≤
        (Real.log (2 * P) / P) * (2 / ((H : ℝ) + 1)) := by
      intro p hp
      have hp_mem := hI p hp
      have h1 : Real.log (p : ℝ) ≤ Real.log (2 * P) := Real.log_le_log (by exact_mod_cast hp_mem.1.pos) hp_mem.2.2
      have h2 : Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (2 * P) / P :=
        div_le_div₀ (Real.log_nonneg hP_ge1) h1 hP_pos hp_mem.2.1.le
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hlog2P : 0 ≤ Real.log (2 * P) := Real.log_nonneg hP_ge1
    calc (I.card : ℝ) * ((Real.log (2 * P) / P) * (2 / ((H : ℝ) + 1)))
        ≤ (2 * P) * ((Real.log (2 * P) / P) * (2 / ((H : ℝ) + 1))) := by gcongr
      _ = (4 * Real.log (2 * P)) / ((H : ℝ) + 1) := by field_simp [hP_pos.ne']; ring
  let S_h := (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0)
  have hsum_err : ∑ p ∈ I, (Real.log (p : ℝ) / (p : ℝ)) *
      (∑ h ∈ S_h, b_tilde h * eExp ((h : ℝ) * ((m : ℝ) / (p : ℝ) ^ j) / 2)).re ≤
      12 * C_exp * (Real.log (n₁ : ℝ)) ^ (-((R_exp : ℝ) + 2)) := by
    have hre_eq : ∑ p ∈ I, (Real.log (p : ℝ) / (p : ℝ)) *
        (∑ h ∈ S_h, b_tilde h * eExp ((h : ℝ) * ((m : ℝ) / (p : ℝ) ^ j) / 2)).re =
        (∑ h ∈ S_h, b_tilde h *
          ∑ p ∈ I, ((1 / (p : ℝ)) * Real.log (p : ℝ) : ℂ) * eExp ((h : ℝ) * (m : ℝ) / (2 * (p : ℝ) ^ j))).re := by
      calc ∑ p ∈ I, (Real.log (p : ℝ) / (p : ℝ)) *
            (∑ h ∈ S_h, b_tilde h * eExp ((h : ℝ) * ((m : ℝ) / (p : ℝ) ^ j) / 2)).re
          = ∑ p ∈ I, ∑ h ∈ S_h, (Real.log (p : ℝ) / (p : ℝ)) *
              (b_tilde h * eExp ((h : ℝ) * ((m : ℝ) / (p : ℝ) ^ j) / 2)).re := by
            apply Finset.sum_congr rfl; intro p _; rw [Complex.re_sum, Finset.mul_sum]
        _ = ∑ h ∈ S_h, ∑ p ∈ I, (Real.log (p : ℝ) / (p : ℝ)) *
              (b_tilde h * eExp ((h : ℝ) * ((m : ℝ) / (p : ℝ) ^ j) / 2)).re := Finset.sum_comm
        _ = (∑ h ∈ S_h, b_tilde h *
              ∑ p ∈ I, ((1 / (p : ℝ)) * Real.log (p : ℝ) : ℂ) * eExp ((h : ℝ) * (m : ℝ) / (2 * (p : ℝ) ^ j))).re := by
            rw [Complex.re_sum]
            apply Finset.sum_congr rfl; intro h _
            rw [Finset.mul_sum, Complex.re_sum]
            apply Finset.sum_congr rfl; intro p _
            have hdiv : (h : ℝ) * ((m : ℝ) / (p : ℝ) ^ j) / 2 = (h : ℝ) * (m : ℝ) / (2 * (p : ℝ) ^ j) := by ring
            rw [hdiv, ← Complex.re_ofReal_mul]
            congr 1
            push_cast; ring
    rw [hre_eq]
    calc (∑ h ∈ S_h, b_tilde h * _).re
        ≤ ‖∑ h ∈ S_h, b_tilde h * _‖ := (Complex.abs_re_le_norm _).trans' (le_abs_self _)
      _ ≤ ∑ h ∈ S_h, ‖b_tilde h * _‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ S_h, (3 / ((H : ℝ) + 1)) * (C_exp * (Real.log (n₁ : ℝ)) ^ (-((R_exp : ℝ) + 2))) := by
          apply Finset.sum_le_sum; intro h hh
          rw [norm_mul]
          have hmem := Finset.mem_filter.mp hh
          have habs : |h| ≤ 2 * (H : ℤ) + 1 := abs_le.mpr (Finset.mem_Icc.mp hmem.1)
          exact mul_le_mul (h_btilde_b h).le (hExp h hmem.2 habs) (norm_nonneg _) (by positivity)
      _ = (S_h.card : ℝ) * ((3 / ((H : ℝ) + 1)) * (C_exp * (Real.log (n₁ : ℝ)) ^ (-((R_exp : ℝ) + 2)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 * ((H : ℝ) + 1)) * ((3 / ((H : ℝ) + 1)) * (C_exp * (Real.log (n₁ : ℝ)) ^ (-((R_exp : ℝ) + 2)))) := by
          have hcard_le : (S_h.card : ℝ) ≤ 4 * ((H : ℝ) + 1) := by
            have h1 : S_h.card ≤ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).card := Finset.card_filter_le _ _
            have h2 : (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).card = 4 * H + 3 := by rw [Int.card_Icc]; omega
            have h1r : (S_h.card : ℝ) ≤ 4 * (H : ℝ) + 3 := by exact_mod_cast le_trans h1 h2.le
            linarith
          gcongr
      _ = 12 * C_exp * (Real.log (n₁ : ℝ)) ^ (-((R_exp : ℝ) + 2)) := by
          have hH0 : (H : ℝ) + 1 ≠ 0 := by positivity
          field_simp [hH0]; ring
  have hsplit : ∑ p ∈ I, (Real.log (p : ℝ) / (p : ℝ)) *
      (b_tilde 0 + ∑ h ∈ S_h, b_tilde h * eExp ((h : ℝ) * ((m : ℝ) / (p : ℝ) ^ j) / 2)).re =
      (∑ p ∈ I, (Real.log (p : ℝ) / (p : ℝ)) * (b_tilde 0).re) +
      (∑ p ∈ I, (Real.log (p : ℝ) / (p : ℝ)) *
        (∑ h ∈ S_h, b_tilde h * eExp ((h : ℝ) * ((m : ℝ) / (p : ℝ) ^ j) / 2)).re) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro p _
    rw [Complex.add_re]; ring
  rw [hsplit]
  exact add_le_add hsum_main hsum_err

private lemma lem63_padicValNat_factorial_eq_sum_Icc {p n r : ℕ} (hp : p.Prime) (hlt : n < p ^ (r + 1)) :
    padicValNat p (Nat.factorial n) = ∑ j ∈ Finset.Icc 1 r, n / p ^ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [padicValNat_factorial (Nat.log_lt_of_lt_pow hn.ne' hlt)]
    congr 1

private lemma prod_sum_piFinset {α β γ : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    [CommSemiring γ] (s : α → Finset β) (f : α → β → γ) :
    ∏ a : α, ∑ b ∈ s a, f a b = ∑ g ∈ Fintype.piFinset s, ∏ a : α, f a (g a) := by
  have h1 : (∏ a : α, ∑ b ∈ s a, f a b) = ∏ a : α, ∑ b : s a, f a b.1 :=
    Finset.prod_congr rfl fun a _ => (Finset.sum_coe_sort (s a) (f a)).symm
  rw [h1, Fintype.prod_sum]
  refine Finset.sum_bij (fun (g : ∀ a, s a) _ => fun a => (g a).1) ?_ ?_ ?_ ?_
  · intro g _; exact Fintype.mem_piFinset.mpr fun a => (g a).2
  · intro g₁ _ g₂ _ h
    funext a; exact Subtype.ext (congrFun h a)
  · intro g hg
    exact ⟨fun a => ⟨g a, Fintype.mem_piFinset.mp hg a⟩, Finset.mem_univ _, rfl⟩
  · intro _ _; rfl

/-- **Honest Oscillatory Correlation Bound for Lemma 6.3**:
Uses ONLY the tightened `prime_exp_sum_bounds_general_phase` with:
- smooth monotone weight `w(t) = 1 / t` (`AntitoneOn` on `[P, 2P]`),
- exact prime subintervals (`IsPrimeSubinterval P I_k`),
- excised thin power collars and resonance collars (total Mertens weight `O(n₁ log log n₁)`),
- genuine multi-digit Vaaler phase `F(t) = ∑_{j=1}^r ((h₁ j + h₂ j) n₁ + h₂ j h) / (2 t^j)`. -/
theorem lem_6_3_osc_bound_honest
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (ε : ℝ) (hε : 0 < ε) :
    ∃ N_osc : ℕ, 1000 ≤ N_osc ∧
    ∀ n₁ n₂ : ℕ, N_osc ≤ n₁ → n₁ < n₂ →
      let R := Nat.floor (1 / δ)
      let A_R := 6 * R + 30
      let h := n₂ - n₁
      let y₁ := (h : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2)
      let I_osc := ((Finset.Icc 3 n₁).filter Nat.Prime).filter (fun p : ℕ => (n₁ : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ≤ y₁)
      ((h : ℝ) ≤ (n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 4)) →
      ((n₁ : ℝ) ^ δ < (h : ℝ)) →
      ((n₁ : ℝ) ^ δ < y₁) →
      |∑ p ∈ I_osc,
        ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
          ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ))| ≤
        (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
  let R := Nat.floor (1 / δ)
  let A_R := 6 * R + 30
  let Mmax : ℝ := ∏ k ∈ Finset.range (5 * R + 2), ((R + k : ℕ) : ℝ)
  let c₁_low : ℝ := (1 / 4 : ℝ) * (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ))
  have hR_ge4 : 4 ≤ R := Nat.le_floor (by rw [Nat.cast_ofNat, le_div_iff₀ hδ0]; linarith)
  have hMmax_pos : 0 < Mmax := by
    unfold Mmax
    exact Finset.prod_pos (fun k _ => by exact_mod_cast (by omega : 0 < R + k))
  have hc₁_pos : 0 < c₁_low := mul_pos (by norm_num) (zpow_pos (by norm_num) _)
  obtain ⟨C₂, hC₂_pos, hGenExp⟩ := prime_exp_sum_bounds_general_phase δ hδ0 (by linarith)
  obtain ⟨C_mert0, hC_mert0_pos, hMert⟩ := Mertens_div_p_band_le
  let C_mert : ℝ := C_mert0 + 1
  have hC_mert_pos : 0 < C_mert := by dsimp [C_mert]; linarith
  -- Asymptotic thresholds
  have hlog_inf : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_inv_delta : Tendsto (fun n : ℕ => 2 * C_mert * (Real.log (n : ℝ) + 1) / (n : ℝ) ^ δ) atTop (nhds 0) := by
    have h1 := log_pow_div_rpow_tendsto_zero 1 hδ0
    have h0 := log_pow_div_rpow_tendsto_zero 0 hδ0
    have heq : (fun n : ℕ => 2 * C_mert * (Real.log (n : ℝ) + 1) / (n : ℝ) ^ δ) =
        fun n : ℕ => 2 * C_mert * ((Real.log (n : ℝ)) ^ 1 / (n : ℝ) ^ δ + (Real.log (n : ℝ)) ^ 0 / (n : ℝ) ^ δ) := by
      ext n; rw [pow_one, pow_zero]; ring
    rw [heq]; simpa using (h1.add h0).const_mul (2 * C_mert)
  have h_loglog : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
    exact h1.comp hlog_inf
  have h_clean_tail : Tendsto (fun n : ℕ =>
      ((R : ℝ) * (2 : ℝ) ^ R * (Real.log (n : ℝ) / Real.log 2 + 2) *
        (((4 / Real.pi) * (((R : ℝ) + 4) * Real.log (Real.log (n : ℝ)) + 4)) ^ (2 * R) *
          (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂)))) / (Real.log (n : ℝ)) ^ (R + 2)) atTop (nhds 0) := by
    -- Numerator is O((log n) * (log log n)^{2R}), denominator is (log n)^{R+2}, ratio ≤ O((log log n)^{2R} / (log n)^{R+1}) → 0
    have hbase : Tendsto (fun x : ℝ => (Real.log x) ^ (2 * R) / x ^ (R + 1)) atTop (nhds 0) := by
      have h1 : Tendsto (fun x : ℝ => (Real.log x) ^ (2 * R) / x ^ (1 : ℝ)) atTop (nhds 0) := by
        have ht : Tendsto (fun x : ℝ => (Real.log x) ^ (2 * R) / x) atTop (nhds 0) := by
          simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 (2 * R) (by norm_num)
        simpa only [Real.rpow_one] using ht
      have hev : ∀ᶠ x : ℝ in atTop, 0 ≤ (Real.log x) ^ (2 * R) / x ^ (R + 1) ∧
          (Real.log x) ^ (2 * R) / x ^ (R + 1) ≤ (Real.log x) ^ (2 * R) / x ^ (1 : ℝ) := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx
        constructor
        · positivity
        · rw [Real.rpow_one]
          exact div_le_div_of_nonneg_left (pow_nonneg hlog_nn _) (by linarith)
            (le_trans (by simp) (pow_le_pow_right₀ hx (by omega : 1 ≤ R + 1)))
      exact squeeze_zero' (hev.mono fun _ h => h.1) (hev.mono fun _ h => h.2) h1
    have hcomp := hbase.comp hlog_inf
    let K_big : ℝ := (R : ℝ) * (2 : ℝ) ^ R * (1 / Real.log 2 + 2) *
      ((4 / Real.pi) * ((R : ℝ) + 8)) ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂))
    have hev_dom : ∀ᶠ n : ℕ in atTop,
        0 ≤ ((R : ℝ) * (2 : ℝ) ^ R * (Real.log (n : ℝ) / Real.log 2 + 2) *
          (((4 / Real.pi) * (((R : ℝ) + 4) * Real.log (Real.log (n : ℝ)) + 4)) ^ (2 * R) *
            (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂)))) / (Real.log (n : ℝ)) ^ (R + 2) ∧
        ((R : ℝ) * (2 : ℝ) ^ R * (Real.log (n : ℝ) / Real.log 2 + 2) *
          (((4 / Real.pi) * (((R : ℝ) + 4) * Real.log (Real.log (n : ℝ)) + 4)) ^ (2 * R) *
            (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂)))) / (Real.log (n : ℝ)) ^ (R + 2) ≤
        K_big * ((Real.log (Real.log (n : ℝ))) ^ (2 * R) / (Real.log (n : ℝ)) ^ (R + 1)) := by
      filter_upwards [hlog_inf.eventually (eventually_ge_atTop (Real.exp 2))] with n hn
      have hlog_ge2 : (2 : ℝ) ≤ Real.log (n : ℝ) := le_trans (by linarith [Real.add_one_le_exp (2 : ℝ)]) hn
      have hll_ge2 : (2 : ℝ) ≤ Real.log (Real.log (n : ℝ)) := by
        have := Real.log_le_log (Real.exp_pos 2) hn; rwa [Real.log_exp] at this
      have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
      constructor
      · positivity
      · have h1 : Real.log (n : ℝ) / Real.log 2 + 2 ≤ (1 / Real.log 2 + 2) * Real.log (n : ℝ) := by
          have : 0 < Real.log 2 := Real.log_pos (by norm_num)
          have : Real.log (n : ℝ) / Real.log 2 = (1 / Real.log 2) * Real.log (n : ℝ) := by ring
          nlinarith
        have h2 : ((R : ℝ) + 4) * Real.log (Real.log (n : ℝ)) + 4 ≤ ((R : ℝ) + 8) * Real.log (Real.log (n : ℝ)) := by
          nlinarith
        have h3 : ((4 / Real.pi) * (((R : ℝ) + 4) * Real.log (Real.log (n : ℝ)) + 4)) ^ (2 * R) ≤
            ((4 / Real.pi) * ((R : ℝ) + 8)) ^ (2 * R) * (Real.log (Real.log (n : ℝ))) ^ (2 * R) := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) (by
            have : 0 ≤ 4 / Real.pi := by positivity
            calc (4 / Real.pi) * (((R : ℝ) + 4) * Real.log (Real.log (n : ℝ)) + 4)
                ≤ (4 / Real.pi) * (((R : ℝ) + 8) * Real.log (Real.log (n : ℝ))) := mul_le_mul_of_nonneg_left h2 this
              _ = (4 / Real.pi) * ((R : ℝ) + 8) * Real.log (Real.log (n : ℝ)) := by ring) _
        have hpow_split : (Real.log (n : ℝ)) ^ (R + 2) = Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (R + 1) := by
          rw [pow_succ']
        rw [hpow_split]
        have hnum : (R : ℝ) * (2 : ℝ) ^ R * (Real.log (n : ℝ) / Real.log 2 + 2) *
              (((4 / Real.pi) * (((R : ℝ) + 4) * Real.log (Real.log (n : ℝ)) + 4)) ^ (2 * R) *
                (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂))) ≤
            (K_big * Real.log (n : ℝ)) * (Real.log (Real.log (n : ℝ))) ^ (2 * R) := by
          dsimp only [K_big]
          calc (R : ℝ) * (2 : ℝ) ^ R * (Real.log (n : ℝ) / Real.log 2 + 2) *
                (((4 / Real.pi) * (((R : ℝ) + 4) * Real.log (Real.log (n : ℝ)) + 4)) ^ (2 * R) *
                  (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂)))
              ≤ (R : ℝ) * (2 : ℝ) ^ R * ((1 / Real.log 2 + 2) * Real.log (n : ℝ)) *
                ((((4 / Real.pi) * ((R : ℝ) + 8)) ^ (2 * R) * (Real.log (Real.log (n : ℝ))) ^ (2 * R)) *
                  (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂))) := by gcongr
            _ = (R : ℝ) * (2 : ℝ) ^ R * (1 / Real.log 2 + 2) *
                ((4 / Real.pi) * ((R : ℝ) + 8)) ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂)) *
                Real.log (n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ (2 * R) := by ring
        calc _ ≤ ((K_big * Real.log (n : ℝ)) * (Real.log (Real.log (n : ℝ))) ^ (2 * R)) /
                (Real.log (n : ℝ) * (Real.log (n : ℝ)) ^ (R + 1)) := by gcongr
          _ = K_big * ((Real.log (Real.log (n : ℝ))) ^ (2 * R) / (Real.log (n : ℝ)) ^ (R + 1)) := by
              field_simp [hlog_pos.ne']
    exact squeeze_zero' (hev_dom.mono fun _ h => h.1) (hev_dom.mono fun _ h => h.2)
      (by simpa using hcomp.const_mul K_big)
  -- Collect all eventual conditions into one N_osc
  have h1_ev : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ)) ^ (R + 3) / (n : ℝ) ^ δ ≤ c₁_low / (10 * ((R : ℝ) * Mmax + 1)) := by
    have h0 := log_pow_div_rpow_tendsto_zero (R + 3) hδ0
    exact (h0.eventually (Iio_mem_nhds (by positivity))).mono fun _ h => h.le
  have h2_ev : ∀ᶠ n : ℕ in atTop,
      (10 * (Real.log (n : ℝ)) ^ (R + 3)) / (Real.log (n : ℝ)) ^ (A_R + 6) ≤ c₁_low / ((R : ℝ) * Mmax + 1) := by
    have h0 : Tendsto (fun x : ℝ => (10 * x ^ (R + 3)) / x ^ (A_R + 6)) atTop (nhds 0) := by
      let d_exp : ℕ := A_R + 6 - (R + 3)
      have hev : ∀ᶠ x : ℝ in atTop, (10 * x ^ (R + 3)) / x ^ (A_R + 6) = 10 * x ^ (-(d_exp : ℝ)) := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        have hx0 : x ≠ 0 := by linarith
        rw [Real.rpow_neg (by linarith), Real.rpow_natCast, div_eq_mul_inv, mul_assoc]
        congr 1
        have hsub : A_R + 6 = (R + 3) + d_exp := by dsimp [d_exp, A_R]; omega
        conv_lhs => rw [hsub, pow_add]
        field_simp [hx0]; rw [pow_add, pow_add]
      have hz : Tendsto (fun x : ℝ => 10 * x ^ (-(d_exp : ℝ))) atTop (nhds 0) := by
        have hpos : (0 : ℝ) < (d_exp : ℝ) := by exact_mod_cast (by dsimp [d_exp, A_R]; omega : 0 < d_exp)
        simpa using (tendsto_rpow_neg_atTop hpos).const_mul 10
      exact hz.congr' (hev.mono fun _ h => h.symm)
    exact ((h0.comp hlog_inf).eventually (Iio_mem_nhds (by positivity))).mono fun _ h => h.le
  have h3_ev : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (1 / ((R : ℝ) + 1)) * (n : ℝ) ^ (1 / ((R : ℝ) + 1)) ≤ (n : ℝ) ^ δ := by
    have hlt_exp : 1 / ((R : ℝ) + 1) < δ := by
      have h1 : 1 / δ < (R : ℝ) + 1 := Nat.lt_floor_add_one (1 / δ)
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [(div_lt_iff₀ hδ0).mp h1]
    have hdiff : 0 < δ - 1 / ((R : ℝ) + 1) := by linarith
    have htr := (tendsto_rpow_atTop hdiff).comp tendsto_natCast_atTop_atTop
    filter_upwards [Filter.eventually_ge_atTop 1, htr.eventually (eventually_ge_atTop ((2 : ℝ) ^ (1 / ((R : ℝ) + 1))))] with n hn hge
    dsimp only [Function.comp_apply] at hge
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    calc (2 : ℝ) ^ (1 / ((R : ℝ) + 1)) * (n : ℝ) ^ (1 / ((R : ℝ) + 1))
        ≤ (n : ℝ) ^ (δ - 1 / ((R : ℝ) + 1)) * (n : ℝ) ^ (1 / ((R : ℝ) + 1)) := by gcongr
      _ = (n : ℝ) ^ ((δ - 1 / ((R : ℝ) + 1)) + 1 / ((R : ℝ) + 1)) := (Real.rpow_add hn_pos _ _).symm
      _ = (n : ℝ) ^ δ := by ring_nf
  have h4_ev : ∀ᶠ n : ℕ in atTop,
      2 * C_mert * (Real.log (n : ℝ) + 1) / (n : ℝ) ^ δ < ε / 32 :=
    h_inv_delta.eventually (Iio_mem_nhds (by positivity))
  have h5_ev : ∀ᶠ n : ℕ in atTop,
      Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) <
        (ε / 32) / (2 * (R : ℝ) * C_mert * (3 * (A_R : ℝ) + 14) + 1) :=
    h_loglog.eventually (Iio_mem_nhds (by positivity))
  have h6_ev : ∀ᶠ n : ℕ in atTop,
      ((R : ℝ) * (2 : ℝ) ^ R * (Real.log (n : ℝ) / Real.log 2 + 2) *
        (((4 / Real.pi) * (((R : ℝ) + 4) * Real.log (Real.log (n : ℝ)) + 4)) ^ (2 * R) *
          (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂)))) / (Real.log (n : ℝ)) ^ (R + 2) < ε / 16 :=
    h_clean_tail.eventually (Iio_mem_nhds (by positivity))
  have h7_ev : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ (n : ℝ) ^ δ :=
    ((tendsto_rpow_atTop hδ0).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 3)
  have h8_ev : ∀ᶠ n : ℕ in atTop,
      (Real.exp 4 : ℝ) ≤ Real.log (n : ℝ) ∧
      1 / (Real.log (n : ℝ)) ^ (A_R + 4) < ε / 32 ∧
      (2 * (R : ℝ) * C_mert * 4) / Real.log (n : ℝ) < ε / 32 := by
    have ha := hlog_inf.eventually (eventually_ge_atTop (Real.exp 4))
    have hb : ∀ᶠ n : ℕ in atTop, 1 / (Real.log (n : ℝ)) ^ (A_R + 4) < ε / 32 := by
      have h0 : Tendsto (fun x : ℝ => 1 / x ^ (A_R + 4)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega))
      exact (h0.comp hlog_inf).eventually (Iio_mem_nhds (by positivity))
    have hc : ∀ᶠ n : ℕ in atTop, (2 * (R : ℝ) * C_mert * 4) / Real.log (n : ℝ) < ε / 32 := by
      have h0 : Tendsto (fun x : ℝ => (2 * (R : ℝ) * C_mert * 4) / x) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      exact (h0.comp hlog_inf).eventually (Iio_mem_nhds (by positivity))
    filter_upwards [ha, hb, hc] with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hAll : ∀ᶠ n : ℕ in atTop,
      1000 ≤ n ∧
      (∀ (P : ℝ) (I : Finset ℕ) (A : Finset ℕ) (M : ℕ → ℝ) (r₀ : ℕ) (w : ℝ → ℝ) (W₀ : ℝ),
        (n : ℝ) ^ δ ≤ P → P ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 12 → IsPrimeSubinterval P I →
        (∀ s ∈ A, 1 ≤ s ∧ s ≤ R) → r₀ ∈ A →
        (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n : ℝ)) ^ A_R ≤ |M r₀| / P ^ r₀ →
        |M r₀| / P ^ r₀ ≤ (n : ℝ) ^ 2 →
        (∀ s ∈ A.erase r₀, |M s| / P ^ s ≤ (c₁_low / ((R : ℝ) * Mmax + 1)) * (|M r₀| / P ^ r₀)) →
        (∀ t ∈ Set.Icc P (2 * P), |w t| ≤ W₀) → AntitoneOn w (Set.Icc P (2 * P)) → 0 ≤ W₀ →
        ‖∑ p ∈ I, (w (p : ℝ) * Real.log (p : ℝ) : ℂ) * eExp (∑ s ∈ A, M s / (2 * (p : ℝ) ^ s))‖ ≤
          C₂ * W₀ * P * (Real.log (n : ℝ)) ^ (-((R : ℝ) + 2))) ∧
      (Real.log (n : ℝ)) ^ (R + 3) / (n : ℝ) ^ δ ≤ c₁_low / (10 * ((R : ℝ) * Mmax + 1)) ∧
      (10 * (Real.log (n : ℝ)) ^ (R + 3)) / (Real.log (n : ℝ)) ^ (A_R + 6) ≤ c₁_low / ((R : ℝ) * Mmax + 1) ∧
      (2 : ℝ) ^ (1 / ((R : ℝ) + 1)) * (n : ℝ) ^ (1 / ((R : ℝ) + 1)) ≤ (n : ℝ) ^ δ ∧
      2 * C_mert * (Real.log (n : ℝ) + 1) / (n : ℝ) ^ δ < ε / 32 ∧
      Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) <
        (ε / 32) / (2 * (R : ℝ) * C_mert * (3 * (A_R : ℝ) + 14) + 1) ∧
      ((R : ℝ) * (2 : ℝ) ^ R * (Real.log (n : ℝ) / Real.log 2 + 2) *
        (((4 / Real.pi) * (((R : ℝ) + 4) * Real.log (Real.log (n : ℝ)) + 4)) ^ (2 * R) *
          (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂)))) / (Real.log (n : ℝ)) ^ (R + 2) < ε / 16 ∧
      (3 : ℝ) ≤ (n : ℝ) ^ δ ∧
      (Real.exp 4 : ℝ) ≤ Real.log (n : ℝ) ∧
      1 / (Real.log (n : ℝ)) ^ (A_R + 4) < ε / 32 ∧
      (2 * (R : ℝ) * C_mert * 4) / Real.log (n : ℝ) < ε / 32 := by
    filter_upwards [Filter.eventually_ge_atTop 1000, hGenExp, h1_ev, h2_ev, h3_ev, h4_ev, h5_ev, h6_ev, h7_ev, h8_ev] with
      n hn hG h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨hn, hG, h1, h2, h3, h4, h5, h6, h7, h8.1, h8.2.1, h8.2.2⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨max N₀ 1000, le_max_right _ _, ?_⟩
  intro n₁ n₂ hn₁ hlt
  dsimp only
  intro hh_ub hh_gt hy₁_gt
  obtain ⟨hn₁_1000, hGen, hsmall_d, hsmall_res, h2n_le_nd, herr_val, herr_ll, herr_clean, hnd_ge3,
    hlog_ge_e4, herr_y1, herr_const⟩ := hN₀ n₁ (le_trans (le_max_left _ _) hn₁)
  let h := n₂ - n₁
  let y₁ := (h : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2)
  let I_osc := ((Finset.Icc 3 n₁).filter Nat.Prime).filter (fun p : ℕ => (n₁ : ℝ) ^ δ < (p : ℝ) ∧ (p : ℝ) ≤ y₁)
  have hn₁_pos : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast (by omega : 0 < n₁)
  have hlog_ge5 : (5 : ℝ) ≤ Real.log (n₁ : ℝ) := by
    have : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    linarith
  have hlog_pos : 0 < Real.log (n₁ : ℝ) := by linarith
  have hll_ge4 : (4 : ℝ) ≤ Real.log (Real.log (n₁ : ℝ)) := by
    have := Real.log_le_log (Real.exp_pos 4) hlog_ge_e4; rwa [Real.log_exp] at this
  have hll_pos : 0 < Real.log (Real.log (n₁ : ℝ)) := by linarith
  have hh_pos : (0 : ℝ) < (h : ℝ) := lt_trans (by positivity) hh_gt
  have hh_lt_n₁ : (h : ℝ) < (n₁ : ℝ) := by
    have hpow_gt1 : (1 : ℝ) < (Real.log (n₁ : ℝ)) ^ (A_R + 4) := one_lt_pow₀ (by linarith) (by omega)
    calc (h : ℝ) ≤ (n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 4) := hh_ub
      _ < (n₁ : ℝ) / 1 := div_lt_div_of_pos_left hn₁_pos (by norm_num) hpow_gt1
      _ = (n₁ : ℝ) := div_one _
  have hn₂_eq : (n₂ : ℝ) = (n₁ : ℝ) + (h : ℝ) := by exact_mod_cast (by omega : n₂ = n₁ + h)
  have hn₂_lt_2n₁ : (n₂ : ℝ) < 2 * (n₁ : ℝ) := by linarith
  have hy₁_le_n₁ : y₁ ≤ (n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2) :=
    div_le_div_of_nonneg_right hh_lt_n₁.le (by positivity)
  have hy₁_le_n1_12 : y₁ ≤ (n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ 12 := by
    refine le_trans hy₁_le_n₁ (div_le_div_of_nonneg_left hn₁_pos.le (by positivity) ?_)
    exact pow_le_pow_right₀ (by linarith) (by unfold A_R; omega)
  -- STEP 1: Replace v_p(n₁!) by n₁ / p
  have hstep1 : |∑ p ∈ I_osc,
      ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
        ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) -
      ∑ p ∈ I_osc,
      ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
        (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))| ≤ (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ p ∈ I_osc, _|
        ≤ ∑ p ∈ I_osc, |((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
            ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) -
          ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
            (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ I_osc, ((2 * (n₁ : ℝ) / (n₁ : ℝ) ^ δ) * (Real.log (p : ℝ) / (p : ℝ)) + Real.log (n₁ : ℝ)) := by
          apply Finset.sum_le_sum; intro p hp
          have hp_m := Finset.mem_filter.mp hp
          have hp_pr : p.Prime := (Finset.mem_filter.mp hp_m.1).2
          have hp_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp_m.1).1
          have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)
          have hlogp_le : Real.log (p : ℝ) ≤ Real.log (n₁ : ℝ) :=
            Real.log_le_log (by exact_mod_cast hp_pr.pos) (by exact_mod_cast hp_icc.2)
          rw [← mul_sub, ← sub_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_nonneg hlogp_nn]
          have hv := val_factorial_sub_div_abs_le (n := n₁) hp_pr hp_icc.1
          have hp_gt : (n₁ : ℝ) ^ δ < (p : ℝ) := hp_m.2.1
          have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pr.pos
          calc |(padicValNat p (Nat.factorial n₁) : ℝ) - (n₁ : ℝ) / (p : ℝ)| * Real.log (p : ℝ)
              ≤ (2 * (n₁ : ℝ) / (p : ℝ) ^ 2 + 1) * Real.log (p : ℝ) := mul_le_mul_of_nonneg_right hv hlogp_nn
            _ = 2 * (n₁ : ℝ) / (p : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) + Real.log (p : ℝ) := by
                field_simp [hp_pos.ne']
            _ ≤ (2 * (n₁ : ℝ) / (n₁ : ℝ) ^ δ) * (Real.log (p : ℝ) / (p : ℝ)) + Real.log (n₁ : ℝ) := by
                gcongr
      _ = (2 * (n₁ : ℝ) / (n₁ : ℝ) ^ δ) * (∑ p ∈ I_osc, Real.log (p : ℝ) / (p : ℝ)) +
            (I_osc.card : ℝ) * Real.log (n₁ : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (n₁ : ℝ) / (n₁ : ℝ) ^ δ) * (C_mert * (Real.log (n₁ : ℝ) + 1)) +
            y₁ * Real.log (n₁ : ℝ) := by
          have hm1 : ∑ p ∈ I_osc, Real.log (p : ℝ) / (p : ℝ) ≤ C_mert * (Real.log (n₁ : ℝ) + 1) := by
            have hsub : I_osc ⊆ ((Finset.Icc 3 (Nat.floor (n₁ : ℝ))).filter Nat.Prime).filter (fun p : ℕ => (3 : ℝ) < (p : ℝ)) := by
              intro p hp
              have h1 := Finset.mem_filter.mp hp
              have h2 := Finset.mem_filter.mp h1.1
              have h3 := Finset.mem_Icc.mp h2.1
              rw [Nat.floor_natCast]
              exact Finset.mem_filter.mpr ⟨h1.1, lt_of_le_of_lt hnd_ge3 h1.2.1⟩
            calc ∑ p ∈ I_osc, Real.log (p : ℝ) / (p : ℝ)
                ≤ ∑ p ∈ ((Finset.Icc 3 (Nat.floor (n₁ : ℝ))).filter Nat.Prime).filter (fun p : ℕ => (3 : ℝ) < (p : ℝ)),
                    Real.log (p : ℝ) / (p : ℝ) :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
                    div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.one_lt.le)) (Nat.cast_nonneg p))
              _ ≤ Real.log ((n₁ : ℝ) / 3) + C_mert0 := hMert 3 (n₁ : ℝ) le_rfl (by exact_mod_cast (by omega : 3 ≤ n₁))
              _ ≤ Real.log (n₁ : ℝ) + C_mert0 := by
                  gcongr; exact div_le_self hn₁_pos.le (by norm_num)
              _ ≤ C_mert * (Real.log (n₁ : ℝ) + 1) := by
                  dsimp [C_mert]; nlinarith [hC_mert0_pos, hlog_pos]
          have hcard : (I_osc.card : ℝ) ≤ y₁ := by
            have hsub : I_osc ⊆ Finset.Icc 1 (Nat.floor y₁) := fun p hp =>
              Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.pos,
                Nat.le_floor (Finset.mem_filter.mp hp).2.2⟩
            exact le_trans (by exact_mod_cast le_trans (Finset.card_le_card hsub) (by simp))
              (Nat.floor_le (by positivity))
          gcongr
      _ ≤ (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) + (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          have ha : (2 * (n₁ : ℝ) / (n₁ : ℝ) ^ δ) * (C_mert * (Real.log (n₁ : ℝ) + 1)) ≤
              (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
            have h1 : (2 * (n₁ : ℝ) / (n₁ : ℝ) ^ δ) * (C_mert * (Real.log (n₁ : ℝ) + 1)) =
                (2 * C_mert * (Real.log (n₁ : ℝ) + 1) / (n₁ : ℝ) ^ δ) * (n₁ : ℝ) := by ring
            rw [h1]
            calc (2 * C_mert * (Real.log (n₁ : ℝ) + 1) / (n₁ : ℝ) ^ δ) * (n₁ : ℝ)
                ≤ (ε / 32) * (n₁ : ℝ) := by gcongr
              _ ≤ (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := le_mul_of_one_le_right (by positivity) (by linarith)
          have hb : y₁ * Real.log (n₁ : ℝ) ≤ (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
            have hy1_bd : y₁ ≤ (1 / (Real.log (n₁ : ℝ)) ^ (A_R + 4)) * (n₁ : ℝ) := by
              calc y₁ ≤ (h : ℝ) := div_le_self hh_pos.le (one_le_pow₀ (by linarith))
                _ ≤ (n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 4) := hh_ub
                _ = (1 / (Real.log (n₁ : ℝ)) ^ (A_R + 4)) * (n₁ : ℝ) := by ring
            calc y₁ * Real.log (n₁ : ℝ) ≤ ((1 / (Real.log (n₁ : ℝ)) ^ (A_R + 4)) * (n₁ : ℝ)) * Real.log (n₁ : ℝ) := by gcongr
              _ ≤ ((ε / 32) * (n₁ : ℝ)) * Real.log (n₁ : ℝ) := by gcongr
              _ = (ε / 32) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
          exact add_le_add ha hb
      _ = (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by ring
  -- STEP 2: Define thin power collars and resonance collars, excise them
  let powCollar : ℕ → ℝ × ℝ := fun r =>
    ((n₁ : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n₁ : ℝ)) ^ A_R, (n₂ : ℝ) ^ (1 / (r : ℝ)))
  let resCollar : ℕ → ℝ × ℝ := fun j₀ =>
    (((n₁ : ℝ) / (h : ℝ)) ^ (1 / ((j₀ : ℝ) - 1)) / (Real.log (n₁ : ℝ)) ^ (A_R + 6),
     ((n₁ : ℝ) / (h : ℝ)) ^ (1 / ((j₀ : ℝ) - 1)) * (Real.log (n₁ : ℝ)) ^ (A_R + 6))
  let isExcised : ℕ → Prop := fun p =>
    (∃ r ∈ Finset.Icc 2 R, (p : ℝ) ∈ Set.Ioc (powCollar r).1 (powCollar r).2) ∨
    (∃ j₀ ∈ Finset.Icc 2 R, (p : ℝ) ∈ Set.Ioc (resCollar j₀).1 (resCollar j₀).2)
  haveI : DecidablePred isExcised := Classical.decPred _
  let I_exc := I_osc.filter isExcised
  let I_clean := I_osc.filter (fun p => ¬ isExcised p)
  have hstep2_exc : |∑ p ∈ I_exc,
      ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
        (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))| ≤ (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
    have hband : ∀ (a b : ℝ) (K_ratio : ℝ), 1 ≤ K_ratio → 0 < a → b ≤ K_ratio * a →
        ∑ p ∈ I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc a b), Real.log (p : ℝ) / (p : ℝ) ≤
          C_mert * (Real.log K_ratio + 1) := by
      intro a b K_ratio hK ha hba
      by_cases hab : a < b
      · let a' := max a 3
        have hsub : I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc a b) ⊆
            ((Finset.Icc 3 (Nat.floor b)).filter Nat.Prime).filter (fun p : ℕ => a' < (p : ℝ)) := by
          intro p hp
          have h1 := Finset.mem_filter.mp hp
          have h2 := Finset.mem_filter.mp h1.1
          have h3 := Finset.mem_filter.mp h2.1
          have hp3 : 3 ≤ p := (Finset.mem_Icc.mp h3.1).1
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, Nat.le_floor h1.2.2⟩, h3.2⟩,
            max_lt h1.2.1 (lt_of_le_of_lt hnd_ge3 h2.2.1)⟩
        by_cases ha'b : a' ≤ b
        · calc ∑ p ∈ I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc a b), Real.log (p : ℝ) / (p : ℝ)
              ≤ ∑ p ∈ ((Finset.Icc 3 (Nat.floor b)).filter Nat.Prime).filter (fun p : ℕ => a' < (p : ℝ)),
                  Real.log (p : ℝ) / (p : ℝ) :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
                  div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.one_lt.le)) (Nat.cast_nonneg p))
            _ ≤ Real.log (b / a') + C_mert0 := hMert a' b (le_max_right a 3) ha'b
            _ ≤ Real.log K_ratio + C_mert0 := by
                have hdiv : b / a' ≤ K_ratio := by
                  calc b / a' ≤ b / a := div_le_div_of_nonneg_left (by linarith) ha (le_max_left a 3)
                    _ ≤ (K_ratio * a) / a := div_le_div_of_nonneg_right hba ha.le
                    _ = K_ratio := mul_div_cancel_right₀ K_ratio ha.ne'
                gcongr
                exact div_pos (by linarith) (lt_of_lt_of_le ha (le_max_left a 3))
            _ ≤ C_mert * (Real.log K_ratio + 1) := by
                have : 0 ≤ Real.log K_ratio := Real.log_nonneg hK
                dsimp [C_mert]; nlinarith [hC_mert0_pos]
        · push_neg at ha'b
          have hemp : I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc a b) = ∅ := by
            ext p; simp only [Finset.notMem_empty, iff_false]
            intro hp
            have h1 := Finset.mem_filter.mp hp
            have h2 := Finset.mem_filter.mp (hsub hp)
            linarith [h1.2.2, h2.2]
          rw [hemp, Finset.sum_empty]
          have : 0 ≤ Real.log K_ratio := Real.log_nonneg hK
          positivity
      · push_neg at hab
        have hemp : I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc a b) = ∅ := by
          ext p; simp only [Finset.notMem_empty, iff_false, Finset.mem_filter, Set.mem_Ioc]
          intro hp; linarith [hp.2.1, hp.2.2]
        rw [hemp, Finset.sum_empty]
        have : 0 ≤ Real.log K_ratio := Real.log_nonneg hK
        positivity
    have hpow_bd : ∀ r ∈ Finset.Icc 2 R,
        ∑ p ∈ I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc (powCollar r).1 (powCollar r).2), Real.log (p : ℝ) / (p : ℝ) ≤
          C_mert * ((A_R : ℝ) * Real.log (Real.log (n₁ : ℝ)) + 2) := by
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have h1 := hband (powCollar r).1 (powCollar r).2 (2 * (Real.log (n₁ : ℝ)) ^ A_R)
        (by have : (1 : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ A_R := one_le_pow₀ (by linarith); linarith)
        (by dsimp [powCollar]; positivity)
        (by
          dsimp [powCollar]
          have hn2_le : (n₂ : ℝ) ^ (1 / (r : ℝ)) ≤ 2 * (n₁ : ℝ) ^ (1 / (r : ℝ)) := by
            calc (n₂ : ℝ) ^ (1 / (r : ℝ)) ≤ (2 * (n₁ : ℝ)) ^ (1 / (r : ℝ)) :=
                  Real.rpow_le_rpow (by positivity) hn₂_lt_2n₁.le (by positivity)
              _ = (2 : ℝ) ^ (1 / (r : ℝ)) * (n₁ : ℝ) ^ (1 / (r : ℝ)) := Real.mul_rpow (by norm_num) hn₁_pos.le
              _ ≤ 2 * (n₁ : ℝ) ^ (1 / (r : ℝ)) := by
                  gcongr
                  calc (2 : ℝ) ^ (1 / (r : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                        Real.rpow_le_rpow_of_exponent_le (by norm_num) (div_le_self (by norm_num) (by exact_mod_cast (by omega : 1 ≤ r)))
                    _ = 2 := Real.rpow_one _
          have hpow_ne : (Real.log (n₁ : ℝ)) ^ A_R ≠ 0 := by positivity
          calc (n₂ : ℝ) ^ (1 / (r : ℝ)) ≤ 2 * (n₁ : ℝ) ^ (1 / (r : ℝ)) := hn2_le
            _ = 2 * (Real.log (n₁ : ℝ)) ^ A_R * ((n₁ : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n₁ : ℝ)) ^ A_R) := by
                field_simp [hpow_ne])
      have hlog_eq : Real.log (2 * (Real.log (n₁ : ℝ)) ^ A_R) ≤ (A_R : ℝ) * Real.log (Real.log (n₁ : ℝ)) + 1 := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        have : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      calc _ ≤ C_mert * (Real.log (2 * (Real.log (n₁ : ℝ)) ^ A_R) + 1) := h1
        _ ≤ C_mert * ((A_R : ℝ) * Real.log (Real.log (n₁ : ℝ)) + 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hC_mert_pos.le
    have hres_bd : ∀ j₀ ∈ Finset.Icc 2 R,
        ∑ p ∈ I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc (resCollar j₀).1 (resCollar j₀).2), Real.log (p : ℝ) / (p : ℝ) ≤
          C_mert * ((2 * (A_R : ℝ) + 12) * Real.log (Real.log (n₁ : ℝ)) + 1) := by
      intro j₀ hj₀
      have h1 := hband (resCollar j₀).1 (resCollar j₀).2 ((Real.log (n₁ : ℝ)) ^ (2 * A_R + 12))
        (one_le_pow₀ (by linarith))
        (by dsimp [resCollar]; positivity)
        (by
          dsimp [resCollar]
          have hpow_ne : (Real.log (n₁ : ℝ)) ^ (A_R + 6) ≠ 0 := by positivity
          have hexp : (Real.log (n₁ : ℝ)) ^ (2 * A_R + 12) = (Real.log (n₁ : ℝ)) ^ (A_R + 6) * (Real.log (n₁ : ℝ)) ^ (A_R + 6) := by
            rw [← pow_add]; congr 1; omega
          rw [hexp]; field_simp [hpow_ne]; rfl)
      rw [Real.log_pow] at h1
      convert h1 using 2; push_cast; ring
    have hsub_exc : I_exc ⊆
        ((Finset.Icc 2 R).biUnion (fun r => I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc (powCollar r).1 (powCollar r).2))) ∪
        ((Finset.Icc 2 R).biUnion (fun j₀ => I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc (resCollar j₀).1 (resCollar j₀).2))) := by
      intro p hp
      have h1 := Finset.mem_filter.mp hp
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
      rcases h1.2 with ⟨r, hr, hpr⟩ | ⟨j₀, hj₀, hpj⟩
      · exact Or.inl ⟨r, hr, h1.1, hpr⟩
      · exact Or.inr ⟨j₀, hj₀, h1.1, hpj⟩
    have hsum_exc_inv : ∑ p ∈ I_exc, Real.log (p : ℝ) / (p : ℝ) ≤
        (R : ℝ) * C_mert * ((3 * (A_R : ℝ) + 14) * Real.log (Real.log (n₁ : ℝ)) + 4) := by
      have hnn : ∀ p ∈ ((Finset.Icc 2 R).biUnion (fun r => I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc (powCollar r).1 (powCollar r).2))) ∪
          ((Finset.Icc 2 R).biUnion (fun j₀ => I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc (resCollar j₀).1 (resCollar j₀).2))),
          0 ≤ Real.log (p : ℝ) / (p : ℝ) := by
        intro p hp
        have hp_osc : p ∈ I_osc := by
          simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter] at hp
          rcases hp with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ <;> exact h
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp_osc).1).2.one_lt.le)) (Nat.cast_nonneg p)
      let U_exc := ((Finset.Icc 2 R).biUnion (fun r => I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc (powCollar r).1 (powCollar r).2))) ∪
          ((Finset.Icc 2 R).biUnion (fun j₀ => I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc (resCollar j₀).1 (resCollar j₀).2)))
      calc ∑ p ∈ I_exc, Real.log (p : ℝ) / (p : ℝ)
          ≤ ∑ p ∈ U_exc, Real.log (p : ℝ) / (p : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg hsub_exc (fun p hp _ => hnn p hp)
        _ ≤ (∑ p ∈ (Finset.Icc 2 R).biUnion (fun r => I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc (powCollar r).1 (powCollar r).2)),
              Real.log (p : ℝ) / (p : ℝ)) +
            (∑ p ∈ (Finset.Icc 2 R).biUnion (fun j₀ => I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc (resCollar j₀).1 (resCollar j₀).2)),
              Real.log (p : ℝ) / (p : ℝ)) :=
            sum_union_le_of_nonneg hnn
        _ ≤ (∑ r ∈ Finset.Icc 2 R, ∑ p ∈ I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc (powCollar r).1 (powCollar r).2),
              Real.log (p : ℝ) / (p : ℝ)) +
            (∑ j₀ ∈ Finset.Icc 2 R, ∑ p ∈ I_osc.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc (resCollar j₀).1 (resCollar j₀).2),
              Real.log (p : ℝ) / (p : ℝ)) :=
            add_le_add (sum_biUnion_le_of_nonneg (fun p hp => hnn p (Finset.mem_union_left _ hp)))
              (sum_biUnion_le_of_nonneg (fun p hp => hnn p (Finset.mem_union_right _ hp)))
        _ ≤ (∑ _r ∈ Finset.Icc 2 R, C_mert * ((A_R : ℝ) * Real.log (Real.log (n₁ : ℝ)) + 2)) +
            (∑ _j₀ ∈ Finset.Icc 2 R, C_mert * ((2 * (A_R : ℝ) + 12) * Real.log (Real.log (n₁ : ℝ)) + 1)) :=
            add_le_add (Finset.sum_le_sum hpow_bd) (Finset.sum_le_sum hres_bd)
        _ ≤ (R : ℝ) * C_mert * ((3 * (A_R : ℝ) + 14) * Real.log (Real.log (n₁ : ℝ)) + 4) := by
            rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
            have hcard : ((Finset.Icc 2 R).card : ℝ) ≤ (R : ℝ) := by
              have : (Finset.Icc 2 R).card ≤ R := by simp
              exact_mod_cast this
            have hterm_nn : 0 ≤ C_mert * ((3 * (A_R : ℝ) + 12) * Real.log (Real.log (n₁ : ℝ)) + 3) := by positivity
            have hsum_eq : ((Finset.Icc 2 R).card : ℝ) * (C_mert * ((A_R : ℝ) * Real.log (Real.log (n₁ : ℝ)) + 2)) +
                ((Finset.Icc 2 R).card : ℝ) * (C_mert * ((2 * (A_R : ℝ) + 12) * Real.log (Real.log (n₁ : ℝ)) + 1)) =
                ((Finset.Icc 2 R).card : ℝ) * (C_mert * ((3 * (A_R : ℝ) + 12) * Real.log (Real.log (n₁ : ℝ)) + 3)) := by ring
            rw [hsum_eq]
            have h1 : ((Finset.Icc 2 R).card : ℝ) * (C_mert * ((3 * (A_R : ℝ) + 12) * Real.log (Real.log (n₁ : ℝ)) + 3)) ≤
                (R : ℝ) * (C_mert * ((3 * (A_R : ℝ) + 12) * Real.log (Real.log (n₁ : ℝ)) + 3)) :=
              mul_le_mul_of_nonneg_right hcard hterm_nn
            have h2 : (R : ℝ) * (C_mert * ((3 * (A_R : ℝ) + 12) * Real.log (Real.log (n₁ : ℝ)) + 3)) ≤
                (R : ℝ) * C_mert * ((3 * (A_R : ℝ) + 14) * Real.log (Real.log (n₁ : ℝ)) + 4) := by
              rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith [hll_pos]) (by positivity)
            exact le_trans h1 h2
    calc |∑ p ∈ I_exc, _|
        ≤ ∑ p ∈ I_exc, |((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
            (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ = (n₁ : ℝ) * ∑ p ∈ I_exc, Real.log (p : ℝ) / (p : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p hp => ?_
          have hp_pr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)))]
          ring
      _ ≤ (n₁ : ℝ) * ((R : ℝ) * C_mert * ((3 * (A_R : ℝ) + 14) * Real.log (Real.log (n₁ : ℝ)) + 4)) := by gcongr
      _ ≤ (ε / 16) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          have h1 : (R : ℝ) * C_mert * (3 * (A_R : ℝ) + 14) * Real.log (Real.log (n₁ : ℝ)) ≤
              (ε / 32) * Real.log (n₁ : ℝ) := by
            have hd : 0 < 2 * (R : ℝ) * C_mert * (3 * (A_R : ℝ) + 14) + 1 := by positivity
            have hmul : Real.log (Real.log (n₁ : ℝ)) * (2 * (R : ℝ) * C_mert * (3 * (A_R : ℝ) + 14) + 1) <
                (ε / 32) * Real.log (n₁ : ℝ) := (div_lt_div_iff₀ hlog_pos hd).mp herr_ll
            have hR_nn : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
            have hAR_nn : (0 : ℝ) ≤ (A_R : ℝ) := Nat.cast_nonneg A_R
            have hprod_nn : 0 ≤ (R : ℝ) * C_mert * (3 * (A_R : ℝ) + 14) * Real.log (Real.log (n₁ : ℝ)) := by positivity
            nlinarith [hll_pos]
          have h2 : (R : ℝ) * C_mert * 4 ≤ (ε / 32) * Real.log (n₁ : ℝ) := by
            have := (div_lt_iff₀ hlog_pos).mp herr_const
            nlinarith [hC_mert_pos]
          nlinarith [hn₁_pos]
  -- STEP 3: Bound the clean primes I_clean using exact multi-digit Vaaler + prime_exp_sum_bounds_general_phase
  have hstep3_clean : |∑ p ∈ I_clean,
      ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
        (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))| ≤ (ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
    let H := Nat.floor ((Real.log (n₁ : ℝ)) ^ (R + 3))
    have hH_ge1 : 1 ≤ H := Nat.le_floor (by simpa using one_le_pow₀ (by linarith : (1 : ℝ) ≤ Real.log (n₁ : ℝ)))
    obtain ⟨c_tilde, b_tilde, h_supp, h_ctilde_b, h_btilde0, h_btilde_b, h_vaaler_pw, h_L1⟩ :=
      vaaler_parity_approx H hH_ge1
    let S_H := (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (fun m => m ≠ 0 ∧ Odd m)
    let Psi_tilde : ℝ → ℂ := fun x => ∑ m ∈ S_H, c_tilde m * eExp ((m : ℝ) * x / 2)
    let B_tilde : ℝ → ℂ := fun x => ∑ m ∈ Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1),
      b_tilde m * eExp ((m : ℝ) * x / 2)
    let L₁ : ℝ := (4 / Real.pi) * (((R : ℝ) + 4) * Real.log (Real.log (n₁ : ℝ)) + 4)
    have hL₁_ge : (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1) ≤ L₁ := by
      dsimp only [L₁]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hH_le : 2 * (H : ℝ) + 1 ≤ 3 * (Real.log (n₁ : ℝ)) ^ (R + 3) := by
        have hfl : (H : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (R + 3) := Nat.floor_le (by positivity)
        have h1 : (1 : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (R + 3) := one_le_pow₀ (by linarith)
        linarith
      have hlog_le : Real.log (2 * (H : ℝ) + 1) ≤ Real.log 3 + ((R : ℝ) + 3) * Real.log (Real.log (n₁ : ℝ)) := by
        calc Real.log (2 * (H : ℝ) + 1) ≤ Real.log (3 * (Real.log (n₁ : ℝ)) ^ (R + 3)) :=
              Real.log_le_log (by positivity) hH_le
          _ = Real.log 3 + ((R + 3 : ℕ) : ℝ) * Real.log (Real.log (n₁ : ℝ)) := by
              rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          _ = Real.log 3 + ((R : ℝ) + 3) * Real.log (Real.log (n₁ : ℝ)) := by push_cast; ring
      have hlog3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
      linarith
    have hL₁_ge1 : 1 ≤ L₁ := by
      have hpi4 : 1 ≤ 4 / Real.pi := by rw [one_le_div Real.pi_pos]; linarith [Real.pi_lt_four]
      have hlog_nn : 0 ≤ Real.log (2 * (H : ℝ) + 1) := Real.log_nonneg (by linarith [show (0 : ℝ) ≤ H by positivity])
      nlinarith
    have hPsi_bd : ∀ x : ℝ, ‖Psi_tilde x‖ ≤ L₁ := fun x => by
      dsimp only [Psi_tilde]
      calc ‖∑ m ∈ S_H, c_tilde m * eExp ((m : ℝ) * x / 2)‖
          ≤ ∑ m ∈ S_H, ‖c_tilde m * eExp ((m : ℝ) * x / 2)‖ := norm_sum_le _ _
        _ = ∑ m ∈ S_H, ‖c_tilde m‖ := by
            apply Finset.sum_congr rfl; intro m _
            rw [norm_mul]; unfold eExp
            rw [show (2 * Real.pi * Complex.I * (((m : ℝ) * x / 2 : ℝ) : ℂ) : ℂ) =
              ((2 * Real.pi * ((m : ℝ) * x / 2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I, mul_one]
        _ ≤ (4 / Real.pi) * (Real.log (2 * (H : ℝ) + 1) + 1) := h_L1
        _ ≤ L₁ := hL₁_ge
    -- Partition I_clean into r ∈ Icc 1 R
    let D_lo : ℕ → ℝ := fun r => max ((n₁ : ℝ) ^ δ) ((n₂ : ℝ) ^ (1 / ((r : ℝ) + 1)))
    let D_hi : ℕ → ℝ := fun r => min y₁ ((n₁ : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n₁ : ℝ)) ^ A_R)
    let D_clean : ℕ → Finset ℕ := fun r =>
      I_clean.filter (fun p : ℕ => D_lo r < (p : ℝ) ∧ (p : ℝ) ≤ D_hi r)
    have hI_clean_eq : I_clean = (Finset.Icc 1 R).biUnion D_clean := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_Icc, D_clean, Finset.mem_filter]
      constructor
      · intro hp
        have hp_osc := (Finset.mem_filter.mp hp).1
        have hp_not := (Finset.mem_filter.mp hp).2
        have hp_m := (Finset.mem_filter.mp hp_osc).2
        have h_n2_le_nd : (n₂ : ℝ) ^ (1 / ((R : ℝ) + 1)) ≤ (n₁ : ℝ) ^ δ := by
          calc (n₂ : ℝ) ^ (1 / ((R : ℝ) + 1)) ≤ (2 * (n₁ : ℝ)) ^ (1 / ((R : ℝ) + 1)) :=
                Real.rpow_le_rpow (by positivity) hn₂_lt_2n₁.le (by positivity)
            _ = (2 : ℝ) ^ (1 / ((R : ℝ) + 1)) * (n₁ : ℝ) ^ (1 / ((R : ℝ) + 1)) := Real.mul_rpow (by norm_num) hn₁_pos.le
            _ ≤ (n₁ : ℝ) ^ δ := h2n_le_nd
        -- Find smallest r ∈ [1, R] such that (n₂ : ℝ)^(1/(r+1)) < p
        have hex : ∃ r ∈ Finset.Icc 1 R, (n₂ : ℝ) ^ (1 / ((r : ℝ) + 1)) < (p : ℝ) :=
          ⟨R, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, lt_of_le_of_lt h_n2_le_nd hp_m.1⟩
        let S_r := (Finset.Icc 1 R).filter (fun r : ℕ => (n₂ : ℝ) ^ (1 / ((r : ℝ) + 1)) < (p : ℝ))
        have hSr_ne : S_r.Nonempty := by obtain ⟨r, hr, hpr⟩ := hex; exact ⟨r, Finset.mem_filter.mpr ⟨hr, hpr⟩⟩
        let r := S_r.min' hSr_ne
        have hr_mem := Finset.mem_filter.mp (Finset.min'_mem S_r hSr_ne)
        have hr_icc := Finset.mem_Icc.mp hr_mem.1
        refine ⟨r, hr_icc, hp, max_lt hp_m.1 hr_mem.2, le_min hp_m.2 ?_⟩
        by_cases hr1 : r = 1
        · rw [hr1]
          rw [Nat.cast_one, div_one, Real.rpow_one]
          exact le_trans hp_m.2 (le_trans hy₁_le_n₁ (div_le_div_of_nonneg_left hn₁_pos.le (by positivity)
            (pow_le_pow_right₀ (by linarith) (by omega))))
        · have hr_ge2 : 2 ≤ r := by omega
          have h_le_n2 : (p : ℝ) ≤ (n₂ : ℝ) ^ (1 / (r : ℝ)) := by
            by_contra hgt; push_neg at hgt
            have hmem' : r - 1 ∈ S_r := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
              have hcast : ((r - 1 : ℕ) : ℝ) + 1 = (r : ℝ) := by rw [Nat.cast_sub (by omega : 1 ≤ r)]; ring
              rwa [hcast]
            have := Finset.min'_le S_r (r - 1) hmem'
            omega
          have hnot_pow : (p : ℝ) ∉ Set.Ioc (powCollar r).1 (powCollar r).2 := fun hmem =>
            hp_not (Or.inl ⟨r, Finset.mem_Icc.mpr ⟨hr_ge2, hr_icc.2⟩, hmem⟩)
          by_contra hgt; push_neg at hgt
          exact hnot_pow ⟨hgt, h_le_n2⟩
      · rintro ⟨_, _, hp, _⟩; exact hp
    have hD_disj : Set.PairwiseDisjoint (Finset.Icc 1 R : Set ℕ) D_clean := by
      intro r₁ hr₁ r₂ hr₂ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp₁ hp₂
      have h1 := (Finset.mem_filter.mp hp₁).2
      have h2 := (Finset.mem_filter.mp hp₂).2
      have h_contra : ∀ a b : ℕ, 1 ≤ a → a < b →
          D_lo a < (p : ℝ) → (p : ℝ) ≤ D_hi a → D_lo b < (p : ℝ) → (p : ℝ) ≤ D_hi b → False := by
        intro a b ha hab _ _ _ hpb
        have hlo_a : (n₂ : ℝ) ^ (1 / ((a : ℝ) + 1)) < (p : ℝ) := lt_of_le_of_lt (le_max_right _ _) (by
          assumption)
        have hhi_b : (p : ℝ) ≤ (n₁ : ℝ) ^ (1 / (b : ℝ)) / (Real.log (n₁ : ℝ)) ^ A_R := le_trans hpb (min_le_right _ _)
        have hle1 : (n₁ : ℝ) ^ (1 / (b : ℝ)) / (Real.log (n₁ : ℝ)) ^ A_R ≤ (n₁ : ℝ) ^ (1 / (b : ℝ)) :=
          div_le_self (by positivity) (one_le_pow₀ (by linarith))
        have hle2 : (n₁ : ℝ) ^ (1 / (b : ℝ)) ≤ (n₂ : ℝ) ^ (1 / ((a : ℝ) + 1)) := by
          calc (n₁ : ℝ) ^ (1 / (b : ℝ)) ≤ (n₂ : ℝ) ^ (1 / (b : ℝ)) :=
                Real.rpow_le_rpow hn₁_pos.le (by exact_mod_cast le_of_lt hlt) (by positivity)
            _ ≤ (n₂ : ℝ) ^ (1 / ((a : ℝ) + 1)) := by
                apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n₂))
                exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : a + 1 ≤ b))
        linarith
      rcases lt_or_gt_of_ne hne with hlt' | hgt'
      · exact h_contra r₁ r₂ (Finset.mem_Icc.mp hr₁).1 hlt' h1.1 h1.2 h2.1 h2.2
      · exact h_contra r₂ r₁ (Finset.mem_Icc.mp hr₂).1 hgt' h2.1 h2.2 h1.1 h1.2
    -- Bound each D_clean r
    let resList : List (ℝ × ℝ) := ((List.range (R - 1)).map (fun k => resCollar (k + 2)))
    have hresList_len : resList.length = R - 1 := by simp [resList]
    have hresList_mem : ∀ j₀ ∈ Finset.Icc 2 R, resCollar j₀ ∈ resList := by
      intro j₀ hj₀
      have h1 := Finset.mem_Icc.mp hj₀
      rw [List.mem_map]
      exact ⟨j₀ - 2, List.mem_range.mpr (by omega), by congr 1; omega⟩
    have hresList_lt : ∀ cd ∈ resList, cd.1 < cd.2 := by
      intro cd hcd
      rw [List.mem_map] at hcd
      obtain ⟨k, _, rfl⟩ := hcd
      dsimp [resCollar]
      have h1 : (1 : ℝ) < (Real.log (n₁ : ℝ)) ^ (A_R + 6) := one_lt_pow₀ (by linarith) (by omega)
      have hbase_pos : (0 : ℝ) < ((n₁ : ℝ) / (h : ℝ)) ^ (1 / (((k + 2 : ℕ) : ℝ) - 1)) := by positivity
      calc ((n₁ : ℝ) / (h : ℝ)) ^ (1 / (((k + 2 : ℕ) : ℝ) - 1)) / (Real.log (n₁ : ℝ)) ^ (A_R + 6)
          < ((n₁ : ℝ) / (h : ℝ)) ^ (1 / (((k + 2 : ℕ) : ℝ) - 1)) / 1 :=
            div_lt_div_of_pos_left hbase_pos (by norm_num) h1
        _ = ((n₁ : ℝ) / (h : ℝ)) ^ (1 / (((k + 2 : ℕ) : ℝ) - 1)) := div_one _
        _ < ((n₁ : ℝ) / (h : ℝ)) ^ (1 / (((k + 2 : ℕ) : ℝ) - 1)) * (Real.log (n₁ : ℝ)) ^ (A_R + 6) :=
            lt_mul_of_one_lt_right hbase_pos h1
    have hresList_le : ∀ cd ∈ resList, cd.1 ≤ cd.2 := fun cd hcd => (hresList_lt cd hcd).le
    have hDr_bound : ∀ r ∈ Finset.Icc 1 R,
        |∑ p ∈ D_clean r,
          ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
            (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))| ≤
          (n₁ : ℝ) * ((2 : ℝ) ^ R * (Real.log (n₁ : ℝ) / Real.log 2 + 2) *
            (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂))) / (Real.log (n₁ : ℝ)) ^ (R + 2)) := by
      intro r hr
      have hr_icc := Finset.mem_Icc.mp hr
      let L_ivs := removeIocs resList [(D_lo r, D_hi r)]
      have hL_len : L_ivs.length ≤ 2 ^ R := by
        rw [removeIocs_length, hresList_len, List.length_singleton, mul_one]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      obtain ⟨hL_pw, hL_sub, hL_disj, hL_cov⟩ := removeIocs_props resList [(D_lo r, D_hi r)] hresList_le (by simp)
      -- Split D_clean r across the disjoint subintervals in L_ivs
      let subFin : Fin L_ivs.length → Finset ℕ := fun idx =>
        D_clean r |>.filter (fun p : ℕ => (p : ℝ) ∈ Set.Ioc (L_ivs.get idx).1 (L_ivs.get idx).2)
      have hDr_eq : D_clean r = Finset.univ.biUnion subFin := by
        ext p; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, subFin, Finset.mem_filter]
        constructor
        · intro hp
          have hp_m := Finset.mem_filter.mp hp
          have hp_not := (Finset.mem_filter.mp hp_m.1).2
          have hnot_res : ∀ cd ∈ resList, (p : ℝ) ∉ Set.Ioc cd.1 cd.2 := by
            intro cd hcd hmem
            rw [List.mem_map] at hcd
            obtain ⟨k, hk, rfl⟩ := hcd
            exact hp_not (Or.inr ⟨k + 2, Finset.mem_Icc.mpr ⟨by omega, by have := List.mem_range.mp hk; omega⟩, hmem⟩)
          obtain ⟨u, hu, hxu⟩ := hL_cov (p : ℝ) ⟨(D_lo r, D_hi r), by simp, hp_m.2⟩ hnot_res
          obtain ⟨idx, rfl⟩ := List.mem_iff_get.mp hu
          exact ⟨idx, hp, hxu⟩
        · rintro ⟨_, hp, _⟩; exact hp
      have hsub_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin L_ivs.length)) subFin := by
        intro i _ j _ hij
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro p hpi hpj
        have h1 := (Finset.mem_filter.mp hpi).2
        have h2 := (Finset.mem_filter.mp hpj).2
        have hpw_ij := List.pairwise_iff_get.mp hL_pw
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt' | hgt'
        · exact Set.disjoint_left.mp (hpw_ij i j hlt') h1 h2
        · exact Set.disjoint_left.mp (hpw_ij j i hgt') h2 h1
      rw [hDr_eq, Finset.sum_biUnion hsub_disj]
      -- Bound each subinterval subFin idx
      have hidx_bd : ∀ idx : Fin L_ivs.length,
          |∑ p ∈ subFin idx,
            ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
              (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))| ≤
            (n₁ : ℝ) * ((Real.log (n₁ : ℝ) / Real.log 2 + 2) *
              (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂))) / (Real.log (n₁ : ℝ)) ^ (R + 2)) := by
        intro idx
        let a_m := (L_ivs.get idx).1
        let b_m := (L_ivs.get idx).2
        rcases le_or_gt b_m a_m with hle_ab | hlt_ab
        · have hemp : subFin idx = ∅ := by
            ext p; simp only [Finset.notMem_empty, iff_false, subFin, Finset.mem_filter, Set.mem_Ioc]
            intro hp; linarith [hp.2.1, hp.2.2]
          rw [hemp, Finset.sum_empty, abs_zero]; positivity
        · have hu_mem : (a_m, b_m) ∈ L_ivs := List.get_mem L_ivs idx
          obtain ⟨v, hv, huv_sub⟩ := hL_sub (a_m, b_m) hu_mem
          simp only [List.mem_singleton] at hv
          subst hv
          have ha_ge_nd : (n₁ : ℝ) ^ δ ≤ a_m := by
            by_contra hlt'; push_neg at hlt'
            have h1 : a_m < min b_m ((n₁ : ℝ) ^ δ) := lt_min hlt_ab hlt'
            have hx_gt : a_m < (a_m + min b_m ((n₁ : ℝ) ^ δ)) / 2 := by linarith
            have hx_le : (a_m + min b_m ((n₁ : ℝ) ^ δ)) / 2 ≤ min b_m ((n₁ : ℝ) ^ δ) := by linarith
            have hx : (a_m + min b_m ((n₁ : ℝ) ^ δ)) / 2 ∈ Set.Ioc a_m b_m :=
              ⟨hx_gt, le_trans hx_le (min_le_left _ _)⟩
            have hxD := huv_sub hx
            have hlo_ge : (n₁ : ℝ) ^ δ ≤ D_lo r := le_max_left _ _
            linarith [hxD.1, hx_le, min_le_right b_m ((n₁ : ℝ) ^ δ)]
          have ha_ge1 : 1 ≤ a_m := by linarith [hnd_ge3]
          have hb_le_y₁ : b_m ≤ y₁ := by
            by_contra hgt'; push_neg at hgt'
            have h1 : max a_m y₁ < b_m := max_lt hlt_ab hgt'
            have hx_gt : max a_m y₁ < (max a_m y₁ + b_m) / 2 := by linarith
            have hx_le : (max a_m y₁ + b_m) / 2 ≤ b_m := by linarith
            have hx : (max a_m y₁ + b_m) / 2 ∈ Set.Ioc a_m b_m :=
              ⟨lt_of_le_of_lt (le_max_left _ _) hx_gt, hx_le⟩
            have hxD := huv_sub hx
            have hhi_le : D_hi r ≤ y₁ := min_le_left _ _
            linarith [hxD.2, hx_gt, le_max_right a_m y₁]
          have hb_le_Dhi : b_m ≤ D_hi r := by
            by_contra hgt'; push_neg at hgt'
            have h1 : max a_m (D_hi r) < b_m := max_lt hlt_ab hgt'
            have hx_gt : max a_m (D_hi r) < (max a_m (D_hi r) + b_m) / 2 := by linarith
            have hx_le : (max a_m (D_hi r) + b_m) / 2 ≤ b_m := by linarith
            have hx : (max a_m (D_hi r) + b_m) / 2 ∈ Set.Ioc a_m b_m :=
              ⟨lt_of_le_of_lt (le_max_left _ _) hx_gt, hx_le⟩
            have hxD := huv_sub hx
            linarith [hxD.2, hx_gt, le_max_right a_m (D_hi r)]
          -- Key: subFin idx is the EXACT set of primes in (a_m, b_m]!
          have hsub_exact : ∀ p : ℕ, p ∈ subFin idx ↔ p.Prime ∧ a_m < (p : ℝ) ∧ (p : ℝ) ≤ b_m := by
            intro p
            constructor
            · intro hp
              have h1 := Finset.mem_filter.mp hp
              have h2 := Finset.mem_filter.mp h1.1
              have h3 := Finset.mem_filter.mp h2.1
              have h4 := Finset.mem_filter.mp h3.1
              exact ⟨(Finset.mem_filter.mp h4.1).2, h1.2.1, h1.2.2⟩
            · rintro ⟨hpr, hpa, hpb⟩
              have hpD : (p : ℝ) ∈ Set.Ioc (D_lo r) (D_hi r) := huv_sub ⟨hpa, hpb⟩
              have hp_nd : (n₁ : ℝ) ^ δ < (p : ℝ) := lt_of_le_of_lt ha_ge_nd hpa
              have hp_y₁ : (p : ℝ) ≤ y₁ := le_trans hpb hb_le_y₁
              have hp3 : 3 ≤ p := by
                have : (3 : ℝ) < (p : ℝ) := lt_of_le_of_lt hnd_ge3 hp_nd
                have : 3 < p := by exact_mod_cast this
                omega
              have hpn₁ : p ≤ n₁ := by
                have : (p : ℝ) ≤ (n₁ : ℝ) := le_trans hp_y₁ (le_trans hy₁_le_n₁ (div_le_self hn₁_pos.le (one_le_pow₀ (by linarith))))
                exact_mod_cast this
              have hp_osc : p ∈ I_osc :=
                Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, hpn₁⟩, hpr⟩, hp_nd, hp_y₁⟩
              have hp_not_exc : ¬ isExcised p := by
                rintro (⟨r', hr', hpr'⟩ | ⟨j₀, hj₀, hpj⟩)
                · have hr'_icc := Finset.mem_Icc.mp hr'
                  rcases lt_or_ge r' r with hlt' | hge'
                  · -- r' < r ⇒ r' + 1 ≤ r ⇒ (p : ℝ) ≤ D_hi r ≤ n₁^(1/r) / (log n₁)^A_R ≤ n₁^(1/r') / (log n₁)^A_R = (powCollar r').1
                    have hle : (n₁ : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n₁ : ℝ)) ^ A_R ≤
                        (n₁ : ℝ) ^ (1 / (r' : ℝ)) / (Real.log (n₁ : ℝ)) ^ A_R := by
                      apply div_le_div_of_nonneg_right _ (by positivity)
                      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n₁))
                      exact one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < r')) (by exact_mod_cast le_of_lt hlt')
                    linarith [le_trans hpD.2 (min_le_right _ _), hpr'.1]
                  · -- r ≤ r' ⇒ r' ≥ r. If r' = r: p ≤ D_hi r = (powCollar r).1, contradicting hpr'.1!
                    -- If r' > r: r' ≥ r + 1 ⇒ (powCollar r').2 = n₂^(1/r') ≤ n₂^(1/(r+1)) ≤ D_lo r < p, contradicting hpr'.2!
                    rcases eq_or_lt_of_le hge' with rfl | hgt'
                    · linarith [le_trans hpD.2 (min_le_right _ _), hpr'.1]
                    · have hle : (n₂ : ℝ) ^ (1 / (r' : ℝ)) ≤ (n₂ : ℝ) ^ (1 / ((r : ℝ) + 1)) := by
                        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n₂))
                        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : r + 1 ≤ r'))
                      linarith [lt_of_le_of_lt (le_max_right _ _) hpD.1, hpr'.2]
                · exact Set.disjoint_left.mp (hL_disj (a_m, b_m) hu_mem (resCollar j₀) (hresList_mem j₀ hj₀))
                    ⟨hpa, hpb⟩ hpj
              exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hp_osc, hp_not_exc⟩, hpD.1, hpD.2⟩, hpa, hpb⟩
          -- Dyadic partition of subFin idx on (a_m, b_m]
          have hmem_ab : ∀ p ∈ subFin idx, a_m < (p : ℝ) ∧ (p : ℝ) ≤ b_m := fun p hp => ((hsub_exact p).mp hp).2
          obtain ⟨hpart_dy, hdisj_dy⟩ := dyadic_partition_finset ha_ge1 hlt_ab.le (subFin idx) hmem_ab
          rw [hpart_dy, Finset.sum_biUnion hdisj_dy]
          -- Bound each dyadic block I_k
          have hdy_bd : ∀ k ∈ dyadicBlocks a_m b_m,
              |∑ p ∈ (subFin idx).filter (fun p : ℕ => a_m * (2 : ℝ) ^ k < (p : ℝ) ∧ (p : ℝ) ≤ 2 * (a_m * (2 : ℝ) ^ k)),
                ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
                  (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))| ≤
                (n₁ : ℝ) * (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂)) / (Real.log (n₁ : ℝ)) ^ (R + 2)) := by
            intro k hk
            let P : ℝ := a_m * (2 : ℝ) ^ k
            let I_k := (subFin idx).filter (fun p : ℕ => P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P)
            have hP_ge_am : a_m ≤ P := le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num))
            have hP_lt_bm : P < b_m := (Finset.mem_filter.mp hk).2
            have hP_lo : (n₁ : ℝ) ^ δ ≤ P := le_trans ha_ge_nd hP_ge_am
            have hP_pos : 0 < P := lt_of_lt_of_le (by positivity) hP_lo
            have hP_ge1 : 1 ≤ P := le_trans ha_ge1 hP_ge_am
            have hP_hi : P ≤ (n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ 12 := le_trans (le_trans hP_lt_bm.le hb_le_y₁) hy₁_le_n1_12
            have hIk_pr : ∀ p ∈ I_k, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P := fun p hp =>
              ⟨((hsub_exact p).mp (Finset.mem_filter.mp hp).1).1, (Finset.mem_filter.mp hp).2⟩
            have hIk_sub : IsPrimeSubinterval P I_k := by
              refine isPrimeSubinterval_of_bounds (a := max a_m P) (b := min b_m (2 * P)) hP_pos.le I_k ?_
                (fun p hp => (hIk_pr p hp).2)
              intro p
              simp only [I_k, Finset.mem_filter, hsub_exact, max_lt_iff, le_min_iff]
              tauto
            have hw_bd : ∀ t ∈ Set.Icc P (2 * P), |(1 : ℝ) / t| ≤ 1 / P := fun t ht => by
              rw [abs_of_pos (one_div_pos.mpr (lt_of_lt_of_le hP_pos ht.1))]
              exact one_div_le_one_div_of_le hP_pos ht.1
            have hw_anti : AntitoneOn (fun t : ℝ => 1 / t) (Set.Icc P (2 * P)) :=
              fun s hs t _ hst => one_div_le_one_div_of_le (lt_of_lt_of_le hP_pos hs.1) hst
            -- Exact multi-digit identity on I_k: v_p(n_i!) = ∑ j ∈ Icc 1 r, ⌊n_i / p^j⌋
            have hprod_id : ∀ p ∈ I_k,
                (((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂)) : ℝ) : ℂ) =
                (∏ j ∈ Finset.Icc 1 r, ((-1 : ℂ) ^ Int.floor ((n₁ : ℝ) / (p : ℝ) ^ j))) *
                (∏ j ∈ Finset.Icc 1 r, ((-1 : ℂ) ^ Int.floor ((n₂ : ℝ) / (p : ℝ) ^ j))) := by
              intro p hp
              have hp_pr := (hIk_pr p hp).1
              have hp_sub := (Finset.mem_filter.mp hp).1
              have hp_D := (Finset.mem_filter.mp (Finset.mem_filter.mp hp_sub).1).2
              have hp_gt_n2 : (n₂ : ℝ) ^ (1 / ((r : ℝ) + 1)) < (p : ℝ) := lt_of_le_of_lt (le_max_right _ _) hp_D.1
              have hn₂_lt_p : n₂ < p ^ (r + 1) := by
                have h1 : (n₂ : ℝ) < (p : ℝ) ^ (r + 1) := by
                  calc (n₂ : ℝ) = ((n₂ : ℝ) ^ (1 / ((r : ℝ) + 1))) ^ (r + 1) := by
                        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
                        push_cast; rw [one_div_mul_cancel (by positivity), Real.rpow_one]
                    _ < (p : ℝ) ^ (r + 1) := pow_lt_pow_left₀ hp_gt_n2 (by positivity) (by omega)
                exact_mod_cast h1
              have hv1 := lem63_padicValNat_factorial_eq_sum_Icc hp_pr (lt_trans hlt hn₂_lt_p)
              have hv2 := lem63_padicValNat_factorial_eq_sum_Icc hp_pr hn₂_lt_p
              have hp_pos_r : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pr.pos
              have hfl : ∀ (m j : ℕ), Int.floor ((m : ℝ) / (p : ℝ) ^ j) = ((m / p ^ j : ℕ) : ℤ) := fun m j => by
                rw [Int.floor_eq_iff]; constructor
                · rw [Int.cast_natCast, le_div_iff₀ (pow_pos hp_pos_r j)]
                  exact_mod_cast Nat.div_mul_le_self m (p ^ j)
                · rw [Int.cast_natCast, div_lt_iff₀ (pow_pos hp_pos_r j)]
                  have hlt_nat : m < (m / p ^ j + 1) * p ^ j := by
                    rw [add_mul, one_mul]; exact Nat.lt_div_mul_add (a := m) (pow_pos hp_pr.pos j)
                  exact_mod_cast hlt_nat
              have hsub_prod : ∀ m : ℕ, (((-1 : ℝ) ^ (∑ j ∈ Finset.Icc 1 r, m / p ^ j) : ℝ) : ℂ) =
                  ∏ j ∈ Finset.Icc 1 r, ((-1 : ℂ) ^ Int.floor ((m : ℝ) / (p : ℝ) ^ j)) := fun m => by
                rw [← Finset.prod_pow_eq_pow_sum, Complex.ofReal_prod]
                refine Finset.prod_congr rfl fun j _ => ?_
                rw [hfl m j, zpow_natCast]; push_cast; rfl
              rw [hv1, hv2, pow_add, Complex.ofReal_mul, hsub_prod n₁, hsub_prod n₂]
            -- Split into mainC (product of Psi_tilde) + errC (telescoping error)
            let mainC : ℂ := ∑ p ∈ I_k, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
              ((∏ j ∈ Finset.Icc 1 r, Psi_tilde ((n₁ : ℝ) / (p : ℝ) ^ j)) *
               (∏ j ∈ Finset.Icc 1 r, Psi_tilde ((n₂ : ℝ) / (p : ℝ) ^ j)))
            let errC : ℂ := ∑ p ∈ I_k, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
              ((((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂)) : ℝ) : ℂ) -
               (∏ j ∈ Finset.Icc 1 r, Psi_tilde ((n₁ : ℝ) / (p : ℝ) ^ j)) *
               (∏ j ∈ Finset.Icc 1 r, Psi_tilde ((n₂ : ℝ) / (p : ℝ) ^ j)))
            have hre_split : ∑ p ∈ I_k,
                ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
                  (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ)) = (n₁ : ℝ) * (mainC + errC).re := by
              rw [Complex.add_re, Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [← Complex.add_re, ← mul_add, add_sub_cancel, ← Complex.ofReal_mul, Complex.ofReal_re]
              ring
            -- Bound errC using norm_prod_sub_prod_le and vaaler_btilde_dyadic_sum_bound_inv
            have herrC_bd : ‖errC‖ ≤ L₁ ^ (2 * r) * (2 * (r : ℝ) * (4 + 12 * C₂) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) := by
              have hpw : ∀ p ∈ I_k,
                  ‖(((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂)) : ℝ) : ℂ) -
                    (∏ j ∈ Finset.Icc 1 r, Psi_tilde ((n₁ : ℝ) / (p : ℝ) ^ j)) *
                    (∏ j ∈ Finset.Icc 1 r, Psi_tilde ((n₂ : ℝ) / (p : ℝ) ^ j))‖ ≤
                  L₁ ^ (2 * r) * ((∑ j ∈ Finset.Icc 1 r, (B_tilde ((n₁ : ℝ) / (p : ℝ) ^ j)).re) +
                    (∑ j ∈ Finset.Icc 1 r, (B_tilde ((n₂ : ℝ) / (p : ℝ) ^ j)).re)) := by
                intro p hp
                rw [hprod_id p hp]
                let idxS := (Finset.Icc 1 r).disjSum (Finset.Icc 1 r)
                let f : ℕ ⊕ ℕ → ℂ := Sum.elim
                  (fun j => ((-1 : ℂ) ^ Int.floor ((n₁ : ℝ) / (p : ℝ) ^ j)))
                  (fun j => ((-1 : ℂ) ^ Int.floor ((n₂ : ℝ) / (p : ℝ) ^ j)))
                let g : ℕ ⊕ ℕ → ℂ := Sum.elim
                  (fun j => Psi_tilde ((n₁ : ℝ) / (p : ℝ) ^ j))
                  (fun j => Psi_tilde ((n₂ : ℝ) / (p : ℝ) ^ j))
                have hpf : ∏ x ∈ idxS, f x =
                    (∏ j ∈ Finset.Icc 1 r, ((-1 : ℂ) ^ Int.floor ((n₁ : ℝ) / (p : ℝ) ^ j))) *
                    (∏ j ∈ Finset.Icc 1 r, ((-1 : ℂ) ^ Int.floor ((n₂ : ℝ) / (p : ℝ) ^ j))) := by
                  simp [idxS, f, Finset.prod_disjSum]
                have hpg : ∏ x ∈ idxS, g x =
                    (∏ j ∈ Finset.Icc 1 r, Psi_tilde ((n₁ : ℝ) / (p : ℝ) ^ j)) *
                    (∏ j ∈ Finset.Icc 1 r, Psi_tilde ((n₂ : ℝ) / (p : ℝ) ^ j)) := by
                  simp [idxS, g, Finset.prod_disjSum]
                have hcard : idxS.card = 2 * r := by
                  simp [idxS, Finset.card_disjSum]; omega
                rw [← hpf, ← hpg]
                have h1 := norm_prod_sub_prod_le idxS f g L₁ hL₁_ge1
                  (fun x _ => by
                    cases x <;> simp [f])
                  (fun x _ => by
                    cases x <;> simp [g, hPsi_bd])
                rw [hcard] at h1
                refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ (by positivity))
                simp only [idxS, Finset.sum_disjSum, f, g, Sum.elim_inl, Sum.elim_inr]
                have hvaal : ∀ x : ℝ, ‖((-1 : ℂ) ^ Int.floor x) - Psi_tilde x‖ ≤ (B_tilde x).re := fun x => by
                  have hp := h_vaaler_pw x
                  dsimp only [Psi_tilde, B_tilde, S_H]
                  convert hp using 2 <;>
                    simp only [mul_div_assoc, Complex.ofReal_zpow, Complex.ofReal_neg, Complex.ofReal_one]
                exact add_le_add (Finset.sum_le_sum fun j _ => hvaal _)
                  (Finset.sum_le_sum fun j _ => hvaal _)
              have hB_single : ∀ (m : ℕ), n₁ ≤ m → (m : ℝ) ≤ 2 * (n₁ : ℝ) → ∀ j ∈ Finset.Icc 1 r,
                  ∑ p ∈ I_k, (Real.log (p : ℝ) / (p : ℝ)) * (B_tilde ((m : ℝ) / (p : ℝ) ^ j)).re ≤
                    (4 + 12 * C₂) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by
                intro m hm hm_ub j hj
                have hj_icc := Finset.mem_Icc.mp hj
                have hBt_eq : ∀ p : ℕ, B_tilde ((m : ℝ) / (p : ℝ) ^ j) =
                    b_tilde 0 + ∑ h' ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0),
                      b_tilde h' * eExp ((h' : ℝ) * ((m : ℝ) / (p : ℝ) ^ j) / 2) := fun p => by
                  dsimp only [B_tilde]
                  have h0m : (0 : ℤ) ∈ Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1) :=
                    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
                  rw [← Finset.add_sum_erase _ _ h0m]
                  congr 1
                  · simp [eExp]
                  · congr 1; ext x; simp [Finset.mem_erase, Finset.mem_filter, and_comm]
                have hBt_re : ∀ p : ℕ, (B_tilde ((m : ℝ) / (p : ℝ) ^ j)).re = (b_tilde 0 + ∑ h' ∈ (Finset.Icc (-(2 * (H : ℤ) + 1)) (2 * (H : ℤ) + 1)).filter (· ≠ 0), b_tilde h' * eExp ((h' : ℝ) * ((m : ℝ) / (p : ℝ) ^ j) / 2)).re := fun p => congrArg Complex.re (hBt_eq p)
                simp_rw [hBt_re]
                have hvb := vaaler_btilde_dyadic_sum_bound_inv H hH_ge1 b_tilde h_btilde0 h_btilde_b
                  n₁ m j P hP_pos (by linarith) I_k hIk_pr C₂ hC₂_pos.le R (fun h' hh' hh'_le => by
                    have hT₀ : (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n₁ : ℝ)) ^ A_R ≤ |(h' : ℝ) * (m : ℝ)| / P ^ j := by
                      have hh'1 : (1 : ℝ) ≤ |(h' : ℝ)| := by exact_mod_cast Int.one_le_abs hh'
                      have hPj : P ^ j ≤ (n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ A_R := by
                        have hP_le : P ≤ (n₁ : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n₁ : ℝ)) ^ A_R :=
                          le_trans hP_lt_bm.le (le_trans hb_le_Dhi (min_le_right _ _))
                        have hP_le1 : P ^ j ≤ ((n₁ : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n₁ : ℝ)) ^ A_R) ^ j :=
                          pow_le_pow_left₀ hP_pos.le hP_le j
                        rw [div_pow] at hP_le1
                        have hnum : ((n₁ : ℝ) ^ (1 / (r : ℝ))) ^ j ≤ (n₁ : ℝ) := by
                          rw [← Real.rpow_natCast, ← Real.rpow_mul hn₁_pos.le]
                          calc (n₁ : ℝ) ^ (1 / (r : ℝ) * (j : ℝ)) ≤ (n₁ : ℝ) ^ (1 : ℝ) := by
                                apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n₁))
                                rw [one_div_mul_eq_div, div_le_one (by exact_mod_cast (by omega : 0 < r))]
                                exact_mod_cast hj_icc.2
                            _ = (n₁ : ℝ) := Real.rpow_one _
                        have hden : (Real.log (n₁ : ℝ)) ^ A_R ≤ ((Real.log (n₁ : ℝ)) ^ A_R) ^ j := by
                          rw [← pow_mul]
                          exact pow_le_pow_right₀ (by linarith) (Nat.le_mul_of_pos_right A_R (by omega))
                        exact le_trans hP_le1 (div_le_div₀ hn₁_pos.le hnum (by positivity) hden)
                      have hdiv : (Real.log (n₁ : ℝ)) ^ A_R ≤ (n₁ : ℝ) / P ^ j := by
                        rw [le_div_iff₀ (pow_pos hP_pos j)]
                        have := (le_div_iff₀ (by positivity : (0 : ℝ) < (Real.log (n₁ : ℝ)) ^ A_R)).mp hPj
                        linarith
                      have h2le : (2 : ℝ) ^ (-(R : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
                      calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n₁ : ℝ)) ^ A_R ≤ 1 * (Real.log (n₁ : ℝ)) ^ A_R := by gcongr
                        _ = (Real.log (n₁ : ℝ)) ^ A_R := one_mul _
                        _ ≤ (n₁ : ℝ) / P ^ j := hdiv
                        _ ≤ (m : ℝ) / P ^ j := by gcongr
                        _ = (1 * (m : ℝ)) / P ^ j := by ring
                        _ ≤ (|(h' : ℝ)| * (m : ℝ)) / P ^ j := by gcongr
                        _ = |(h' : ℝ) * (m : ℝ)| / P ^ j := by rw [abs_mul, abs_of_nonneg (a := (m : ℝ)) (Nat.cast_nonneg m)]
                    have hT₀_le : |(h' : ℝ) * (m : ℝ)| / P ^ j ≤ (n₁ : ℝ) ^ 2 := by
                      have hh'_r : |(h' : ℝ)| ≤ 2 * (H : ℝ) + 1 := by exact_mod_cast hh'_le
                      have hH_le : (H : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (R + 3) := Nat.floor_le (by positivity)
                      have hlog_ge1 : (1 : ℝ) ≤ Real.log (n₁ : ℝ) := by linarith
                      have hc1_le1 : c₁_low ≤ 1 := by
                        unfold c₁_low
                        have hpow_le : (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ)) ≤ 1 :=
                          zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
                        linarith
                      have hRM1 : (1 : ℝ) ≤ (R : ℝ) * Mmax + 1 := by positivity
                      have hlog3_le : 10 * (Real.log (n₁ : ℝ)) ^ (R + 3) ≤ (n₁ : ℝ) ^ δ := by
                        have h1 : (Real.log (n₁ : ℝ)) ^ (R + 3) / (n₁ : ℝ) ^ δ ≤ 1 / 10 := by
                          have h2 : c₁_low / (10 * ((R : ℝ) * Mmax + 1)) ≤ 1 / 10 := by
                            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
                          linarith
                        have h2 := (div_le_iff₀ (Real.rpow_pos_of_pos hn₁_pos δ)).mp h1
                        linarith
                      have hnd_le : (n₁ : ℝ) ^ δ ≤ (n₁ : ℝ) := by
                        calc (n₁ : ℝ) ^ δ ≤ (n₁ : ℝ) ^ (1 : ℝ) :=
                              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n₁)) (by linarith)
                          _ = (n₁ : ℝ) := Real.rpow_one _
                      have hh'_le_half : |(h' : ℝ)| * 2 ≤ (n₁ : ℝ) := by
                        have h1 : (1 : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (R + 3) := one_le_pow₀ hlog_ge1
                        linarith
                      have hPj_ge1 : (1 : ℝ) ≤ P ^ j := one_le_pow₀ hP_ge1
                      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
                      calc |(h' : ℝ)| * (m : ℝ) / P ^ j ≤ |(h' : ℝ)| * (m : ℝ) := div_le_self (by positivity) hPj_ge1
                        _ ≤ |(h' : ℝ)| * (2 * (n₁ : ℝ)) := mul_le_mul_of_nonneg_left hm_ub (abs_nonneg _)
                        _ = (|(h' : ℝ)| * 2) * (n₁ : ℝ) := by ring
                        _ ≤ (n₁ : ℝ) * (n₁ : ℝ) := mul_le_mul_of_nonneg_right hh'_le_half hn₁_pos.le
                        _ = (n₁ : ℝ) ^ 2 := (sq _).symm
                    have hres := hGen P I_k {j} (fun _ => (h' : ℝ) * (m : ℝ)) j (fun t => 1 / t) (1 / P)
                      hP_lo hP_hi hIk_sub (fun s hs => by rw [Finset.mem_singleton.mp hs]; omega)
                      (Finset.mem_singleton_self j) hT₀ hT₀_le (fun s hs => by simp at hs) hw_bd hw_anti (by positivity)
                    have hcancel : C₂ * (1 / P) * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) =
                        C₂ * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by field_simp [hP_pos.ne']
                    rw [hcancel] at hres; simpa using hres)
                have h4_le : (4 * Real.log (2 * P)) / ((H : ℝ) + 1) ≤ 4 * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by
                  have h2P_le : Real.log (2 * P) ≤ Real.log (n₁ : ℝ) := by
                    apply Real.log_le_log (by positivity)
                    have hpow12 : (2 : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ 12 := le_trans (by linarith) (pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ 12))
                    calc 2 * P ≤ 2 * ((n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ 12) := by gcongr
                      _ ≤ (Real.log (n₁ : ℝ)) ^ 12 * ((n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ 12) := by gcongr
                      _ = (n₁ : ℝ) := mul_div_cancel₀ _ (by positivity)
                  have hH1 : (Real.log (n₁ : ℝ)) ^ (R + 3) ≤ (H : ℝ) + 1 := (Nat.lt_floor_add_one _).le
                  have h1 : (4 * Real.log (2 * P)) / ((H : ℝ) + 1) ≤
                      (4 * Real.log (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ (R + 3) :=
                    div_le_div₀ (by positivity) (by gcongr) (by positivity) hH1
                  have h2 : (4 * Real.log (n₁ : ℝ)) / (Real.log (n₁ : ℝ)) ^ (R + 3) =
                      4 * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by
                    rw [Real.rpow_neg hlog_pos.le, show ((R : ℝ) + 2) = ((R + 2 : ℕ) : ℝ) by push_cast; ring,
                      Real.rpow_natCast, show R + 3 = (R + 2) + 1 by omega, pow_succ]
                    field_simp [hlog_pos.ne']
                  exact h2 ▸ h1
                linarith
              calc ‖errC‖ ≤ ∑ p ∈ I_k, ‖((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) * _‖ := norm_sum_le _ _
                _ ≤ ∑ p ∈ I_k, (Real.log (p : ℝ) / (p : ℝ)) *
                    (L₁ ^ (2 * r) * ((∑ j ∈ Finset.Icc 1 r, (B_tilde ((n₁ : ℝ) / (p : ℝ) ^ j)).re) +
                      (∑ j ∈ Finset.Icc 1 r, (B_tilde ((n₂ : ℝ) / (p : ℝ) ^ j)).re))) := by
                    apply Finset.sum_le_sum; intro p hp
                    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                      abs_of_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast (hIk_pr p hp).1.one_lt.le)) (Nat.cast_nonneg p))]
                    exact mul_le_mul_of_nonneg_left (hpw p hp) (by positivity)
                _ = L₁ ^ (2 * r) * ((∑ j ∈ Finset.Icc 1 r, ∑ p ∈ I_k, (Real.log (p : ℝ) / (p : ℝ)) * (B_tilde ((n₁ : ℝ) / (p : ℝ) ^ j)).re) +
                    (∑ j ∈ Finset.Icc 1 r, ∑ p ∈ I_k, (Real.log (p : ℝ) / (p : ℝ)) * (B_tilde ((n₂ : ℝ) / (p : ℝ) ^ j)).re)) := by
                    simp_rw [← mul_assoc, mul_comm (Real.log _ / _) (L₁ ^ (2 * r)), mul_assoc]
                    rw [← Finset.mul_sum]
                    congr 1
                    simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
                    rw [Finset.sum_comm, Finset.sum_comm (s := I_k)]
                _ ≤ L₁ ^ (2 * r) * (2 * (r : ℝ) * (4 + 12 * C₂) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) := by
                    apply mul_le_mul_of_nonneg_left _ (by positivity)
                    have h1 := Finset.sum_le_sum (fun j hj => hB_single n₁ le_rfl (by linarith) j hj)
                    have h2 := Finset.sum_le_sum (fun j hj => hB_single n₂ hlt.le hn₂_lt_2n₁.le j hj)
                    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h1 h2
                    have hcard : ((r + 1 - 1 : ℕ) : ℝ) = (r : ℝ) := by simp
                    rw [hcard] at h1 h2
                    linarith
            -- Bound mainC using prime_exp_sum_bounds_general_phase
            have hmainC_bd : ‖mainC‖ ≤ L₁ ^ (2 * r) * (C₂ * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) := by
              -- Expand product of Psi_tilde over Finset.Icc 1 r
              let A := Finset.Icc 1 r
              let PiSet := Fintype.piFinset (fun _ : A => S_H)
              have hexp_main : mainC = ∑ f₁ ∈ PiSet, ∑ f₂ ∈ PiSet,
                  ((∏ j : A, c_tilde (f₁ j)) * (∏ j : A, c_tilde (f₂ j))) *
                  ∑ p ∈ I_k, ((1 / (p : ℝ)) * Real.log (p : ℝ) : ℂ) *
                    eExp (∑ j ∈ A, (if hj : j ∈ A then (((f₁ ⟨j, hj⟩ : ℝ) + (f₂ ⟨j, hj⟩ : ℝ)) * (n₁ : ℝ) + (f₂ ⟨j, hj⟩ : ℝ) * (h : ℝ)) else 0) / (2 * (p : ℝ) ^ j)) := by
                dsimp only [mainC, Psi_tilde]
                calc ∑ p ∈ I_k, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
                      ((∏ j ∈ A, ∑ m ∈ S_H, c_tilde m * eExp ((m : ℝ) * ((n₁ : ℝ) / (p : ℝ) ^ j) / 2)) *
                       (∏ j ∈ A, ∑ m ∈ S_H, c_tilde m * eExp ((m : ℝ) * ((n₂ : ℝ) / (p : ℝ) ^ j) / 2)))
                    = ∑ p ∈ I_k, ∑ f₁ ∈ PiSet, ∑ f₂ ∈ PiSet,
                        ((1 / (p : ℝ)) * Real.log (p : ℝ) : ℂ) *
                        (((∏ j : A, c_tilde (f₁ j)) * (∏ j : A, c_tilde (f₂ j))) *
                          eExp (∑ j ∈ A, (if hj : j ∈ A then (((f₁ ⟨j, hj⟩ : ℝ) + (f₂ ⟨j, hj⟩ : ℝ)) * (n₁ : ℝ) + (f₂ ⟨j, hj⟩ : ℝ) * (h : ℝ)) else 0) / (2 * (p : ℝ) ^ j))) := by
                      refine Finset.sum_congr rfl fun p _ => ?_
                      have hp1 : (∏ j ∈ A, ∑ m ∈ S_H, c_tilde m * eExp ((m : ℝ) * ((n₁ : ℝ) / (p : ℝ) ^ j) / 2)) =
                          ∑ f₁ ∈ PiSet, ∏ j : A, (c_tilde (f₁ j) * eExp ((f₁ j : ℝ) * ((n₁ : ℝ) / (p : ℝ) ^ (j : ℕ)) / 2)) := by
                        rw [← Finset.prod_coe_sort A]; exact prod_sum_piFinset (fun _ : A => S_H) _
                      have hp2 : (∏ j ∈ A, ∑ m ∈ S_H, c_tilde m * eExp ((m : ℝ) * ((n₂ : ℝ) / (p : ℝ) ^ j) / 2)) =
                          ∑ f₂ ∈ PiSet, ∏ j : A, (c_tilde (f₂ j) * eExp ((f₂ j : ℝ) * ((n₂ : ℝ) / (p : ℝ) ^ (j : ℕ)) / 2)) := by
                        rw [← Finset.prod_coe_sort A]; exact prod_sum_piFinset (fun _ : A => S_H) _
                      rw [hp1, hp2, Finset.sum_mul, Finset.mul_sum]
                      refine Finset.sum_congr rfl fun f₁ _ => ?_
                      rw [Finset.mul_sum, Finset.mul_sum]
                      refine Finset.sum_congr rfl fun f₂ _ => ?_
                      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
                      have he_eq : (∏ j : A, eExp ((f₁ j : ℝ) * ((n₁ : ℝ) / (p : ℝ) ^ (j : ℕ)) / 2)) *
                          (∏ j : A, eExp ((f₂ j : ℝ) * ((n₂ : ℝ) / (p : ℝ) ^ (j : ℕ)) / 2)) =
                          eExp (∑ j ∈ A, (if hj : j ∈ A then (((f₁ ⟨j, hj⟩ : ℝ) + (f₂ ⟨j, hj⟩ : ℝ)) * (n₁ : ℝ) + (f₂ ⟨j, hj⟩ : ℝ) * (h : ℝ)) else 0) / (2 * (p : ℝ) ^ j)) := by
                        rw [← Finset.prod_mul_distrib]
                        unfold eExp
                        simp_rw [← Complex.exp_add]
                        rw [← Complex.exp_sum]
                        congr 1
                        rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_coe_sort A]
                        push_cast
                        refine Finset.sum_congr rfl fun j _ => ?_
                        have hn₂_eqC : (n₂ : ℂ) = (n₁ : ℂ) + (h : ℂ) := by exact_mod_cast (by omega : n₂ = n₁ + h)
                        simp only [j.2, ↓reduceDIte, hn₂_eqC]
                        push_cast; ring
                      have hw_eq : ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) = ((1 / (p : ℝ)) * Real.log (p : ℝ) : ℂ) := by
                        push_cast; ring
                      rw [hw_eq, ← he_eq]; ring
                  _ = ∑ f₁ ∈ PiSet, ∑ f₂ ∈ PiSet,
                        ((∏ j : A, c_tilde (f₁ j)) * (∏ j : A, c_tilde (f₂ j))) *
                        ∑ p ∈ I_k, ((1 / (p : ℝ)) * Real.log (p : ℝ) : ℂ) *
                          eExp (∑ j ∈ A, (if hj : j ∈ A then (((f₁ ⟨j, hj⟩ : ℝ) + (f₂ ⟨j, hj⟩ : ℝ)) * (n₁ : ℝ) + (f₂ ⟨j, hj⟩ : ℝ) * (h : ℝ)) else 0) / (2 * (p : ℝ) ^ j)) := by
                      rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl fun f₁ _ => ?_
                      rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl fun f₂ _ => ?_
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl fun p _ => by ring
              rw [hexp_main]
              -- Bound each (f₁, f₂) inner sum by C₂ * (log n₁)^(-(R+2))
              have hinner : ∀ f₁ ∈ PiSet, ∀ f₂ ∈ PiSet,
                  ‖∑ p ∈ I_k, ((1 / (p : ℝ)) * Real.log (p : ℝ) : ℂ) *
                    eExp (∑ j ∈ A, (if hj : j ∈ A then (((f₁ ⟨j, hj⟩ : ℝ) + (f₂ ⟨j, hj⟩ : ℝ)) * (n₁ : ℝ) + (f₂ ⟨j, hj⟩ : ℝ) * (h : ℝ)) else 0) / (2 * (p : ℝ) ^ j))‖ ≤
                    C₂ * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by
                intro f₁ hf₁ f₂ hf₂
                let M : ℕ → ℝ := fun j =>
                  if hj : j ∈ A then (((f₁ ⟨j, hj⟩ : ℝ) + (f₂ ⟨j, hj⟩ : ℝ)) * (n₁ : ℝ) + (f₂ ⟨j, hj⟩ : ℝ) * (h : ℝ)) else 0
                have hf_bd : ∀ (f : A → ℤ), f ∈ PiSet → ∀ j : A, |((f j : ℤ) : ℝ)| ≤ 2 * (H : ℝ) + 1 ∧ f j ≠ 0 ∧ Odd (f j) := by
                  intro f hf j
                  have hm := Finset.mem_filter.mp (Fintype.mem_piFinset.mp hf j)
                  have hicc := Finset.mem_Icc.mp hm.1
                  exact ⟨by exact_mod_cast abs_le.mpr hicc, hm.2.1, hm.2.2⟩
                have hM_nz_lb : ∀ j : A, f₁ j + f₂ j ≠ 0 → (n₁ : ℝ) ≤ |M j| := by
                  intro j hne
                  have h1 := (hf_bd f₁ hf₁ j).2.2
                  have h2 := (hf_bd f₂ hf₂ j).2.2
                  have hev : Even (f₁ j + f₂ j) := h1.add_odd h2
                  have hge2 : (2 : ℝ) ≤ |(f₁ j : ℝ) + (f₂ j : ℝ)| := by
                    obtain ⟨k, hk⟩ := hev
                    have hk_ne : k ≠ 0 := by omega
                    have : (2 : ℤ) ≤ |f₁ j + f₂ j| := by
                      rw [hk]
                      rcases lt_or_gt_of_ne hk_ne with hlt' | hgt'
                      · rw [abs_of_neg (by omega)]; omega
                      · rw [abs_of_pos (by omega)]; omega
                    exact_mod_cast this
                  have hf2_le : |(f₂ j : ℝ)| ≤ 2 * (H : ℝ) + 1 := (hf_bd f₂ hf₂ j).1
                  have hH_le : (H : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (R + 3) := Nat.floor_le (by positivity)
                  have h2H_h : (2 * (H : ℝ) + 1) * (h : ℝ) ≤ (n₁ : ℝ) := by
                    have hpow : 2 * (H : ℝ) + 1 ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 4) := by
                      have h1 : (Real.log (n₁ : ℝ)) ^ (R + 3) ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 3) :=
                        pow_le_pow_right₀ (by linarith) (by unfold A_R; omega)
                      have h2 : (Real.log (n₁ : ℝ)) ^ (A_R + 4) = Real.log (n₁ : ℝ) * (Real.log (n₁ : ℝ)) ^ (A_R + 3) := by
                        rw [pow_succ']
                      have h3 : (1 : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 3) := one_le_pow₀ (by linarith)
                      nlinarith
                    calc (2 * (H : ℝ) + 1) * (h : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 4) * ((n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 4)) := by gcongr
                      _ = (n₁ : ℝ) := mul_div_cancel₀ _ (by positivity)
                  dsimp only [M]; rw [dif_pos j.2]
                  have hrev := abs_sub_abs_le_abs_add (((f₁ j : ℝ) + (f₂ j : ℝ)) * (n₁ : ℝ)) ((f₂ j : ℝ) * (h : ℝ))
                  rw [abs_mul, abs_mul, abs_of_pos hn₁_pos, abs_of_pos hh_pos] at hrev
                  nlinarith only [hrev, hge2, hf2_le, h2H_h, hn₁_pos, hh_pos]
                have hM_ub : ∀ j : A, |M j| ≤ 10 * (Real.log (n₁ : ℝ)) ^ (R + 3) * (n₁ : ℝ) := by
                  intro j
                  dsimp only [M]; rw [dif_pos j.2]
                  have h1 := (hf_bd f₁ hf₁ j).1
                  have h2 := (hf_bd f₂ hf₂ j).1
                  have hH_le : (H : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (R + 3) := Nat.floor_le (by positivity)
                  have h1_le : (1 : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (R + 3) := one_le_pow₀ (by linarith)
                  calc |((f₁ j : ℝ) + (f₂ j : ℝ)) * (n₁ : ℝ) + (f₂ j : ℝ) * (h : ℝ)|
                      ≤ |((f₁ j : ℝ) + (f₂ j : ℝ)) * (n₁ : ℝ)| + |(f₂ j : ℝ) * (h : ℝ)| := abs_add_le _ _
                    _ ≤ (|(f₁ j : ℝ)| + |(f₂ j : ℝ)|) * (n₁ : ℝ) + |(f₂ j : ℝ)| * (n₁ : ℝ) := by
                        rw [abs_mul, abs_mul, abs_of_pos hn₁_pos, abs_of_pos hh_pos]
                        gcongr
                        exact abs_add_le _ _
                    _ ≤ (6 * (H : ℝ) + 3) * (n₁ : ℝ) := by nlinarith only [h1, h2, hn₁_pos]
                    _ ≤ 10 * (Real.log (n₁ : ℝ)) ^ (R + 3) * (n₁ : ℝ) := by nlinarith only [hH_le, h1_le, hn₁_pos]
                have hM_z_ub : ∀ j : A, f₁ j + f₂ j = 0 → |M j| ≤ 3 * (Real.log (n₁ : ℝ)) ^ (R + 3) * (h : ℝ) := by
                  intro j hz
                  dsimp only [M]; rw [dif_pos j.2]
                  have hzr : (f₁ j : ℝ) + (f₂ j : ℝ) = 0 := by exact_mod_cast hz
                  rw [hzr, zero_mul, zero_add, abs_mul, abs_of_pos hh_pos]
                  have h2 := (hf_bd f₂ hf₂ j).1
                  have hH_le : (H : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (R + 3) := Nat.floor_le (by positivity)
                  have h1_le : (1 : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (R + 3) := one_le_pow₀ (by linarith)
                  nlinarith only [h2, hH_le, h1_le, hh_pos]
                have hM_z_lb : ∀ j : A, f₁ j + f₂ j = 0 → (h : ℝ) ≤ |M j| := by
                  intro j hz
                  dsimp only [M]; rw [dif_pos j.2]
                  have hzr : (f₁ j : ℝ) + (f₂ j : ℝ) = 0 := by exact_mod_cast hz
                  rw [hzr, zero_mul, zero_add, abs_mul, abs_of_pos hh_pos]
                  have h1 : (1 : ℝ) ≤ |(f₂ j : ℝ)| := by exact_mod_cast Int.one_le_abs (hf_bd f₂ hf₂ j).2.1
                  nlinarith only [h1, hh_pos]
                have hPj_lb : ∀ j ∈ A, (Real.log (n₁ : ℝ)) ^ A_R ≤ (n₁ : ℝ) / P ^ j := by
                  intro j hj
                  have hj_icc := Finset.mem_Icc.mp hj
                  have hP_le : P ≤ (n₁ : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n₁ : ℝ)) ^ A_R :=
                    le_trans hP_lt_bm.le (le_trans hb_le_Dhi (min_le_right _ _))
                  have hP_le1 : P ^ j ≤ ((n₁ : ℝ) ^ (1 / (r : ℝ)) / (Real.log (n₁ : ℝ)) ^ A_R) ^ j :=
                    pow_le_pow_left₀ hP_pos.le hP_le j
                  rw [div_pow] at hP_le1
                  have hnum : ((n₁ : ℝ) ^ (1 / (r : ℝ))) ^ j ≤ (n₁ : ℝ) := by
                    rw [← Real.rpow_natCast, ← Real.rpow_mul hn₁_pos.le]
                    calc (n₁ : ℝ) ^ (1 / (r : ℝ) * (j : ℝ)) ≤ (n₁ : ℝ) ^ (1 : ℝ) := by
                          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n₁))
                          rw [one_div_mul_eq_div, div_le_one (by exact_mod_cast (by omega : 0 < r))]
                          exact_mod_cast hj_icc.2
                      _ = (n₁ : ℝ) := Real.rpow_one _
                  have hden : (Real.log (n₁ : ℝ)) ^ A_R ≤ ((Real.log (n₁ : ℝ)) ^ A_R) ^ j := by
                    rw [← pow_mul]
                    exact pow_le_pow_right₀ (by linarith) (Nat.le_mul_of_pos_right A_R (by omega))
                  have hPj : P ^ j ≤ (n₁ : ℝ) / (Real.log (n₁ : ℝ)) ^ A_R :=
                    le_trans hP_le1 (div_le_div₀ hn₁_pos.le hnum (by positivity) hden)
                  rw [le_div_iff₀ (pow_pos hP_pos j)]
                  have := (le_div_iff₀ (by positivity : (0 : ℝ) < (Real.log (n₁ : ℝ)) ^ A_R)).mp hPj
                  linarith
                have hP1_h_lb : (Real.log (n₁ : ℝ)) ^ A_R ≤ (h : ℝ) / P := by
                  have h1 : P ≤ (h : ℝ) / (Real.log (n₁ : ℝ)) ^ (A_R + 2) := le_trans hP_lt_bm.le hb_le_y₁
                  rw [le_div_iff₀ hP_pos]
                  have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < (Real.log (n₁ : ℝ)) ^ (A_R + 2))).mp h1
                  have hpow : (Real.log (n₁ : ℝ)) ^ A_R ≤ (Real.log (n₁ : ℝ)) ^ (A_R + 2) :=
                    pow_le_pow_right₀ (by linarith) (by omega)
                  nlinarith only [h2, hpow, hP_pos]
                have h1A : 1 ∈ A := Finset.mem_Icc.mpr ⟨le_rfl, hr_icc.1⟩
                have h2le : (2 : ℝ) ^ (-(R : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
                have hsmall_d10 : 10 * ((Real.log (n₁ : ℝ)) ^ (R + 3) / (n₁ : ℝ) ^ δ) ≤ c₁_low / ((R : ℝ) * Mmax + 1) := by
                  have hmul := mul_le_mul_of_nonneg_left hsmall_d (by norm_num : (0 : ℝ) ≤ 10)
                  have h10 : 10 * (c₁_low / (10 * ((R : ℝ) * Mmax + 1))) = c₁_low / ((R : ℝ) * Mmax + 1) := by
                    have hden : (R : ℝ) * Mmax + 1 ≠ 0 := by positivity
                    field_simp [hden]
                  linarith
                -- Choose dominant index r₀ ∈ A
                have hDom_exists : ∃ r₀ ∈ A,
                    (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n₁ : ℝ)) ^ A_R ≤ |M r₀| / P ^ r₀ ∧
                    ∀ s ∈ A.erase r₀, |M s| / P ^ s ≤ (c₁_low / ((R : ℝ) * Mmax + 1)) * (|M r₀| / P ^ r₀) := by
                  by_cases h1_nz : f₁ ⟨1, h1A⟩ + f₂ ⟨1, h1A⟩ ≠ 0
                  · refine ⟨1, h1A, ?_, ?_⟩
                    · calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n₁ : ℝ)) ^ A_R ≤ (Real.log (n₁ : ℝ)) ^ A_R :=
                            mul_le_of_le_one_left (by positivity) h2le
                        _ ≤ (n₁ : ℝ) / P ^ 1 := hPj_lb 1 h1A
                        _ ≤ |M 1| / P ^ 1 := div_le_div_of_nonneg_right (hM_nz_lb ⟨1, h1A⟩ h1_nz) (by positivity)
                    · intro s hs
                      have hsA := Finset.mem_of_mem_erase hs
                      have hs_gt1 : 2 ≤ s := by have := Finset.mem_Icc.mp hsA; have := Finset.ne_of_mem_erase hs; omega
                      have hPs : P ^ 2 ≤ P ^ s := pow_le_pow_right₀ hP_ge1 hs_gt1
                      calc |M s| / P ^ s ≤ (10 * (Real.log (n₁ : ℝ)) ^ (R + 3) * (n₁ : ℝ)) / P ^ 2 :=
                            div_le_div₀ (by positivity) (hM_ub ⟨s, hsA⟩) (by positivity) hPs
                        _ = (10 * ((Real.log (n₁ : ℝ)) ^ (R + 3) / P)) * ((n₁ : ℝ) / P ^ 1) := by ring
                        _ ≤ (10 * ((Real.log (n₁ : ℝ)) ^ (R + 3) / (n₁ : ℝ) ^ δ)) * (|M 1| / P ^ 1) := by
                            gcongr
                            exact hM_nz_lb ⟨1, h1A⟩ h1_nz
                        _ ≤ (c₁_low / ((R : ℝ) * Mmax + 1)) * (|M 1| / P ^ 1) := by
                            gcongr
                  · push_neg at h1_nz
                    let S_nz := (Finset.Icc 2 r).filter (fun j : ℕ => ∃ hj : j ∈ A, f₁ ⟨j, hj⟩ + f₂ ⟨j, hj⟩ ≠ 0)
                    by_cases hSnz : S_nz.Nonempty
                    · let j_star := S_nz.min' hSnz
                      have hj_mem := Finset.mem_filter.mp (Finset.min'_mem S_nz hSnz)
                      have hj_icc := Finset.mem_Icc.mp hj_mem.1
                      obtain ⟨hjA, hj_nz⟩ := hj_mem.2
                      have hj_in_2R : j_star ∈ Finset.Icc 2 R := Finset.mem_Icc.mpr ⟨hj_icc.1, le_trans hj_icc.2 hr_icc.2⟩
                      have hdisj_j := hL_disj (a_m, b_m) hu_mem (resCollar j_star) (hresList_mem j_star hj_in_2R)
                      have hcases := disjoint_Ioc_cases hlt_ab (hresList_lt _ (hresList_mem j_star hj_in_2R)) hdisj_j
                      have hj1_pos : (0 : ℝ) < (j_star : ℝ) - 1 := by
                        have : (2 : ℝ) ≤ (j_star : ℝ) := by exact_mod_cast hj_icc.1
                        linarith
                      have hj1_ge1 : 1 ≤ j_star - 1 := by omega
                      rcases hcases with hb_le_c | hd_le_a
                      · -- P < b_m ≤ c_{j_star} ⇒ j_star dominates!
                        have hP_le_c : P ≤ (resCollar j_star).1 := le_trans hP_lt_bm.le hb_le_c
                        have hratio : (h : ℝ) / P ≤ ((n₁ : ℝ) / P ^ j_star) / (Real.log (n₁ : ℝ)) ^ (A_R + 6) := by
                          dsimp [resCollar] at hP_le_c
                          have hpow := pow_le_pow_left₀ hP_pos.le hP_le_c (j_star - 1)
                          rw [div_pow, ← Real.rpow_natCast (((n₁ : ℝ) / (h : ℝ)) ^ _), ← Real.rpow_mul (by positivity)] at hpow
                          have hexp1 : 1 / ((j_star : ℝ) - 1) * ((j_star - 1 : ℕ) : ℝ) = 1 := by
                            rw [Nat.cast_sub (by omega : 1 ≤ j_star), Nat.cast_one, one_div_mul_cancel hj1_pos.ne']
                          rw [hexp1, Real.rpow_one] at hpow
                          have hden_ge : (Real.log (n₁ : ℝ)) ^ (A_R + 6) ≤ ((Real.log (n₁ : ℝ)) ^ (A_R + 6)) ^ (j_star - 1) := by
                            rw [← pow_mul]; exact pow_le_pow_right₀ (by linarith) (Nat.le_mul_of_pos_right _ hj1_ge1)
                          have hpow2 : P ^ (j_star - 1) ≤ ((n₁ : ℝ) / (h : ℝ)) / (Real.log (n₁ : ℝ)) ^ (A_R + 6) :=
                            le_trans hpow (div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge)
                          have hPj_eq : P ^ j_star = P * P ^ (j_star - 1) := by
                            conv_lhs => rw [show j_star = 1 + (j_star - 1) by omega, pow_add, pow_one]
                          rw [hPj_eq, div_div, le_div_iff₀ (by positivity)]
                          have := (le_div_iff₀ (by positivity : (0 : ℝ) < (Real.log (n₁ : ℝ)) ^ (A_R + 6))).mp hpow2
                          rw [le_div_iff₀ hh_pos] at this
                          have hstep : (h : ℝ) * (P ^ (j_star - 1) * (Real.log (n₁ : ℝ)) ^ (A_R + 6)) ≤ (n₁ : ℝ) := by linarith
                          calc (h : ℝ) / P * (P * P ^ (j_star - 1) * (Real.log (n₁ : ℝ)) ^ (A_R + 6))
                              = (h : ℝ) * (P ^ (j_star - 1) * (Real.log (n₁ : ℝ)) ^ (A_R + 6)) := by field_simp [hP_pos.ne']
                            _ ≤ (n₁ : ℝ) := hstep
                        refine ⟨j_star, hjA, ?_, ?_⟩
                        · calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n₁ : ℝ)) ^ A_R ≤ (Real.log (n₁ : ℝ)) ^ A_R :=
                                mul_le_of_le_one_left (by positivity) h2le
                            _ ≤ (n₁ : ℝ) / P ^ j_star := hPj_lb j_star hjA
                            _ ≤ |M j_star| / P ^ j_star := div_le_div_of_nonneg_right (hM_nz_lb ⟨j_star, hjA⟩ hj_nz) (by positivity)
                        · intro s hs
                          have hsA := Finset.mem_of_mem_erase hs
                          have hs_ne := Finset.ne_of_mem_erase hs
                          rcases lt_or_gt_of_ne hs_ne with hs_lt | hs_gt
                          · -- s < j_star ⇒ f₁ s + f₂ s = 0
                            have hs_z : f₁ ⟨s, hsA⟩ + f₂ ⟨s, hsA⟩ = 0 := by
                              by_cases hs1 : s = 1
                              · subst hs1; exact h1_nz
                              · by_contra hne
                                have hmem : s ∈ S_nz := Finset.mem_filter.mpr
                                  ⟨Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hsA).1; omega, (Finset.mem_Icc.mp hsA).2⟩, hsA, hne⟩
                                exact absurd (Finset.min'_le S_nz s hmem) (not_le.mpr hs_lt)
                            have hPs1 : P ≤ P ^ s := by
                              conv_lhs => rw [← pow_one P]
                              exact pow_le_pow_right₀ hP_ge1 (Finset.mem_Icc.mp hsA).1
                            calc |M s| / P ^ s ≤ (3 * (Real.log (n₁ : ℝ)) ^ (R + 3) * (h : ℝ)) / P :=
                                  div_le_div₀ (by positivity) (hM_z_ub ⟨s, hsA⟩ hs_z) hP_pos hPs1
                              _ = (3 * (Real.log (n₁ : ℝ)) ^ (R + 3)) * ((h : ℝ) / P) := by ring
                              _ ≤ (3 * (Real.log (n₁ : ℝ)) ^ (R + 3)) * (((n₁ : ℝ) / P ^ j_star) / (Real.log (n₁ : ℝ)) ^ (A_R + 6)) := by gcongr
                              _ = ((3 * (Real.log (n₁ : ℝ)) ^ (R + 3)) / (Real.log (n₁ : ℝ)) ^ (A_R + 6)) * ((n₁ : ℝ) / P ^ j_star) := by ring
                              _ ≤ ((10 * (Real.log (n₁ : ℝ)) ^ (R + 3)) / (Real.log (n₁ : ℝ)) ^ (A_R + 6)) * (|M j_star| / P ^ j_star) := by
                                  gcongr
                                  · linarith [show (0 : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (R + 3) by positivity]
                                  · exact hM_nz_lb ⟨j_star, hjA⟩ hj_nz
                              _ ≤ (c₁_low / ((R : ℝ) * Mmax + 1)) * (|M j_star| / P ^ j_star) := by gcongr
                          · -- s > j_star ⇒ P^s ≥ P * P^j_star
                            have hPs : P * P ^ j_star ≤ P ^ s := by
                              rw [← pow_succ']
                              exact pow_le_pow_right₀ hP_ge1 (by omega)
                            calc |M s| / P ^ s ≤ (10 * (Real.log (n₁ : ℝ)) ^ (R + 3) * (n₁ : ℝ)) / (P * P ^ j_star) :=
                                  div_le_div₀ (by positivity) (hM_ub ⟨s, hsA⟩) (by positivity) hPs
                              _ = (10 * ((Real.log (n₁ : ℝ)) ^ (R + 3) / P)) * ((n₁ : ℝ) / P ^ j_star) := by ring
                              _ ≤ (10 * ((Real.log (n₁ : ℝ)) ^ (R + 3) / (n₁ : ℝ) ^ δ)) * (|M j_star| / P ^ j_star) := by
                                  gcongr; exact hM_nz_lb ⟨j_star, hjA⟩ hj_nz
                              _ ≤ (c₁_low / ((R : ℝ) * Mmax + 1)) * (|M j_star| / P ^ j_star) := by gcongr
                      · -- d_{j_star} ≤ a_m ≤ P ⇒ j = 1 dominates!
                        have hd_le_P : (resCollar j_star).2 ≤ P := le_trans hd_le_a hP_ge_am
                        have hratio : (n₁ : ℝ) / P ^ j_star ≤ ((h : ℝ) / P) / (Real.log (n₁ : ℝ)) ^ (A_R + 6) := by
                          dsimp [resCollar] at hd_le_P
                          have hpow := pow_le_pow_left₀ (by positivity) hd_le_P (j_star - 1)
                          rw [mul_pow, ← Real.rpow_natCast (((n₁ : ℝ) / (h : ℝ)) ^ _), ← Real.rpow_mul (by positivity)] at hpow
                          have hexp1 : 1 / ((j_star : ℝ) - 1) * ((j_star - 1 : ℕ) : ℝ) = 1 := by
                            rw [Nat.cast_sub (by omega : 1 ≤ j_star), Nat.cast_one, one_div_mul_cancel hj1_pos.ne']
                          rw [hexp1, Real.rpow_one] at hpow
                          have hden_ge : (Real.log (n₁ : ℝ)) ^ (A_R + 6) ≤ ((Real.log (n₁ : ℝ)) ^ (A_R + 6)) ^ (j_star - 1) := by
                            rw [← pow_mul]; exact pow_le_pow_right₀ (by linarith) (Nat.le_mul_of_pos_right _ hj1_ge1)
                          have hpow2 : ((n₁ : ℝ) / (h : ℝ)) * (Real.log (n₁ : ℝ)) ^ (A_R + 6) ≤ P ^ (j_star - 1) :=
                            le_trans (mul_le_mul_of_nonneg_left hden_ge (by positivity)) hpow
                          have hPj_eq : P ^ j_star = P * P ^ (j_star - 1) := by
                            conv_lhs => rw [show j_star = 1 + (j_star - 1) by omega, pow_add, pow_one]
                          rw [hPj_eq, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
                          have hstep : (n₁ : ℝ) * (Real.log (n₁ : ℝ)) ^ (A_R + 6) ≤ (h : ℝ) * P ^ (j_star - 1) := by
                            have := mul_le_mul_of_nonneg_left hpow2 hh_pos.le
                            have heq : (h : ℝ) * ((n₁ : ℝ) / (h : ℝ) * (Real.log (n₁ : ℝ)) ^ (A_R + 6)) =
                                (n₁ : ℝ) * (Real.log (n₁ : ℝ)) ^ (A_R + 6) := by field_simp [hh_pos.ne']
                            linarith
                          nlinarith only [hstep, hP_pos]
                        refine ⟨1, h1A, ?_, ?_⟩
                        · calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n₁ : ℝ)) ^ A_R ≤ (Real.log (n₁ : ℝ)) ^ A_R :=
                                mul_le_of_le_one_left (by positivity) h2le
                            _ ≤ (h : ℝ) / P := hP1_h_lb
                            _ = (h : ℝ) / P ^ 1 := by rw [pow_one]
                            _ ≤ |M 1| / P ^ 1 := div_le_div_of_nonneg_right (hM_z_lb ⟨1, h1A⟩ h1_nz) (by positivity)
                        · intro s hs
                          have hsA := Finset.mem_of_mem_erase hs
                          have hs_gt1 : 2 ≤ s := by have := Finset.mem_Icc.mp hsA; have := Finset.ne_of_mem_erase hs; omega
                          rcases lt_or_ge s j_star with hs_lt | hs_ge
                          · have hs_z : f₁ ⟨s, hsA⟩ + f₂ ⟨s, hsA⟩ = 0 := by
                              by_contra hne
                              have hmem : s ∈ S_nz := Finset.mem_filter.mpr
                                ⟨Finset.mem_Icc.mpr ⟨hs_gt1, (Finset.mem_Icc.mp hsA).2⟩, hsA, hne⟩
                              exact absurd (Finset.min'_le S_nz s hmem) (not_le.mpr hs_lt)
                            have hPs : P ^ 2 ≤ P ^ s := pow_le_pow_right₀ hP_ge1 hs_gt1
                            calc |M s| / P ^ s ≤ (3 * (Real.log (n₁ : ℝ)) ^ (R + 3) * (h : ℝ)) / P ^ 2 :=
                                  div_le_div₀ (by positivity) (hM_z_ub ⟨s, hsA⟩ hs_z) (by positivity) hPs
                              _ = (3 * ((Real.log (n₁ : ℝ)) ^ (R + 3) / P)) * ((h : ℝ) / P ^ 1) := by ring
                              _ ≤ (10 * ((Real.log (n₁ : ℝ)) ^ (R + 3) / (n₁ : ℝ) ^ δ)) * (|M 1| / P ^ 1) := by
                                  gcongr
                                  · linarith [show (0 : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (R + 3) / P by positivity]
                                  · exact hM_z_lb ⟨1, h1A⟩ h1_nz
                              _ ≤ (c₁_low / ((R : ℝ) * Mmax + 1)) * (|M 1| / P ^ 1) := by gcongr
                          · have hPs : P ^ j_star ≤ P ^ s := pow_le_pow_right₀ hP_ge1 hs_ge
                            calc |M s| / P ^ s ≤ (10 * (Real.log (n₁ : ℝ)) ^ (R + 3) * (n₁ : ℝ)) / P ^ j_star :=
                                  div_le_div₀ (by positivity) (hM_ub ⟨s, hsA⟩) (by positivity) hPs
                              _ = (10 * (Real.log (n₁ : ℝ)) ^ (R + 3)) * ((n₁ : ℝ) / P ^ j_star) := by ring
                              _ ≤ (10 * (Real.log (n₁ : ℝ)) ^ (R + 3)) * (((h : ℝ) / P) / (Real.log (n₁ : ℝ)) ^ (A_R + 6)) := by gcongr
                              _ = ((10 * (Real.log (n₁ : ℝ)) ^ (R + 3)) / (Real.log (n₁ : ℝ)) ^ (A_R + 6)) * ((h : ℝ) / P ^ 1) := by rw [pow_one]; ring
                              _ ≤ (c₁_low / ((R : ℝ) * Mmax + 1)) * (|M 1| / P ^ 1) := by
                                  gcongr; exact hM_z_lb ⟨1, h1A⟩ h1_nz
                    · -- S_nz = ∅ ⇒ f₁ j + f₂ j = 0 for all j ∈ A ⇒ j = 1 dominates!
                      refine ⟨1, h1A, ?_, ?_⟩
                      · calc (2 : ℝ) ^ (-(R : ℤ)) * (Real.log (n₁ : ℝ)) ^ A_R ≤ (Real.log (n₁ : ℝ)) ^ A_R :=
                              mul_le_of_le_one_left (by positivity) h2le
                          _ ≤ (h : ℝ) / P := hP1_h_lb
                          _ = (h : ℝ) / P ^ 1 := by rw [pow_one]
                          _ ≤ |M 1| / P ^ 1 := div_le_div_of_nonneg_right (hM_z_lb ⟨1, h1A⟩ h1_nz) (by positivity)
                      · intro s hs
                        have hsA := Finset.mem_of_mem_erase hs
                        have hs_gt1 : 2 ≤ s := by have := Finset.mem_Icc.mp hsA; have := Finset.ne_of_mem_erase hs; omega
                        have hs_z : f₁ ⟨s, hsA⟩ + f₂ ⟨s, hsA⟩ = 0 := by
                          by_contra hne
                          exact hSnz ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hs_gt1, (Finset.mem_Icc.mp hsA).2⟩, hsA, hne⟩⟩
                        have hPs : P ^ 2 ≤ P ^ s := pow_le_pow_right₀ hP_ge1 hs_gt1
                        calc |M s| / P ^ s ≤ (3 * (Real.log (n₁ : ℝ)) ^ (R + 3) * (h : ℝ)) / P ^ 2 :=
                              div_le_div₀ (by positivity) (hM_z_ub ⟨s, hsA⟩ hs_z) (by positivity) hPs
                          _ = (3 * ((Real.log (n₁ : ℝ)) ^ (R + 3) / P)) * ((h : ℝ) / P ^ 1) := by ring
                          _ ≤ (10 * ((Real.log (n₁ : ℝ)) ^ (R + 3) / (n₁ : ℝ) ^ δ)) * (|M 1| / P ^ 1) := by
                              gcongr
                              · linarith [show (0 : ℝ) ≤ (Real.log (n₁ : ℝ)) ^ (R + 3) / P by positivity]
                              · exact hM_z_lb ⟨1, h1A⟩ h1_nz
                          _ ≤ (c₁_low / ((R : ℝ) * Mmax + 1)) * (|M 1| / P ^ 1) := by gcongr
                obtain ⟨r₀, hr₀A, hT₀, hDom⟩ := hDom_exists
                have hT₀_le : |M r₀| / P ^ r₀ ≤ (n₁ : ℝ) ^ 2 := by
                  have hc1_le1 : c₁_low ≤ 1 := by
                    unfold c₁_low
                    have hpow_le : (2 : ℝ) ^ (-((R + (5 * R + 2) : ℕ) : ℤ)) ≤ 1 :=
                      zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
                    linarith
                  have hRM1 : (1 : ℝ) ≤ (R : ℝ) * Mmax + 1 := by positivity
                  have hlog3_le : 10 * (Real.log (n₁ : ℝ)) ^ (R + 3) ≤ (n₁ : ℝ) ^ δ := by
                    have h1 : (Real.log (n₁ : ℝ)) ^ (R + 3) / (n₁ : ℝ) ^ δ ≤ 1 / 10 := by
                      have h2 : c₁_low / (10 * ((R : ℝ) * Mmax + 1)) ≤ 1 / 10 := by
                        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
                      linarith
                    have h2 := (div_le_iff₀ (Real.rpow_pos_of_pos hn₁_pos δ)).mp h1
                    linarith
                  have hnd_le : (n₁ : ℝ) ^ δ ≤ (n₁ : ℝ) := by
                    calc (n₁ : ℝ) ^ δ ≤ (n₁ : ℝ) ^ (1 : ℝ) :=
                          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n₁)) (by linarith)
                      _ = (n₁ : ℝ) := Real.rpow_one _
                  have hPr_ge1 : (1 : ℝ) ≤ P ^ r₀ := one_le_pow₀ hP_ge1
                  calc |M r₀| / P ^ r₀ ≤ |M r₀| := div_le_self (abs_nonneg _) hPr_ge1
                    _ ≤ 10 * (Real.log (n₁ : ℝ)) ^ (R + 3) * (n₁ : ℝ) := hM_ub ⟨r₀, hr₀A⟩
                    _ ≤ (n₁ : ℝ) * (n₁ : ℝ) := mul_le_mul_of_nonneg_right (le_trans hlog3_le hnd_le) hn₁_pos.le
                    _ = (n₁ : ℝ) ^ 2 := (sq _).symm
                have hres := hGen P I_k A M r₀ (fun t => 1 / t) (1 / P)
                  hP_lo hP_hi hIk_sub (fun s hs => by have := Finset.mem_Icc.mp hs; omega)
                  hr₀A hT₀ hT₀_le hDom hw_bd hw_anti (by positivity)
                have hcancel : C₂ * (1 / P) * P * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) =
                    C₂ * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) := by field_simp [hP_pos.ne']
                rw [hcancel] at hres; simpa [M] using hres
              calc ‖∑ f₁ ∈ PiSet, ∑ f₂ ∈ PiSet, _‖
                  ≤ ∑ f₁ ∈ PiSet, ‖∑ f₂ ∈ PiSet, _‖ := norm_sum_le _ _
                _ ≤ ∑ f₁ ∈ PiSet, ∑ f₂ ∈ PiSet, ‖((∏ j : A, c_tilde (f₁ j)) * (∏ j : A, c_tilde (f₂ j))) * _‖ :=
                    Finset.sum_le_sum fun f₁ _ => norm_sum_le _ _
                _ ≤ ∑ f₁ ∈ PiSet, ∑ f₂ ∈ PiSet, ((∏ j : A, ‖c_tilde (f₁ j)‖) * (∏ j : A, ‖c_tilde (f₂ j)‖)) *
                      (C₂ * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) := by
                    apply Finset.sum_le_sum; intro f₁ hf₁
                    apply Finset.sum_le_sum; intro f₂ hf₂
                    rw [norm_mul, norm_mul, norm_prod, norm_prod]
                    exact mul_le_mul_of_nonneg_left (hinner f₁ hf₁ f₂ hf₂) (by positivity)
                _ = (∑ f₁ ∈ PiSet, ∏ j : A, ‖c_tilde (f₁ j)‖) * (∑ f₂ ∈ PiSet, ∏ j : A, ‖c_tilde (f₂ j)‖) *
                      (C₂ * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) := by
                    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]; exact Finset.sum_comm
                _ ≤ L₁ ^ (2 * r) * (C₂ * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) := by
                    have hsum_pi : ∑ f ∈ PiSet, ∏ j : A, ‖c_tilde (f j)‖ ≤ L₁ ^ r := by
                      have heq_pi : (∏ _j : A, ∑ m ∈ S_H, ‖c_tilde m‖) = ∑ f ∈ PiSet, ∏ j : A, ‖c_tilde (f j)‖ :=
                        prod_sum_piFinset (fun _ : A => S_H) (fun _ m => ‖c_tilde m‖)
                      rw [← heq_pi]
                      have hcardA : Fintype.card A = r := by simp [A]
                      calc ∏ _j : A, ∑ m ∈ S_H, ‖c_tilde m‖
                          ≤ ∏ _j : A, L₁ := by gcongr; exact le_trans h_L1 hL₁_ge
                        _ = L₁ ^ Fintype.card A := by simp
                        _ = L₁ ^ r := by rw [hcardA]
                    have hsq : (∑ f₁ ∈ PiSet, ∏ j : A, ‖c_tilde (f₁ j)‖) * (∑ f₂ ∈ PiSet, ∏ j : A, ‖c_tilde (f₂ j)‖) ≤ L₁ ^ (2 * r) := by
                      calc _ ≤ L₁ ^ r * L₁ ^ r := mul_le_mul hsum_pi hsum_pi (Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
                        _ = L₁ ^ (2 * r) := by rw [← pow_add, two_mul]
                    gcongr
            -- Combine mainC + errC on I_k
            rw [hre_split, abs_mul, abs_of_pos hn₁_pos]
            have hL_mono : L₁ ^ (2 * r) ≤ L₁ ^ (2 * R) := pow_le_pow_right₀ hL₁_ge1 (by omega)
            have hr_le : (r : ℝ) ≤ (R : ℝ) := by exact_mod_cast hr_icc.2
            have hpow_neg : (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)) = 1 / (Real.log (n₁ : ℝ)) ^ (R + 2) := by
              rw [Real.rpow_neg hlog_pos.le, one_div, show ((R : ℝ) + 2) = ((R + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
            calc (n₁ : ℝ) * |(mainC + errC).re|
                ≤ (n₁ : ℝ) * ‖mainC + errC‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hn₁_pos.le
              _ ≤ (n₁ : ℝ) * (‖mainC‖ + ‖errC‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hn₁_pos.le
              _ ≤ (n₁ : ℝ) * (L₁ ^ (2 * r) * (C₂ * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2))) +
                    L₁ ^ (2 * r) * (2 * (r : ℝ) * (4 + 12 * C₂) * (Real.log (n₁ : ℝ)) ^ (-((R : ℝ) + 2)))) := by gcongr
              _ ≤ (n₁ : ℝ) * (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂)) / (Real.log (n₁ : ℝ)) ^ (R + 2)) := by
                  rw [hpow_neg]
                  have hfac : L₁ ^ (2 * r) * (C₂ * (1 / (Real.log (n₁ : ℝ)) ^ (R + 2))) +
                      L₁ ^ (2 * r) * (2 * (r : ℝ) * (4 + 12 * C₂) * (1 / (Real.log (n₁ : ℝ)) ^ (R + 2))) =
                      L₁ ^ (2 * r) * (C₂ + 2 * (r : ℝ) * (4 + 12 * C₂)) / (Real.log (n₁ : ℝ)) ^ (R + 2) := by ring
                  rw [hfac]; gcongr
          -- Sum over dyadic blocks
          have hcard_dy : ((dyadicBlocks a_m b_m).card : ℝ) ≤ Real.log (n₁ : ℝ) / Real.log 2 + 2 := by
            have h1 := dyadicBlocks_card_le ha_ge1 hlt_ab.le
            have hlog_ba : Real.log (b_m / a_m) ≤ Real.log (n₁ : ℝ) := by
              apply Real.log_le_log (div_pos (by linarith) (by linarith))
              calc b_m / a_m ≤ b_m / 1 := div_le_div_of_nonneg_left (by linarith) (by norm_num) ha_ge1
                _ = b_m := div_one _
                _ ≤ y₁ := hb_le_y₁
                _ ≤ (n₁ : ℝ) := le_trans hy₁_le_n₁ (div_le_self hn₁_pos.le (one_le_pow₀ (by linarith)))
            have : 0 < Real.log 2 := Real.log_pos (by norm_num)
            have hdiv : Real.log (b_m / a_m) / Real.log 2 ≤ Real.log (n₁ : ℝ) / Real.log 2 := by gcongr
            linarith
          calc |∑ k ∈ dyadicBlocks a_m b_m, _|
              ≤ ∑ k ∈ dyadicBlocks a_m b_m, |_| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _k ∈ dyadicBlocks a_m b_m,
                  (n₁ : ℝ) * (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂)) / (Real.log (n₁ : ℝ)) ^ (R + 2)) :=
                Finset.sum_le_sum hdy_bd
            _ = ((dyadicBlocks a_m b_m).card : ℝ) *
                  ((n₁ : ℝ) * (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂)) / (Real.log (n₁ : ℝ)) ^ (R + 2))) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (Real.log (n₁ : ℝ) / Real.log 2 + 2) *
                  ((n₁ : ℝ) * (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂)) / (Real.log (n₁ : ℝ)) ^ (R + 2))) := by
                gcongr
            _ = (n₁ : ℝ) * ((Real.log (n₁ : ℝ) / Real.log 2 + 2) *
                  (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂))) / (Real.log (n₁ : ℝ)) ^ (R + 2)) := by ring
      calc |∑ idx : Fin L_ivs.length, _|
          ≤ ∑ idx : Fin L_ivs.length, |_| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _idx : Fin L_ivs.length,
              (n₁ : ℝ) * ((Real.log (n₁ : ℝ) / Real.log 2 + 2) *
                (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂))) / (Real.log (n₁ : ℝ)) ^ (R + 2)) :=
            Finset.sum_le_sum (fun idx _ => hidx_bd idx)
        _ = (L_ivs.length : ℝ) * ((n₁ : ℝ) * ((Real.log (n₁ : ℝ) / Real.log 2 + 2) *
              (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂))) / (Real.log (n₁ : ℝ)) ^ (R + 2))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ R * ((n₁ : ℝ) * ((Real.log (n₁ : ℝ) / Real.log 2 + 2) *
              (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂))) / (Real.log (n₁ : ℝ)) ^ (R + 2))) := by
            gcongr; exact_mod_cast hL_len
        _ = (n₁ : ℝ) * ((2 : ℝ) ^ R * (Real.log (n₁ : ℝ) / Real.log 2 + 2) *
              (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂))) / (Real.log (n₁ : ℝ)) ^ (R + 2)) := by ring
    -- Sum over r ∈ Icc 1 R
    rw [hI_clean_eq, Finset.sum_biUnion hD_disj]
    calc |∑ r ∈ Finset.Icc 1 R, _|
        ≤ ∑ r ∈ Finset.Icc 1 R, |_| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ Finset.Icc 1 R,
            (n₁ : ℝ) * ((2 : ℝ) ^ R * (Real.log (n₁ : ℝ) / Real.log 2 + 2) *
              (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂))) / (Real.log (n₁ : ℝ)) ^ (R + 2)) :=
          Finset.sum_le_sum hDr_bound
      _ = (R : ℝ) * ((n₁ : ℝ) * ((2 : ℝ) ^ R * (Real.log (n₁ : ℝ) / Real.log 2 + 2) *
            (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂))) / (Real.log (n₁ : ℝ)) ^ (R + 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]; simp
      _ = (n₁ : ℝ) * (((R : ℝ) * (2 : ℝ) ^ R * (Real.log (n₁ : ℝ) / Real.log 2 + 2) *
            (L₁ ^ (2 * R) * (C₂ + 2 * (R : ℝ) * (4 + 12 * C₂)))) / (Real.log (n₁ : ℝ)) ^ (R + 2)) := by ring
      _ ≤ (n₁ : ℝ) * (ε / 16) := mul_le_mul_of_nonneg_left herr_clean.le hn₁_pos.le
      _ ≤ (ε / 8) * (n₁ : ℝ) * Real.log (n₁ : ℝ) := by
          have : 0 ≤ (n₁ : ℝ) * (ε / 16) := by positivity
          nlinarith
  -- Combine Steps 1, 2, 3
  have hpart_exc_clean : I_osc = I_exc ∪ I_clean := by
    ext p; simp only [I_exc, I_clean, Finset.mem_union, Finset.mem_filter]
    by_cases h : isExcised p <;> simp [h]
  have hdisj_exc_clean : Disjoint I_exc I_clean := by
    rw [Finset.disjoint_left]; intro p hp1 hp2
    exact (Finset.mem_filter.mp hp2).2 (Finset.mem_filter.mp hp1).2
  have hsplit_sum : ∑ p ∈ I_osc,
      ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
        (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ)) =
      (∑ p ∈ I_exc, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
        (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))) +
      (∑ p ∈ I_clean, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
        (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))) := by
    rw [hpart_exc_clean, Finset.sum_union hdisj_exc_clean]
  change |∑ p ∈ I_osc,
      ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
        ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ))| ≤
    (ε / 4) * (n₁ : ℝ) * Real.log (n₁ : ℝ)
  have htri1 : |∑ p ∈ I_osc,
      ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
        ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ))| ≤
      |∑ p ∈ I_osc, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
          ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) -
        ∑ p ∈ I_osc, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
          (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))| +
      |∑ p ∈ I_osc, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
          (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))| := by
    simpa [sub_add_cancel] using abs_add_le
      (∑ p ∈ I_osc, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
          ((padicValNat p (Nat.factorial n₁) : ℝ) * Real.log (p : ℝ)) -
        ∑ p ∈ I_osc, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
          (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ)))
      (∑ p ∈ I_osc, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
          (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ)))
  have htri2 : |∑ p ∈ I_osc, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
        (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))| ≤
      |∑ p ∈ I_exc, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
        (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))| +
      |∑ p ∈ I_clean, ((-1 : ℝ) ^ (padicValNat p (Nat.factorial n₁) + padicValNat p (Nat.factorial n₂))) *
        (((n₁ : ℝ) / (p : ℝ)) * Real.log (p : ℝ))| := by
    rw [hsplit_sum]; exact abs_add_le _ _
  linarith only [htri1, htri2, hstep1, hstep2_exc, hstep3_clean]

end GrasGreenbergBrocard
