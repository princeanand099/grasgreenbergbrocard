import Mathlib

/-!
# Section 7.4 Helper Module: Pigeonhole Cluster Reduction & Asymptotic Utilities

Pure `Finset` combinatorics and elementary asymptotic utilities for Theorem 1.3(ii) (eq. 7.17),
with **zero external axioms**:
- `pigeonhole_cluster_reduction`: Pigeonhole Principle modulo `r` reducing solution counts in
  `[N, 2N]` to clusters sharing a single strictly increasing shift tuple `β : Fin d → ℕ`.
- `short_interval_pigeonhole`: Covering `[N, 2N]` by `L` short subintervals.
- `factorial_log_lower`, `factorial_log_diff_upper`, `log_two_lt_one`, `log_four_lt_two`,
  `eventually_mul_log_lt_rpow`, `eventually_linear_lt_half_log`.
-/

open scoped BigOperators
open Real Finset Filter Asymptotics

namespace GrasGreenbergBrocard

/-! ### Section 7.4: Pigeonhole Cluster Reduction (eq. 7.17) -/

/-- **Pigeonhole Cluster Reduction (eq. 7.17)** (proved purely via `Finset` combinatorics):
Given a set `S_sol ⊆ [N, 2N]` of solutions, `d ≥ 1`, `r ≥ 2`, and `d * r ≤ M`, there exists a
strictly increasing shift tuple `β : Fin d → ℕ` with `r ≤ β i ≤ M` and `r ∣ β i` such that
the cluster base-point set `T = {n₀ ∈ S_sol | ∀ i, n₀ - β i ∈ S_sol}` satisfies
`S_sol.card ≤ d * r * (N / M + 1) + (M + 1) ^ d * T.card`. -/
theorem pigeonhole_cluster_reduction {N M d r : ℕ}
    (hM : 1 ≤ M) (hd : 1 ≤ d) (hr : 2 ≤ r) (hdM : d * r ≤ M)
    (S_sol : Finset ℕ) (hS_sub : S_sol ⊆ Finset.Icc N (2 * N)) :
    ∃ (β : Fin d → ℕ),
      (∀ i, r ≤ β i ∧ β i ≤ M ∧ r ∣ β i) ∧
      StrictMono β ∧
      ∃ T : Finset ℕ, T ⊆ S_sol ∧
        (∀ n₀ ∈ T, ∀ i : Fin d, β i ≤ n₀ ∧ n₀ - β i ∈ S_sol) ∧
        S_sol.card ≤ d * r * (N / M + 1) + (M + 1) ^ d * T.card := by
  classical
  let blockOf (n : ℕ) : ℕ := (n - N) / M
  let cell (j c : ℕ) : Finset ℕ := S_sol.filter (fun n => blockOf n = j ∧ n % r = c)
  let isGood (n : ℕ) : Prop :=
    d ≤ ((cell (blockOf n) (n % r)).filter (fun m => m < n)).card
  let S_good : Finset ℕ := S_sol.filter isGood
  let S_bad : Finset ℕ := S_sol.filter (fun n => ¬ isGood n)
  have hpart : S_sol.card = S_bad.card + S_good.card := by
    have := Finset.card_filter_add_card_filter_not (s := S_sol) (p := isGood)
    omega
  have hbad_le : S_bad.card ≤ d * r * (N / M + 1) := by
    let pairs := (Finset.range (N / M + 1)) ×ˢ (Finset.range r)
    have hcov : S_bad ⊆ pairs.biUnion (fun p => (cell p.1 p.2).filter (fun n => ¬ isGood n)) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      have hnIcc := Finset.mem_Icc.mp (hS_sub hn.1)
      rw [Finset.mem_biUnion]
      refine ⟨(blockOf n, n % r), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · rw [Finset.mem_range]
        have hle : n - N ≤ N := by omega
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hle)
      · exact Finset.mem_range.mpr (Nat.mod_lt n (by omega))
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_filter.mpr ⟨hn.1, rfl, rfl⟩, hn.2⟩
    have hcell_bad : ∀ p ∈ pairs,
        ((cell p.1 p.2).filter (fun n => ¬ isGood n)).card ≤ d := by
      intro p _
      set A := (cell p.1 p.2).filter (fun n => ¬ isGood n)
      by_contra hgt
      push Not at hgt
      have hne : A.Nonempty := Finset.card_pos.mp (by omega)
      let n_max := A.max' hne
      have hmax_mem : n_max ∈ A := Finset.max'_mem A hne
      have hmax_cell : n_max ∈ cell p.1 p.2 := (Finset.mem_filter.mp hmax_mem).1
      have hmax_bad : ¬ isGood n_max := (Finset.mem_filter.mp hmax_mem).2
      have hmax_jc : blockOf n_max = p.1 ∧ n_max % r = p.2 := (Finset.mem_filter.mp hmax_cell).2
      have hsub_lt : A.erase n_max ⊆ (cell (blockOf n_max) (n_max % r)).filter (fun m => m < n_max) := by
        intro m hm
        rw [Finset.mem_erase] at hm
        rw [Finset.mem_filter, hmax_jc.1, hmax_jc.2]
        exact ⟨(Finset.mem_filter.mp hm.2).1, lt_of_le_of_ne (Finset.le_max' A m hm.2) hm.1⟩
      have hcard_lt : d ≤ ((cell (blockOf n_max) (n_max % r)).filter (fun m => m < n_max)).card := by
        have h1 := Finset.card_le_card hsub_lt
        rw [Finset.card_erase_of_mem hmax_mem] at h1
        omega
      exact hmax_bad hcard_lt
    calc S_bad.card
        ≤ ∑ p ∈ pairs, ((cell p.1 p.2).filter (fun n => ¬ isGood n)).card :=
          le_trans (Finset.card_le_card hcov) Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ pairs, d := Finset.sum_le_sum hcell_bad
      _ = pairs.card * d := by simp
      _ = d * r * (N / M + 1) := by
          simp only [pairs, Finset.card_product, Finset.card_range]; ring
  have hgood_shift : ∀ n₀ ∈ S_good,
      ∃ β : Fin d → Fin (M + 1),
        (∀ i, r ≤ (β i : ℕ) ∧ (β i : ℕ) ≤ M ∧ r ∣ (β i : ℕ)) ∧
        StrictMono (fun i => (β i : ℕ)) ∧
        (∀ i, (β i : ℕ) ≤ n₀ ∧ n₀ - (β i : ℕ) ∈ S_sol) := by
    intro n₀ hn₀
    have hn₀_sol : n₀ ∈ S_sol := (Finset.mem_filter.mp hn₀).1
    have hn₀_good : d ≤ ((cell (blockOf n₀) (n₀ % r)).filter (fun m => m < n₀)).card :=
      (Finset.mem_filter.mp hn₀).2
    set L_set := (cell (blockOf n₀) (n₀ % r)).filter (fun m => m < n₀)
    let emb : Fin L_set.card ↪o ℕ := L_set.orderEmbOfFin rfl
    have hidx : ∀ i : Fin d, L_set.card - 1 - i.val < L_set.card := fun i => by omega
    have hmem_emb : ∀ i : Fin d, emb ⟨L_set.card - 1 - i.val, hidx i⟩ ∈ L_set :=
      fun i => L_set.orderEmbOfFin_mem rfl ⟨L_set.card - 1 - i.val, hidx i⟩
    have hval_lt : ∀ i : Fin d, emb ⟨L_set.card - 1 - i.val, hidx i⟩ < n₀ :=
      fun i => (Finset.mem_filter.mp (hmem_emb i)).2
    have hval_cell : ∀ i : Fin d, emb ⟨L_set.card - 1 - i.val, hidx i⟩ ∈ cell (blockOf n₀) (n₀ % r) :=
      fun i => (Finset.mem_filter.mp (hmem_emb i)).1
    have hdiff_le : ∀ i : Fin d, n₀ - emb ⟨L_set.card - 1 - i.val, hidx i⟩ ≤ M := by
      intro i
      have hm_blk := (Finset.mem_filter.mp (hval_cell i)).2.1
      have hm_sol := (Finset.mem_filter.mp (hval_cell i)).1
      have hm_ge := (Finset.mem_Icc.mp (hS_sub hm_sol)).1
      have hn_ge := (Finset.mem_Icc.mp (hS_sub hn₀_sol)).1
      dsimp only [blockOf] at hm_blk
      have h1 := Nat.div_add_mod (n₀ - N) M
      have h2 := Nat.div_add_mod (emb ⟨L_set.card - 1 - i.val, hidx i⟩ - N) M
      have h3 := Nat.mod_lt (n₀ - N) (by omega : 0 < M)
      rw [hm_blk] at h2
      omega
    let β : Fin d → Fin (M + 1) := fun i =>
      ⟨n₀ - emb ⟨L_set.card - 1 - i.val, hidx i⟩, Nat.lt_succ_of_le (hdiff_le i)⟩
    refine ⟨β, ?_, ?_, ?_⟩
    · intro i
      have hm_lt := hval_lt i
      have hm_mod := (Finset.mem_filter.mp (hval_cell i)).2.2
      have hdvd : r ∣ (n₀ - emb ⟨L_set.card - 1 - i.val, hidx i⟩) := by
        have h1 := Nat.div_add_mod n₀ r
        have h2 := Nat.div_add_mod (emb ⟨L_set.card - 1 - i.val, hidx i⟩) r
        refine ⟨n₀ / r - emb ⟨L_set.card - 1 - i.val, hidx i⟩ / r, ?_⟩
        rw [Nat.mul_sub_left_distrib]; omega
      have hpos : 0 < n₀ - emb ⟨L_set.card - 1 - i.val, hidx i⟩ := by omega
      have hge_r : r ≤ n₀ - emb ⟨L_set.card - 1 - i.val, hidx i⟩ := Nat.le_of_dvd hpos hdvd
      exact ⟨hge_r, hdiff_le i, hdvd⟩
    · intro i j hij
      dsimp only [β]
      have hlt_idx : (⟨L_set.card - 1 - j.val, hidx j⟩ : Fin L_set.card) <
          ⟨L_set.card - 1 - i.val, hidx i⟩ := by
        change L_set.card - 1 - j.val < L_set.card - 1 - i.val
        omega
      have hemb_lt := emb.strictMono hlt_idx
      have hi_lt := hval_lt i
      have hj_lt := hval_lt j
      omega
    · intro i
      dsimp only [β]
      have hm_lt := hval_lt i
      have hm_sol := (Finset.mem_filter.mp (hval_cell i)).1
      refine ⟨by omega, ?_⟩
      have hsub_eq : n₀ - (n₀ - emb ⟨L_set.card - 1 - i.val, hidx i⟩) =
          emb ⟨L_set.card - 1 - i.val, hidx i⟩ := by omega
      rw [hsub_eq]; exact hm_sol
  by_cases hne : S_good.Nonempty
  · choose f hf_prop hf_mono hf_sol using hgood_shift
    let g : ℕ → (Fin d → Fin (M + 1)) := fun n₀ =>
      if h : n₀ ∈ S_good then f n₀ h else fun _ => ⟨0, by omega⟩
    have hcard_cod : (Finset.univ : Finset (Fin d → Fin (M + 1))).card = (M + 1) ^ d := by
      simp [Fintype.card_fun, Fintype.card_fin]
    have hne_cod : (Finset.univ : Finset (Fin d → Fin (M + 1))).Nonempty :=
      ⟨fun _ => ⟨0, by omega⟩, Finset.mem_univ _⟩
    have hpig : ∃ β_fin : Fin d → Fin (M + 1),
        (S_good.filter (fun n₀ => g n₀ = β_fin)).Nonempty ∧
        S_good.card ≤ (M + 1) ^ d * (S_good.filter (fun n₀ => g n₀ = β_fin)).card := by
      by_contra hall
      push Not at hall
      have hsum_eq : ∑ β_fin : Fin d → Fin (M + 1), (S_good.filter (fun n₀ => g n₀ = β_fin)).card =
          S_good.card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext n₀; simp
        · intro a _ b _ hab
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro x hxa hxb
          exact hab ((Finset.mem_filter.mp hxa).2.symm.trans (Finset.mem_filter.mp hxb).2)
      obtain ⟨β_max, _, hβ_max⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin d → Fin (M + 1)))
        (fun β_fin => (S_good.filter (fun n₀ => g n₀ = β_fin)).card) hne_cod
      have hsum_le : S_good.card ≤ (M + 1) ^ d * (S_good.filter (fun n₀ => g n₀ = β_max)).card := by
        calc S_good.card
            = ∑ β_fin : Fin d → Fin (M + 1), (S_good.filter (fun n₀ => g n₀ = β_fin)).card := hsum_eq.symm
          _ ≤ ∑ _β_fin : Fin d → Fin (M + 1), (S_good.filter (fun n₀ => g n₀ = β_max)).card :=
              Finset.sum_le_sum (fun b hb => hβ_max b hb)
          _ = (M + 1) ^ d * (S_good.filter (fun n₀ => g n₀ = β_max)).card := by
              rw [Finset.sum_const, hcard_cod, smul_eq_mul]
      have hpos_max : (S_good.filter (fun n₀ => g n₀ = β_max)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        rw [hemp, Finset.card_empty, mul_zero] at hsum_le
        have := Finset.card_pos.mpr hne
        omega
      exact not_le_of_gt (hall β_max hpos_max) hsum_le
    obtain ⟨β_fin, ⟨n_rep, hn_rep⟩, hcard_ge⟩ := hpig
    have hn_rep_good : n_rep ∈ S_good := (Finset.mem_filter.mp hn_rep).1
    have hn_rep_eq : f n_rep hn_rep_good = β_fin := by
      have h1 := (Finset.mem_filter.mp hn_rep).2
      dsimp only [g] at h1
      rw [dif_pos hn_rep_good] at h1
      exact h1
    refine ⟨fun i => (β_fin i : ℕ), ?_, ?_, S_good.filter (fun n₀ => g n₀ = β_fin), ?_, ?_, ?_⟩
    · rw [← hn_rep_eq]; exact hf_prop n_rep hn_rep_good
    · rw [← hn_rep_eq]; exact hf_mono n_rep hn_rep_good
    · intro x hx; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
    · intro n₀ hn₀ i
      have hn₀_good : n₀ ∈ S_good := (Finset.mem_filter.mp hn₀).1
      have hgeq : f n₀ hn₀_good = β_fin := by
        have h1 := (Finset.mem_filter.mp hn₀).2
        dsimp only [g] at h1
        rw [dif_pos hn₀_good] at h1
        exact h1
      rw [← hgeq]
      exact hf_sol n₀ hn₀_good i
    · omega
  · have hgood0 : S_good.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    refine ⟨fun i => (i.val + 1) * r, ?_, ?_, ∅, Finset.empty_subset _, ?_, ?_⟩
    · intro i
      refine ⟨?_, ?_, dvd_mul_left r _⟩
      · exact Nat.le_mul_of_pos_left r (Nat.succ_pos i.val)
      · exact le_trans (Nat.mul_le_mul_right r (Nat.succ_le_of_lt i.isLt)) hdM
    · intro i j hij
      exact Nat.mul_lt_mul_of_pos_right (Nat.succ_lt_succ hij) (by omega)
    · intro n₀ hn₀; exact absurd hn₀ (Finset.notMem_empty n₀)
    · simp only [Finset.card_empty, mul_zero, add_zero]; omega

/-- **Short-Interval Pigeonhole**: Covering `[N, 2N]` by `L ≥ 1` consecutive intervals of width
`step = N / L + 1`, some subinterval `[N', N' + step]` captures at least `|T| / L` elements of `T`. -/
lemma short_interval_pigeonhole {N L : ℕ} (hL : 1 ≤ L)
    (T : Finset ℕ) (hT : T ⊆ Finset.Icc N (2 * N)) :
    let step := N / L + 1
    ∃ N' : ℕ, N ≤ N' ∧ N' ≤ 2 * N ∧
      ∃ T' : Finset ℕ, T' ⊆ T ∧ (∀ n ∈ T', N' ≤ n ∧ n ≤ N' + step) ∧
        T.card ≤ L * T'.card := by
  intro step
  let f : ℕ → Fin L := fun n =>
    ⟨min (L - 1) ((n - N) / step), by omega⟩
  have hsum : ∑ j : Fin L, (T.filter (fun n => f n = j)).card = T.card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext n; simp
    · intro a _ b _ hab
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hxa hxb
      exact hab ((Finset.mem_filter.mp hxa).2.symm.trans (Finset.mem_filter.mp hxb).2)
  have hneL : (Finset.univ : Finset (Fin L)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨j_max, _, hj_max⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin L))
    (fun j => (T.filter (fun n => f n = j)).card) hneL
  have hcard_le : T.card ≤ L * (T.filter (fun n => f n = j_max)).card := by
    calc T.card
        = ∑ j : Fin L, (T.filter (fun n => f n = j)).card := hsum.symm
      _ ≤ ∑ _j : Fin L, (T.filter (fun n => f n = j_max)).card :=
          Finset.sum_le_sum (fun j hj => hj_max j hj)
      _ = L * (T.filter (fun n => f n = j_max)).card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  let N' := min (2 * N) (N + j_max.val * step)
  refine ⟨N', ?_, min_le_left _ _, T.filter (fun n => f n = j_max), Finset.filter_subset _ _, ?_, hcard_le⟩
  · exact le_min (by omega) (Nat.le_add_right N _)
  · intro n hn
    have hnIcc := Finset.mem_Icc.mp (hT (Finset.mem_filter.mp hn).1)
    have hfeq : min (L - 1) ((n - N) / step) = j_max.val :=
      congrArg Fin.val (Finset.mem_filter.mp hn).2
    have hdiv_lt : (n - N) / step < L := by
      have h1 : n - N ≤ N := by omega
      have h2 : N < step * L := by
        have hdm := Nat.div_add_mod N L
        have hml := Nat.mod_lt N (by omega : 0 < L)
        dsimp only [step]; nlinarith
      exact Nat.div_lt_of_lt_mul (lt_of_le_of_lt h1 h2)
    have hmin_eq : min (L - 1) ((n - N) / step) = (n - N) / step := min_eq_right (by omega)
    rw [hmin_eq] at hfeq
    have hstep_pos : 0 < step := Nat.succ_pos _
    have hdm := Nat.div_add_mod (n - N) step
    have hml := Nat.mod_lt (n - N) hstep_pos
    have hlo : N + j_max.val * step ≤ n := by
      have : j_max.val * step = step * ((n - N) / step) := by rw [hfeq, mul_comm]
      omega
    have hhi : n ≤ N + j_max.val * step + step := by
      have : j_max.val * step = step * ((n - N) / step) := by rw [hfeq, mul_comm]
      omega
    have hN'_eq : N' = N + j_max.val * step := min_eq_right (by omega)
    rw [hN'_eq]
    exact ⟨hlo, hhi⟩

/-- Elementary factorial lower bound: for `n ≥ 4`, `(n / 2 : ℝ) * log (n / 2 : ℝ) ≤ log (n!)`. -/
lemma factorial_log_lower {n : ℕ} (hn : 4 ≤ n) :
    ((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ) ≤ Real.log ((Nat.factorial n : ℕ) : ℝ) := by
  have hpow : (n / 2) ^ (n / 2) ≤ Nat.factorial n := by
    have hprod_le : (n / 2) ^ (n / 2) ≤ ∏ k ∈ Finset.range (n / 2), (n / 2 + 1 + k) := by
      calc (n / 2) ^ (n / 2)
          = ∏ _k ∈ Finset.range (n / 2), (n / 2) := by simp
        _ ≤ ∏ k ∈ Finset.range (n / 2), (n / 2 + 1 + k) :=
            Finset.prod_le_prod' (fun k _ => by omega)
    have hprod_dvd : ∏ k ∈ Finset.range (n / 2), (n / 2 + 1 + k) ≤ Nat.factorial n := by
      have hfac_eq : ∀ a b : ℕ, Nat.factorial a * (∏ k ∈ Finset.range b, (a + 1 + k)) =
          Nat.factorial (a + b) := by
        intro a b
        induction b with
        | zero => simp
        | succ b ih =>
          rw [Finset.prod_range_succ, ← mul_assoc, ih, ← Nat.add_assoc, Nat.factorial_succ]
          ring
      have h1 := hfac_eq (n / 2) (n / 2)
      have h2 : Nat.factorial (n / 2 + n / 2) ≤ Nat.factorial n :=
        Nat.factorial_le (by omega)
      have h3 : 1 ≤ Nat.factorial (n / 2) := Nat.factorial_pos _
      nlinarith
    exact le_trans hprod_le hprod_dvd
  have hpos : (0 : ℝ) < (((n / 2) ^ (n / 2) : ℕ) : ℝ) := by
    have : 1 ≤ (n / 2) ^ (n / 2) := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  have hlog := Real.log_le_log hpos (by exact_mod_cast hpow : (((n / 2) ^ (n / 2) : ℕ) : ℝ) ≤ ((Nat.factorial n : ℕ) : ℝ))
  rw [Nat.cast_pow, Real.log_pow] at hlog
  exact hlog

/-- Elementary factorial ratio bound: for `N' ≤ n₀ ≤ N' + step`,
`log (n₀!) ≤ log (N'!) + step * log (N' + step)`. -/
lemma factorial_log_diff_upper {N' n₀ step : ℕ} (hN' : 1 ≤ N') (hlo : N' ≤ n₀) (hhi : n₀ ≤ N' + step) :
    Real.log ((Nat.factorial n₀ : ℕ) : ℝ) ≤
      Real.log ((Nat.factorial N' : ℕ) : ℝ) + (step : ℝ) * Real.log ((N' + step : ℕ) : ℝ) := by
  have hfac_le : Nat.factorial n₀ ≤ Nat.factorial N' * (N' + step) ^ step := by
    have h1 : Nat.factorial n₀ ≤ Nat.factorial (N' + step) := Nat.factorial_le hhi
    have h2 : Nat.factorial (N' + step) ≤ Nat.factorial N' * (N' + step) ^ step := by
      clear hlo hhi h1
      induction step with
      | zero => simp
      | succ s ih =>
        rw [show N' + (s + 1) = (N' + s) + 1 by omega, Nat.factorial_succ, pow_succ]
        have hstep : Nat.factorial N' * (N' + s) ^ s ≤ Nat.factorial N' * (N' + s + 1) ^ s :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) s)
        have h3 := le_trans ih hstep
        calc (N' + s + 1) * Nat.factorial (N' + s)
            ≤ (N' + s + 1) * (Nat.factorial N' * (N' + s + 1) ^ s) := Nat.mul_le_mul_left _ h3
          _ = Nat.factorial N' * ((N' + s + 1) ^ s * (N' + s + 1)) := by ring
    exact le_trans h1 h2
  have hpos1 : (0 : ℝ) < ((Nat.factorial n₀ : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n₀
  have hpos2 : (0 : ℝ) < ((Nat.factorial N' : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos N'
  have hpos3 : (0 : ℝ) < ((N' + step : ℕ) : ℝ) := by exact_mod_cast (show 0 < N' + step by omega)
  have hlog := Real.log_le_log hpos1 (by exact_mod_cast hfac_le :
    ((Nat.factorial n₀ : ℕ) : ℝ) ≤ ((Nat.factorial N' * (N' + step) ^ step : ℕ) : ℝ))
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hpos2.ne' (pow_ne_zero _ hpos3.ne'), Real.log_pow] at hlog
  exact hlog

lemma log_two_lt_one : Real.log 2 < 1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have := Real.exp_one_gt_d9
  linarith

lemma log_four_lt_two : Real.log 4 < 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  linarith [log_two_lt_one]

lemma eventually_mul_log_lt_rpow {a c : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in Filter.atTop, c * Real.log (N : ℝ) < (N : ℝ) ^ a := by
  have h1 : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ) ^ a) Filter.atTop (nhds 0) :=
    ((isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
  have hc : 0 < 1 / (max c 1) := by positivity
  filter_upwards [h1.eventually (gt_mem_nhds hc), Filter.eventually_ge_atTop 2] with N hN hN2
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hpow_pos : (0 : ℝ) < (N : ℝ) ^ a := Real.rpow_pos_of_pos hN_pos a
  have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlt := (div_lt_iff₀ hpow_pos).mp hN
  have hmul : (max c 1) * Real.log (N : ℝ) < (N : ℝ) ^ a := by
    have h2 := mul_lt_mul_of_pos_left hlt (show 0 < max c 1 by positivity)
    rw [← mul_assoc, mul_one_div_cancel (by positivity : max c 1 ≠ 0), one_mul] at h2
    exact h2
  nlinarith [le_max_left c 1]

lemma eventually_linear_lt_half_log (C : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      C * (N : ℝ) < ((N / 2 : ℕ) : ℝ) * Real.log ((N / 2 : ℕ) : ℝ) := by
  have hhalf : Filter.Tendsto (fun N : ℕ => ((N / 2 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop (2 * (Nat.ceil (max b 0) + 1))] with N hN
    have h1 : Nat.ceil (max b 0) + 1 ≤ N / 2 := by omega
    have h2 : b ≤ (Nat.ceil (max b 0) : ℝ) := le_trans (le_max_left b 0) (Nat.le_ceil _)
    have h3 : ((Nat.ceil (max b 0) + 1 : ℕ) : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h3; linarith
  have hlog := Real.tendsto_log_atTop.comp hhalf
  filter_upwards [hlog.eventually (Filter.eventually_gt_atTop (4 * max C 1)),
    Filter.eventually_ge_atTop 4] with N hlogN hN4
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN2_ge : (N : ℝ) / 4 ≤ ((N / 2 : ℕ) : ℝ) := by
    have : N ≤ 4 * (N / 2) := by omega
    have h1 : (N : ℝ) ≤ 4 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  dsimp only [Function.comp_apply] at hlogN
  have hC_le : C ≤ max C 1 := le_max_left C 1
  nlinarith

end GrasGreenbergBrocard
