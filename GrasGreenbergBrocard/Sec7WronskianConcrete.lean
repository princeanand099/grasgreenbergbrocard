import Mathlib
import GrasGreenbergBrocard.Sec7TaylorSeries
import GrasGreenbergBrocard.Sec7PowerSeriesODE

/-!
# Section 7 Concrete Support-Reduced Wronskian (Eliminates `axiom canonicalSupportWronskian`)

Constructs `padeP0Coeff`, `SupportWronskianData`, and the concrete `def canonicalSupportWronskian`
using the power-series ODE, Concrete Lemma 7.2 (`monomial_series_linear_indep_poly`), and
weighted Wronskian non-vanishing (`weighted_wronskian_ne_zero`) from `Sec7PowerSeriesODE.lean`.
-/

noncomputable section

open scoped BigOperators
open Polynomial Finset

namespace GrasGreenbergBrocard

/-- The `i = 0` Padé polynomial coefficients `p_{0, v}` (`0 ≤ v ≤ D`) uniquely determined
from `P_coeff` (`P_1, ..., P_m`) and `fam.clearedCoeff` by canceling Taylor orders
`0 ≤ v ≤ D` (manuscript eq. 7.5). -/
def padeP0Coeff {m r M D : ℕ} (fam : AlgebraicTaylorFamily m r M)
    (P_coeff : Fin m → Fin (D + 1) → ℤ) (v : Fin (D + 1)) : ℤ :=
  - ∑ i : Fin m, ∑ j : Fin (D + 1),
      if j.val ≤ v.val then
        fam.clearedCoeff i.succ (v.val - j.val) * (r : ℤ) ^ (2 * j.val) * P_coeff i j
      else 0

/-- Differential Wronskian data for a non-zero Padé linear form
`L(x) = ∑_{i ∈ S} P_i(x) f_i(x)` supported on `S ⊆ Fin(m+1)` with `s = |S|`. -/
structure SupportWronskianData (m r D O M : ℕ) (S : Finset (Fin (m + 1))) (H : ℝ) where
  Delta : ℤ[X]
  Delta_ne_zero : Delta ≠ 0
  deg_le : Delta.natDegree ≤ S.card * D + Nat.choose S.card 2 * M
  ord_zero : ℕ
  ord_zero_ge : O - (S.card - 1) ≤ ord_zero
  ord_zero_le_deg : ord_zero ≤ Delta.natDegree
  multAt : ℕ → ℕ
  sum_mult_le : ∀ T : Finset ℕ, (∀ n ∈ T, M < n) →
    ∑ n ∈ T, multAt n ≤ Delta.natDegree - ord_zero
  prod_linear_dvd : ∀ T : Finset ℕ, (∀ n ∈ T, M < n) →
    (∏ n ∈ T, (Polynomial.C (n : ℤ) * X - 1) ^ multAt n) ∣ Delta
  C_Q : ℝ
  C_Q_ge_one : 1 ≤ C_Q
  lead_bound : |(Delta.leadingCoeff : ℝ)| ≤
    (Nat.factorial S.card : ℝ) * ((D + S.card * M : ℕ) : ℝ) ^ (S.card ^ 2) *
      H ^ S.card * C_Q ^ (Nat.choose S.card 2)

/-- Helper: `(C (n : ℤ) * X - 1)` is primitive in `ℤ[X]` for every `n : ℕ`. -/
private lemma isPrimitive_C_mul_X_sub_one (n : ℕ) :
    (Polynomial.C (n : ℤ) * Polynomial.X - 1 : ℤ[X]).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  rcases hr with ⟨q, hq⟩
  have h0 := congrArg (fun P : ℤ[X] => P.coeff 0) hq
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, mul_zero,
    Polynomial.coeff_one_zero, zero_sub, Polynomial.coeff_C_mul] at h0
  exact isUnit_of_mul_eq_one r (-q.coeff 0) (by linarith)

/-- Helper: in `Polynomial ℚ`, `(C (n : ℚ) * X - 1)^a ∣ P` where `a = P.rootMultiplicity (n : ℚ)⁻¹`. -/
private lemma pow_linear_dvd_of_rootMultiplicity {n : ℕ} (hn : 1 ≤ n) (P : Polynomial ℚ) :
    (Polynomial.C (n : ℚ) * Polynomial.X - 1) ^ (P.rootMultiplicity ((n : ℚ)⁻¹)) ∣ P := by
  have hn_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlin : Polynomial.C (n : ℚ) * Polynomial.X - 1 =
      Polynomial.C (n : ℚ) * (Polynomial.X - Polynomial.C ((n : ℚ)⁻¹)) := by
    rw [mul_sub, ← Polynomial.C_mul, mul_inv_cancel₀ hn_ne, Polynomial.C_1]
  rw [hlin, mul_pow]
  have hdvd := Polynomial.pow_rootMultiplicity_dvd P ((n : ℚ)⁻¹)
  rcases hdvd with ⟨q, hq⟩
  refine ⟨Polynomial.C (((n : ℚ) ^ (P.rootMultiplicity ((n : ℚ)⁻¹)))⁻¹) * q, ?_⟩
  rw [hq, ← Polynomial.C_pow]
  calc P = (Polynomial.X - Polynomial.C (n : ℚ)⁻¹) ^ P.rootMultiplicity (n : ℚ)⁻¹ * q := hq
    _ = (Polynomial.C ((n : ℚ) ^ P.rootMultiplicity (n : ℚ)⁻¹) *
          Polynomial.C (((n : ℚ) ^ P.rootMultiplicity (n : ℚ)⁻¹)⁻¹)) *
        ((Polynomial.X - Polynomial.C (n : ℚ)⁻¹) ^ P.rootMultiplicity (n : ℚ)⁻¹ * q) := by
          rw [← Polynomial.C_mul, mul_inv_cancel₀ (pow_ne_zero _ hn_ne), Polynomial.C_1, one_mul]
    _ = Polynomial.C ((n : ℚ) ^ P.rootMultiplicity (n : ℚ)⁻¹) *
        (Polynomial.X - Polynomial.C (n : ℚ)⁻¹) ^ P.rootMultiplicity (n : ℚ)⁻¹ *
        (Polynomial.C (((n : ℚ) ^ P.rootMultiplicity (n : ℚ)⁻¹)⁻¹) * q) := by ring

/-- Helper: `rootMultiplicity` of `0` plus `∑ n ∈ T, rootMultiplicity (1/n)` is `≤ P.natDegree`. -/
private lemma rootMultiplicity_zero_add_sum_le {P : Polynomial ℚ} (hP : P ≠ 0)
    (T : Finset ℕ) (hT : ∀ n ∈ T, 1 ≤ n) :
    P.rootMultiplicity 0 + ∑ n ∈ T, P.rootMultiplicity ((n : ℚ)⁻¹) ≤ P.natDegree := by
  classical
  let f : ℕ → ℚ := fun n => (n : ℚ)⁻¹
  have hfinj : Set.InjOn f T := by
    intro a ha b hb hab
    dsimp only [f] at hab
    have h1 : (a : ℚ) = (b : ℚ) := inv_injective hab
    exact Nat.cast_injective h1
  have h0not : (0 : ℚ) ∉ T.image f := by
    intro h0
    rcases Finset.mem_image.mp h0 with ⟨n, hn, hfn⟩
    have hn1 := hT n hn
    have hn_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact inv_ne_zero hn_ne hfn
  let S_roots : Finset ℚ := insert 0 (T.image f)
  have hsum_eq : ∑ α ∈ S_roots, P.rootMultiplicity α =
      P.rootMultiplicity 0 + ∑ n ∈ T, P.rootMultiplicity ((n : ℚ)⁻¹) := by
    rw [Finset.sum_insert h0not, Finset.sum_image (fun a ha b hb hab => hfinj ha hb hab)]
  rw [← hsum_eq]
  have hcount : ∀ α ∈ S_roots, P.rootMultiplicity α = Multiset.count α P.roots := fun α _ =>
    (Polynomial.count_roots P).symm
  rw [Finset.sum_congr rfl hcount]
  have hle_card : ∑ α ∈ S_roots, Multiset.count α P.roots ≤ P.roots.card := by
    have hsub : (S_roots.val.bind (fun α => Multiset.replicate (Multiset.count α P.roots) α)) ≤ P.roots := by
      rw [Multiset.le_iff_count]
      intro x
      by_cases hx : x ∈ S_roots
      · have h1 : Multiset.count x (S_roots.val.bind (fun α => Multiset.replicate (Multiset.count α P.roots) α)) =
            ∑ α ∈ S_roots, Multiset.count x (Multiset.replicate (Multiset.count α P.roots) α) := by
          rw [Multiset.count_bind]; rfl
        rw [h1, Finset.sum_eq_single x]
        · simp
        · intro α _ hαx; simp [Multiset.count_replicate, hαx]
        · intro habs; exact absurd hx habs
      · have h1 : Multiset.count x (S_roots.val.bind (fun α => Multiset.replicate (Multiset.count α P.roots) α)) = 0 := by
          rw [Multiset.count_bind]
          change ∑ α ∈ S_roots, Multiset.count x (Multiset.replicate (Multiset.count α P.roots) α) = 0
          apply Finset.sum_eq_zero; intro α hα
          have hne : α ≠ x := fun h => hx (h ▸ hα)
          simp [Multiset.count_replicate, hne]
        rw [h1]; exact Nat.zero_le _
    calc ∑ α ∈ S_roots, Multiset.count α P.roots
        = (S_roots.val.bind (fun α => Multiset.replicate (Multiset.count α P.roots) α)).card := by
            rw [Multiset.card_bind]; simp; rfl
      _ ≤ P.roots.card := Multiset.card_le_card hsub
  exact le_trans hle_card (Polynomial.card_roots' P)

/-- **Concrete Canonical Support-Reduced Wronskian (`def`, Zero External Axioms — Eliminates
`axiom canonicalSupportWronskian`)**:
Constructs `Delta_S := Matrix.det M_S ∈ ℤ[X]` directly from `P_coeff`, `padeP0Coeff`, and the
concrete ODE differential operator `D_step Q = T_int * Q' + TA_int * Q`, proving all fields of
`SupportWronskianData` unconditionally from Concrete Lemma 7.2 (`monomial_series_linear_indep_poly`),
Wronskian non-vanishing (`weighted_wronskian_ne_zero`), `Matrix.adjugate_mul`, and Gauss's Lemma. -/
def canonicalSupportWronskian {d E r D O M B : ℕ}
    (hd : 1 ≤ d) (hE : 1 ≤ E) (hr : 2 ≤ r) (hEr : E ≤ r - 1) (hM : 1 ≤ M)
    (β : Fin d → ℕ)
    (hβ_lo : ∀ i, r ≤ β i) (hβ_hi : ∀ i, β i ≤ M) (hβ_dvd : ∀ i, r ∣ β i)
    (hβ_mono : StrictMono β)
    (P_coeff : Fin (Nat.choose (d + E) d - 1) → Fin (D + 1) → ℤ)
    (S : Finset (Fin ((Nat.choose (d + E) d - 1) + 1)))
    (hD : 1 ≤ D) (hO_gt : D < O)
    (hP_nz : ∃ i j, P_coeff i j ≠ 0)
    (hP_bd : ∀ i j, |P_coeff i j| ≤ (B : ℤ))
    (hP_van : ∀ t : Fin (O - D),
      ∑ i : Fin (Nat.choose (d + E) d - 1), ∑ j : Fin (D + 1),
        (if j.val ≤ D + 1 + t.val then
          (canonicalMonomialTaylorFamily hd hE hr hEr hM β hβ_lo hβ_hi hβ_dvd hβ_mono).clearedCoeff
            i.succ (D + 1 + t.val - j.val) * (r : ℤ) ^ (2 * j.val)
        else 0) * P_coeff i j = 0)
    (hS_zero : (0 : Fin ((Nat.choose (d + E) d - 1) + 1)) ∈ S ↔
      ∃ v : Fin (D + 1), padeP0Coeff
        (canonicalMonomialTaylorFamily hd hE hr hEr hM β hβ_lo hβ_hi hβ_dvd hβ_mono)
        P_coeff v ≠ 0)
    (hS_eq : ∀ i : Fin (Nat.choose (d + E) d - 1),
      i.succ ∈ S ↔ ∃ j : Fin (D + 1), P_coeff i j ≠ 0) :
    SupportWronskianData (Nat.choose (d + E) d - 1) r D O M S (((D + 1) * B + 1 : ℕ) : ℝ) := by
  classical
  let m := Nat.choose (d + E) d - 1
  have hchoose_pos : 1 ≤ Nat.choose (d + E) d := Nat.choose_pos (by omega)
  have hcast : m + 1 = Nat.choose (d + E) d := Nat.sub_add_cancel hchoose_pos
  let idxToMulti : Fin (m + 1) → (Fin d → ℕ) :=
    fun i => (multiIndexEquiv d E (Fin.cast hcast i)).val
  let fam := canonicalMonomialTaylorFamily hd hE hr hEr hM β hβ_lo hβ_hi hβ_dvd hβ_mono
  have hr1 : 1 ≤ r := by omega
  have hr_ne_z : (r : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hr_ne_q : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Cleared integer Padé polynomials `P_int i ∈ ℤ[X]` (scaled by `r^(2D)`)
  let P_int : Fin (m + 1) → ℤ[X] := fun i =>
    Fin.cases
      (∑ v : Fin (D + 1), Polynomial.C (padeP0Coeff fam P_coeff v * (r : ℤ) ^ (2 * (D - v.val))) * Polynomial.X ^ v.val)
      (fun i' => ∑ j : Fin (D + 1), Polynomial.C (P_coeff i' j * (r : ℤ) ^ (2 * D)) * Polynomial.X ^ j.val)
      i
  have hP_int_deg : ∀ i : Fin (m + 1), (P_int i).natDegree ≤ D := by
    intro i
    refine Fin.cases ?_ (fun i' => ?_) i
    · dsimp only [P_int]; simp only [Fin.cases_zero]
      refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
      rw [Finset.fold_max_le]; refine ⟨Nat.zero_le D, fun v _ => ?_⟩
      refine le_trans Polynomial.natDegree_C_mul_le ?_; rw [Polynomial.natDegree_X_pow]; omega
    · dsimp only [P_int]; simp only [Fin.cases_succ]
      refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
      rw [Finset.fold_max_le]; refine ⟨Nat.zero_le D, fun j _ => ?_⟩
      refine le_trans Polynomial.natDegree_C_mul_le ?_; rw [Polynomial.natDegree_X_pow]; omega
  have hP_int_coeff_zero : ∀ v : Fin (D + 1),
      (P_int 0).coeff v.val = padeP0Coeff fam P_coeff v * (r : ℤ) ^ (2 * (D - v.val)) := by
    intro v
    dsimp only [P_int]; simp only [Fin.cases_zero, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single v]
    · simp
    · intro u _ huv; have : v.val ≠ u.val := fun h => huv (Fin.ext h.symm); simp [this]
    · intro habs; exact absurd (Finset.mem_univ v) habs
  have hP_int_coeff_succ : ∀ (i' : Fin m) (j : Fin (D + 1)),
      (P_int i'.succ).coeff j.val = P_coeff i' j * (r : ℤ) ^ (2 * D) := by
    intro i' j
    dsimp only [P_int]; simp only [Fin.cases_succ, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro u _ huj; have : j.val ≠ u.val := fun h => huj (Fin.ext h.symm); simp [this]
    · intro habs; exact absurd (Finset.mem_univ j) habs
  have hP_int_ne_zero : ∀ i ∈ S, P_int i ≠ 0 := by
    intro i hi
    refine Fin.cases ?_ (fun i' => ?_) i hi
    · intro hi0 h0
      obtain ⟨v, hv⟩ := hS_zero.mp hi0
      have hc := congrArg (fun P : ℤ[X] => P.coeff v.val) h0
      rw [hP_int_coeff_zero v, Polynomial.coeff_zero] at hc
      exact (mul_ne_zero hv (pow_ne_zero _ hr_ne_z)) hc
    · intro his h0
      obtain ⟨j, hj⟩ := (hS_eq i').mp his
      have hc := congrArg (fun P : ℤ[X] => P.coeff j.val) h0
      rw [hP_int_coeff_succ i' j, Polynomial.coeff_zero] at hc
      exact (mul_ne_zero hj (pow_ne_zero _ hr_ne_z)) hc
  have hP_int_eq_zero_of_notMem : ∀ i : Fin (m + 1), i ∉ S → P_int i = 0 := by
    intro i hi
    refine Fin.cases ?_ (fun i' => ?_) i hi
    · intro hi0
      have hall : ∀ v : Fin (D + 1), padeP0Coeff fam P_coeff v = 0 := by
        intro v; by_contra hne; exact hi0 (hS_zero.mpr ⟨v, hne⟩)
      dsimp only [P_int]; simp [hall]
    · intro his
      have hall : ∀ j : Fin (D + 1), P_coeff i' j = 0 := by
        intro j; by_contra hne; exact his ((hS_eq i').mpr ⟨j, hne⟩)
      dsimp only [P_int]; simp [hall]
  -- Differential iteration `P_iter k i ∈ ℤ[X]`
  let D_step : Fin (m + 1) → ℤ[X] → ℤ[X] := fun i Q =>
    T_int r M * Polynomial.derivative Q + TA_int M β (idxToMulti i) * Q
  let P_iter : ℕ → Fin (m + 1) → ℤ[X] := fun k i => (D_step i)^[k] (P_int i)
  have hP_iter_deg : ∀ k i, (P_iter k i).natDegree ≤ D + k * M := by
    intro k
    induction k with
    | zero => intro i; simpa [P_iter] using hP_int_deg i
    | succ k ih =>
      intro i
      dsimp only [P_iter]
      rw [Function.iterate_succ_apply']
      dsimp only [D_step]
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans Polynomial.natDegree_mul_le ?_
        have h1 := natDegree_T_int_le r M
        have h2 := le_trans Polynomial.natDegree_derivative_le (ih i)
        have : M + (D + k * M) = D + (k + 1) * M := by ring
        omega
      · refine le_trans Polynomial.natDegree_mul_le ?_
        have h1 := natDegree_TA_int_le M β (idxToMulti i)
        have h2 := ih i
        have : M + (D + k * M) = D + (k + 1) * M := by ring
        omega
  -- Equivalence `eS : Fin S.card ≃ S` and Wronskian matrix `M_S`
  let s := S.card
  let eS : Fin s ≃ {i : Fin (m + 1) // i ∈ S} := (Fintype.equivFinOfCardEq (by simp [s])).symm
  let M_S : Matrix (Fin s) (Fin s) ℤ[X] := Matrix.of (fun k j => P_iter k.val (eS j).val)
  let Delta_S : ℤ[X] := M_S.det
  -- Key power-series relation: `((P_iter k i).map ℚ) * Ω_i = (T_rat * psDeriv)^[k] (((P_int i).map ℚ) * Ω_i)`
  have hiter_ps : ∀ (k : ℕ) (i : Fin (m + 1)),
      (((P_iter k i).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
        unscaledMonomialSeries r β (idxToMulti i) =
      (fun f => (T_rat r M : PowerSeries ℚ) * psDeriv f)^[k]
        ((((P_int i).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
          unscaledMonomialSeries r β (idxToMulti i)) := by
    intro k i
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ← ih]
      dsimp only [P_iter]
      rw [Function.iterate_succ_apply']
      dsimp only [D_step]
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.derivative_map,
        Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul,
        psDeriv_mul, psDeriv_coe_poly, mul_add]
      have hode := unscaledMonomialSeries_ode hr1 β (idxToMulti i) hβ_hi
      change ((T_rat r M : PowerSeries ℚ) * ((Polynomial.derivative ((P_iter k i).map (Int.castRingHom ℚ)) : Polynomial ℚ) : PowerSeries ℚ) +
        (TA_rat M β (idxToMulti i) : PowerSeries ℚ) * (((P_iter k i).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ)) *
          unscaledMonomialSeries r β (idxToMulti i) = _
      calc ((T_rat r M : PowerSeries ℚ) * ((Polynomial.derivative ((P_iter k i).map (Int.castRingHom ℚ)) : Polynomial ℚ) : PowerSeries ℚ) +
            (TA_rat M β (idxToMulti i) : PowerSeries ℚ) * (((P_iter k i).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ)) *
              unscaledMonomialSeries r β (idxToMulti i)
          = (T_rat r M : PowerSeries ℚ) * (((Polynomial.derivative ((P_iter k i).map (Int.castRingHom ℚ)) : Polynomial ℚ) : PowerSeries ℚ) *
              unscaledMonomialSeries r β (idxToMulti i)) +
            (((P_iter k i).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
              ((TA_rat M β (idxToMulti i) : PowerSeries ℚ) * unscaledMonomialSeries r β (idxToMulti i)) := by ring
        _ = (T_rat r M : PowerSeries ℚ) * (((Polynomial.derivative ((P_iter k i).map (Int.castRingHom ℚ)) : Polynomial ℚ) : PowerSeries ℚ) *
              unscaledMonomialSeries r β (idxToMulti i)) +
            (T_rat r M : PowerSeries ℚ) * ((((P_iter k i).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
              psDeriv (unscaledMonomialSeries r β (idxToMulti i))) := by rw [← hode]; ring
  -- Linear form `L_0 = ∑ j : Fin s, P_int (eS j) * Ω_{eS j}` vanishes to order `≥ O + 1` at `0`
  let L_0 : PowerSeries ℚ := ∑ j : Fin s,
    (((P_int (eS j).val).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
      unscaledMonomialSeries r β (idxToMulti (eS j).val)
  have hL_0_eq_full : L_0 = ∑ i : Fin (m + 1),
      (((P_int i).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
        unscaledMonomialSeries r β (idxToMulti i) := by
    dsimp only [L_0]
    have hbij : ∑ j : Fin s,
        (((P_int (eS j).val).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
          unscaledMonomialSeries r β (idxToMulti (eS j).val) =
        ∑ i ∈ S, (((P_int i).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
          unscaledMonomialSeries r β (idxToMulti i) := by
      rw [← Finset.sum_attach S]
      exact Fintype.sum_equiv eS _ _ (fun _ => rfl)
    rw [hbij]
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    rw [hP_int_eq_zero_of_notMem i hi, Polynomial.map_zero, Polynomial.coe_zero, zero_mul]
  have hL_0_van : ∀ n : ℕ, n ≤ O → PowerSeries.coeff n L_0 = 0 := by
    intro n hnO
    rw [hL_0_eq_full, map_sum, Fin.sum_univ_succ]
    have h0_idx : idxToMulti 0 = fun _ => 0 := multiIndexEquiv_zero d E
    have h0_om : unscaledMonomialSeries r β (idxToMulti 0) = 1 := by
      rw [h0_idx, unscaledMonomialSeries_zero]
    rw [h0_om, mul_one]
    have hterm_succ : ∀ i' : Fin m,
        PowerSeries.coeff n
          ((((P_int i'.succ).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
            unscaledMonomialSeries r β (idxToMulti i'.succ)) =
        ((r : ℚ) ^ (2 * D) / (r : ℚ) ^ (2 * n)) *
          ∑ j : Fin (D + 1),
            if j.val ≤ n then
              (fam.clearedCoeff i'.succ (n - j.val) : ℚ) * (r : ℚ) ^ (2 * j.val) * (P_coeff i' j : ℚ)
            else 0 := by
      intro i'
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v => PowerSeries.coeff u (((P_int i'.succ).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) * PowerSeries.coeff v (unscaledMonomialSeries r β (idxToMulti i'.succ)))]
      have hsum_fin : ∑ u ∈ Finset.range (n + 1),
          PowerSeries.coeff u (((P_int i'.succ).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
            PowerSeries.coeff (n - u) (unscaledMonomialSeries r β (idxToMulti i'.succ)) =
          ∑ j : Fin (D + 1),
            if j.val ≤ n then
              ((P_coeff i' j : ℚ) * (r : ℚ) ^ (2 * D)) *
                PowerSeries.coeff (n - j.val) (unscaledMonomialSeries r β (idxToMulti i'.succ))
            else 0 := by
        have hrhs_eq : (∑ j : Fin (D + 1),
            if j.val ≤ n then
              ((P_coeff i' j : ℚ) * (r : ℚ) ^ (2 * D)) *
                PowerSeries.coeff (n - j.val) (unscaledMonomialSeries r β (idxToMulti i'.succ))
            else 0) =
          ∑ u ∈ Finset.range (D + 1),
            if u ≤ n then
              (if h : u < D + 1 then (P_coeff i' ⟨u, h⟩ : ℚ) * (r : ℚ) ^ (2 * D) else 0) *
                PowerSeries.coeff (n - u) (unscaledMonomialSeries r β (idxToMulti i'.succ))
            else 0 := by
          rw [← Fin.sum_univ_eq_sum_range]
          apply Finset.sum_congr rfl; intro j _
          simp [j.isLt]
        rw [hrhs_eq]
        have h1 : ∀ u ∈ Finset.range (n + 1),
            PowerSeries.coeff u (((P_int i'.succ).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
              PowerSeries.coeff (n - u) (unscaledMonomialSeries r β (idxToMulti i'.succ)) =
            (if h : u < D + 1 then (P_coeff i' ⟨u, h⟩ : ℚ) * (r : ℚ) ^ (2 * D) else 0) *
              PowerSeries.coeff (n - u) (unscaledMonomialSeries r β (idxToMulti i'.succ)) := by
          intro u _
          rw [Polynomial.coeff_coe, Polynomial.coeff_map]
          by_cases hu : u < D + 1
          · rw [dif_pos hu, hP_int_coeff_succ i' ⟨u, hu⟩]; simp
          · rw [dif_neg hu]
            have hdeg := hP_int_deg i'.succ
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
        rw [Finset.sum_congr rfl h1]
        -- Both sums equal sum over `u ∈ range (min n D + 1)`
        have hmin1 : ∑ u ∈ Finset.range (n + 1),
            (if h : u < D + 1 then (P_coeff i' ⟨u, h⟩ : ℚ) * (r : ℚ) ^ (2 * D) else 0) *
              PowerSeries.coeff (n - u) (unscaledMonomialSeries r β (idxToMulti i'.succ)) =
            ∑ u ∈ Finset.range (min n D + 1),
              (if h : u < D + 1 then (P_coeff i' ⟨u, h⟩ : ℚ) * (r : ℚ) ^ (2 * D) else 0) *
                PowerSeries.coeff (n - u) (unscaledMonomialSeries r β (idxToMulti i'.succ)) := by
          symm; apply Finset.sum_subset (Finset.range_mono (by omega))
          intro u hu hnot
          have hu_gt : D + 1 ≤ u := by
            have := Finset.mem_range.mp hu
            have : ¬ u < min n D + 1 := fun h => hnot (Finset.mem_range.mpr h)
            omega
          rw [dif_neg (by omega), zero_mul]
        have hmin2 : ∑ u ∈ Finset.range (D + 1),
            (if u ≤ n then
              (if h : u < D + 1 then (P_coeff i' ⟨u, h⟩ : ℚ) * (r : ℚ) ^ (2 * D) else 0) *
                PowerSeries.coeff (n - u) (unscaledMonomialSeries r β (idxToMulti i'.succ))
             else 0) =
            ∑ u ∈ Finset.range (min n D + 1),
              (if h : u < D + 1 then (P_coeff i' ⟨u, h⟩ : ℚ) * (r : ℚ) ^ (2 * D) else 0) *
                PowerSeries.coeff (n - u) (unscaledMonomialSeries r β (idxToMulti i'.succ)) := by
          rw [← Finset.sum_filter]
          have hflt : (Finset.range (D + 1)).filter (· ≤ n) = Finset.range (min n D + 1) := by
            ext u; simp only [Finset.mem_filter, Finset.mem_range]; omega
          rw [hflt]
        rw [hmin1, hmin2]
      rw [hsum_fin, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      split_ifs with hjle
      · have hscale : (fam.clearedCoeff i'.succ (n - j.val) : ℚ) =
            (r : ℚ) ^ (2 * (n - j.val)) * PowerSeries.coeff (n - j.val) (unscaledMonomialSeries r β (idxToMulti i'.succ)) := by
          exact clearedMonomialSeries_coeff_eq_scaled hr1 β (idxToMulti i'.succ) (n - j.val)
        rw [hscale]
        have hpow : (r : ℚ) ^ (2 * (n - j.val)) * (r : ℚ) ^ (2 * j.val) = (r : ℚ) ^ (2 * n) := by
          rw [← pow_add, show 2 * (n - j.val) + 2 * j.val = 2 * n by omega]
        field_simp [pow_ne_zero (2 * n) hr_ne_q]
        rw [← hpow]; ring
      · simp
    simp_rw [hterm_succ, ← Finset.mul_sum]
    by_cases hnD : n ≤ D
    · have h0c : PowerSeries.coeff n (((P_int 0).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) =
          (padeP0Coeff fam P_coeff ⟨n, by omega⟩ : ℚ) * (r : ℚ) ^ (2 * (D - n)) := by
        rw [Polynomial.coeff_coe, Polynomial.coeff_map, hP_int_coeff_zero ⟨n, by omega⟩]; simp
      rw [h0c]
      unfold padeP0Coeff
      push_cast
      have hpow : (r : ℚ) ^ (2 * (D - n)) * (r : ℚ) ^ (2 * n) = (r : ℚ) ^ (2 * D) := by
        rw [← pow_add, show 2 * (D - n) + 2 * n = 2 * D by omega]
      field_simp [pow_ne_zero (2 * n) hr_ne_q]
      linear_combination -(∑ i : Fin m, ∑ j : Fin (D + 1),
        if j.val ≤ n then (fam.clearedCoeff i.succ (n - j.val) : ℚ) * (r : ℚ) ^ (2 * j.val) * (P_coeff i j : ℚ)
        else 0) * hpow
    · have h0c : PowerSeries.coeff n (((P_int 0).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) = 0 := by
        rw [Polynomial.coeff_coe, Polynomial.coeff_map]
        have hdeg := hP_int_deg 0
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
      rw [h0c, zero_add]
      have ht_lt : n - (D + 1) < O - D := by omega
      have hvan := hP_van ⟨n - (D + 1), ht_lt⟩
      have hvan_q : (∑ i : Fin m, ∑ j : Fin (D + 1),
          (if j.val ≤ n then
            (fam.clearedCoeff i.succ (n - j.val) : ℚ) * (r : ℚ) ^ (2 * j.val)
           else 0) * (P_coeff i j : ℚ)) = 0 := by
        have hcast_van : ((∑ i : Fin m, ∑ j : Fin (D + 1),
            (if j.val ≤ D + 1 + (n - (D + 1)) then
              fam.clearedCoeff i.succ (D + 1 + (n - (D + 1)) - j.val) * (r : ℤ) ^ (2 * j.val)
             else 0) * P_coeff i j : ℤ) : ℚ) = 0 := by
          exact_mod_cast hvan
        have hneq : D + 1 + (n - (D + 1)) = n := by omega
        rw [hneq] at hcast_van
        push_cast at hcast_van
        exact hcast_van
      have hsum_eq : (∑ i : Fin m, ∑ j : Fin (D + 1),
          if j.val ≤ n then
            (fam.clearedCoeff i.succ (n - j.val) : ℚ) * (r : ℚ) ^ (2 * j.val) * (P_coeff i j : ℚ)
          else 0) = 0 := by
        trans (∑ i : Fin m, ∑ j : Fin (D + 1),
          (if j.val ≤ n then
            (fam.clearedCoeff i.succ (n - j.val) : ℚ) * (r : ℚ) ^ (2 * j.val)
           else 0) * (P_coeff i j : ℚ))
        · apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          split_ifs <;> ring
        · exact hvan_q
      rw [hsum_eq, mul_zero]
  -- Prove `2 ≤ s` (from `hP_nz`, `hO_gt`, and `hL_0_van`)
  have hs_ge2 : 2 ≤ s := by
    obtain ⟨i₀, j₀, hij₀⟩ := hP_nz
    have hi₀_mem : i₀.succ ∈ S := (hS_eq i₀).mpr ⟨j₀, hij₀⟩
    have hs_pos : 1 ≤ s := Finset.card_pos.mpr ⟨i₀.succ, hi₀_mem⟩
    by_contra hlt2
    have hs1 : s = 1 := by omega
    have hS_sing : S = {i₀.succ} := (Finset.card_eq_one.mp hs1).elim (fun a ha => by
      have : i₀.succ = a := Finset.mem_singleton.mp (ha ▸ hi₀_mem)
      rw [ha, this])
    have hL0_sing : L_0 =
        (((P_int i₀.succ).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
          unscaledMonomialSeries r β (idxToMulti i₀.succ) := by
      rw [hL_0_eq_full]
      rw [Finset.sum_eq_single i₀.succ]
      · intro i _ hi_ne
        have : i ∉ S := by rw [hS_sing, Finset.mem_singleton]; exact hi_ne
        rw [hP_int_eq_zero_of_notMem i this, Polynomial.map_zero, Polynomial.coe_zero, zero_mul]
      · intro habs; exact absurd (Finset.mem_univ _) habs
    -- Since `P_int i₀.succ ≠ 0` and has `natDegree ≤ D`, its lowest nonzero coeff `k ≤ D` gives `coeff k L_0 ≠ 0`!
    have hne0 : (P_int i₀.succ).map (Int.castRingHom ℚ) ≠ 0 := by
      intro h0
      apply hP_int_ne_zero i₀.succ hi₀_mem
      ext k
      have := congrArg (fun P : Polynomial ℚ => P.coeff k) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast, Int.cast_eq_zero] at this
      exact this
    have hex_c : ∃ k : ℕ, ((P_int i₀.succ).map (Int.castRingHom ℚ)).coeff k ≠ 0 := by
      by_contra h0; push Not at h0; apply hne0; ext k; exact h0 k
    set k0 := Nat.find hex_c
    have hk0_ne : ((P_int i₀.succ).map (Int.castRingHom ℚ)).coeff k0 ≠ 0 := Nat.find_spec hex_c
    have hk0_min : ∀ u < k0, ((P_int i₀.succ).map (Int.castRingHom ℚ)).coeff u = 0 := fun u hu => by
      by_contra hne; exact Nat.find_min hex_c hu hne
    have hk0_le_D : k0 ≤ D := by
      by_contra hgt
      have hdeg := le_trans Polynomial.natDegree_map_le (hP_int_deg i₀.succ)
      exact hk0_ne (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
    have hcoeff_k0 : PowerSeries.coeff k0 L_0 = ((P_int i₀.succ).map (Int.castRingHom ℚ)).coeff k0 := by
      rw [hL0_sing, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v => PowerSeries.coeff u (((P_int i₀.succ).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) * PowerSeries.coeff v (unscaledMonomialSeries r β (idxToMulti i₀.succ)))]
      rw [Finset.sum_eq_single k0]
      · simp [Polynomial.coeff_coe, unscaledMonomialSeries_const]
      · intro u hu hne
        have hlt : u < k0 := by have := Finset.mem_range.mp hu; omega
        rw [Polynomial.coeff_coe, hk0_min u hlt, zero_mul]
      · intro habs; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k0)) habs
    have h0 := hL_0_van k0 (by omega)
    rw [hcoeff_k0] at h0
    exact hk0_ne h0
  -- 1. Prove `Delta_S ≠ 0`
  have hDelta_ne_zero : Delta_S ≠ 0 := by
    intro hD0
    let g : Fin s → PowerSeries ℚ := fun j =>
      (((P_int (eS j).val).map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) *
        unscaledMonomialSeries r β (idxToMulti (eS j).val)
    have hli : ∀ c : Fin s → ℚ, (∑ j : Fin s, PowerSeries.C (c j) * g j = 0) → ∀ j, c j = 0 := by
      intro c hc
      let U : Finset (Fin d → ℕ) := S.image idxToMulti
      have hU_sub : U ⊆ multiIndexFinset d E := by
        intro e he
        rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
        exact (multiIndexEquiv d E (Fin.cast hcast i)).property
      have hidx_inj : Function.Injective idxToMulti := by
        intro a b hab
        have h1 : multiIndexEquiv d E (Fin.cast hcast a) = multiIndexEquiv d E (Fin.cast hcast b) :=
          Subtype.ext hab
        have h2 := (multiIndexEquiv d E).injective h1
        exact Fin.cast_injective hcast h2
      let P_map : (Fin d → ℕ) → Polynomial ℚ := fun e =>
        if h : ∃ j : Fin s, idxToMulti (eS j).val = e then
          let j := Classical.choose h
          Polynomial.C (c j) * (P_int (eS j).val).map (Int.castRingHom ℚ)
        else 0
      have hrel : ∑ e ∈ U, (P_map e : PowerSeries ℚ) * unscaledMonomialSeries r β e = 0 := by
        have hsum_eq : ∑ e ∈ U, (P_map e : PowerSeries ℚ) * unscaledMonomialSeries r β e =
            ∑ j : Fin s, PowerSeries.C (c j) * g j := by
          symm
          refine Finset.sum_nbij (fun j : Fin s => idxToMulti (eS j).val) ?_ ?_ ?_ ?_
          · intro j _; exact Finset.mem_image.mpr ⟨(eS j).val, (eS j).property, rfl⟩
          · intro j₁ _ j₂ _ heq
            exact eS.injective (Subtype.ext (hidx_inj heq))
          · intro e he
            rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
            exact ⟨eS.symm ⟨i, hi⟩, Finset.mem_univ _, by simp⟩
          · intro j _
            have hex : ∃ j' : Fin s, idxToMulti (eS j').val = idxToMulti (eS j).val := ⟨j, rfl⟩
            have hch : Classical.choose hex = j :=
              eS.injective (Subtype.ext (hidx_inj (Classical.choose_spec hex)))
            dsimp only [P_map, g]
            rw [dif_pos hex, hch, Polynomial.coe_mul, Polynomial.coe_C, mul_assoc]
        rw [hsum_eq]; exact hc
      have hall0 := monomial_series_linear_indep_poly hd hE hr hEr hM β hβ_lo hβ_hi hβ_mono U hU_sub P_map hrel
      intro j
      have he_mem : idxToMulti (eS j).val ∈ U := Finset.mem_image.mpr ⟨(eS j).val, (eS j).property, rfl⟩
      have h0 := hall0 _ he_mem
      have hex : ∃ j' : Fin s, idxToMulti (eS j').val = idxToMulti (eS j).val := ⟨j, rfl⟩
      have hch : Classical.choose hex = j :=
        eS.injective (Subtype.ext (hidx_inj (Classical.choose_spec hex)))
      dsimp only [P_map] at h0
      rw [dif_pos hex, hch] at h0
      have hPne : (P_int (eS j).val).map (Int.castRingHom ℚ) ≠ 0 := by
        intro hp0
        apply hP_int_ne_zero (eS j).val (eS j).property
        ext k
        have := congrArg (fun P : Polynomial ℚ => P.coeff k) hp0
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast, Int.cast_eq_zero] at this
        exact this
      have hC0 : Polynomial.C (c j) = 0 := (mul_eq_zero.mp h0).resolve_right hPne
      exact Polynomial.C_eq_zero.mp hC0
    have hT_ps_ne : (T_rat r M : PowerSeries ℚ) ≠ 0 := by
      intro h0
      apply T_rat_ne_zero hr1
      ext k
      have := congrArg (PowerSeries.coeff k) h0
      simpa [Polynomial.coeff_coe] using this
    have hG_ne := weighted_wronskian_ne_zero (T_rat r M : PowerSeries ℚ) hT_ps_ne g hli
    -- Relate `det G` to `Delta_S * ∏ j, Ω_{eS j}`
    let ι_ps : ℤ[X] →+* PowerSeries ℚ := (Polynomial.coeToPowerSeries.ringHom (R := ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))
    have hG_fac : Matrix.of (fun k j : Fin s => (fun f => (T_rat r M : PowerSeries ℚ) * psDeriv f)^[k.val] (g j)) =
        ι_ps.mapMatrix M_S * Matrix.diagonal (fun j : Fin s => unscaledMonomialSeries r β (idxToMulti (eS j).val)) := by
      apply Matrix.ext; intro k j
      simp only [Matrix.of_apply, Matrix.mul_diagonal, RingHom.mapMatrix_apply, Matrix.map_apply, M_S,
        ι_ps, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coeToPowerSeries.ringHom_apply]
      exact (hiter_ps k.val (eS j).val).symm
    rw [hG_fac, Matrix.det_mul, ← RingHom.map_det] at hG_ne
    have hD0_ps : ι_ps M_S.det = 0 := by
      change ι_ps Delta_S = 0; rw [hD0, map_zero]
    rw [hD0_ps, zero_mul] at hG_ne
    exact hG_ne rfl
  -- 2. Prove `deg_le : Delta_S.natDegree ≤ s * D + Nat.choose s 2 * M`
  have hdeg_le : Delta_S.natDegree ≤ s * D + Nat.choose s 2 * M := by
    dsimp only [Delta_S]
    rw [Matrix.det_apply]
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun σ _ => ?_⟩
    have hsmul : (Equiv.Perm.sign σ • ∏ k : Fin s, M_S (σ k) k).natDegree ≤
        (∏ k : Fin s, M_S (σ k) k).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> rw [h1] <;> simp
    refine le_trans hsmul (le_trans (Polynomial.natDegree_prod_le _ _) ?_)
    have hsum_deg : ∑ k : Fin s, (M_S (σ k) k).natDegree ≤ ∑ k : Fin s, (D + (σ k).val * M) :=
      Finset.sum_le_sum (fun k _ => hP_iter_deg (σ k).val (eS k).val)
    refine le_trans hsum_deg ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      ← Finset.sum_mul]
    have hperm_sum : ∑ k : Fin s, (σ k).val = Nat.choose s 2 := by
      rw [Equiv.sum_comp σ (fun k : Fin s => k.val), Fin.sum_univ_eq_sum_range (fun k => k) s]
      clear hsum_deg hsmul hDelta_ne_zero hP_iter_deg hiter_ps hL_0_van hL_0_eq_full hs_ge2
      induction s with
      | zero => simp
      | succ n ihn =>
        rw [Finset.sum_range_succ, ihn, Nat.choose_succ_succ, Nat.choose_one_right]; ring
    rw [hperm_sum]
  -- 3. Prove `ord_zero_ge : O - (s - 1) ≤ Delta_S.rootMultiplicity 0` via `Matrix.adjugate_mul`
  have hord_zero_ge : O - (s - 1) ≤ Delta_S.rootMultiplicity 0 := by
    let ι_ps : ℤ[X] →+* PowerSeries ℚ :=
      (Polynomial.coeToPowerSeries.ringHom (R := ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))
    let M_ps : Matrix (Fin s) (Fin s) (PowerSeries ℚ) := ι_ps.mapMatrix M_S
    let v : Fin s → PowerSeries ℚ := fun j => unscaledMonomialSeries r β (idxToMulti (eS j).val)
    let L_vec : Fin s → PowerSeries ℚ := fun k => (fun f => (T_rat r M : PowerSeries ℚ) * psDeriv f)^[k.val] L_0
    have hMv : M_ps.mulVec v = L_vec := by
      funext k
      simp only [Matrix.mulVec, dotProduct, M_ps, RingHom.mapMatrix_apply, Matrix.map_apply, M_S,
        Matrix.of_apply, v, L_vec, ι_ps, RingHom.comp_apply, Polynomial.coe_mapRingHom,
        Polynomial.coeToPowerSeries.ringHom_apply]
      have hlin_iter : ∀ (n : ℕ) (S_f : Finset (Fin s)) (F : Fin s → PowerSeries ℚ),
          (fun f => (T_rat r M : PowerSeries ℚ) * psDeriv f)^[n] (∑ j ∈ S_f, F j) =
          ∑ j ∈ S_f, (fun f => (T_rat r M : PowerSeries ℚ) * psDeriv f)^[n] (F j) := by
        intro n
        induction n with
        | zero => intro _ _; rfl
        | succ n ihn =>
          intro S_f F
          rw [Function.iterate_succ_apply', ihn, psDeriv_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _
          rw [Function.iterate_succ_apply']
      dsimp only [L_0]
      rw [hlin_iter k.val Finset.univ]
      apply Finset.sum_congr rfl; intro j _
      exact hiter_ps k.val (eS j).val
    have hadj : M_ps.det • v = M_ps.adjugate.mulVec L_vec := by
      have h1 : (M_ps.det • (1 : Matrix (Fin s) (Fin s) (PowerSeries ℚ))).mulVec v = M_ps.det • v := by
        funext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply, smul_eq_mul]
      rw [← h1, ← Matrix.adjugate_mul, ← Matrix.mulVec_mulVec, hMv]
    have hL_vec_van : ∀ (k : Fin s) (t : ℕ), t < O - (s - 1) → PowerSeries.coeff t (L_vec k) = 0 := by
      have hvan_step : ∀ (n : ℕ) (f : PowerSeries ℚ) (N : ℕ),
          (∀ t ≤ N, PowerSeries.coeff t f = 0) →
          ∀ t, t + n ≤ N → PowerSeries.coeff t ((fun g => (T_rat r M : PowerSeries ℚ) * psDeriv g)^[n] f) = 0 := by
        intro n
        induction n with
        | zero => intro f N hf t ht; exact hf t ht
        | succ n ihn =>
          intro f N hf t ht
          rw [Function.iterate_succ_apply', PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v => PowerSeries.coeff u (T_rat r M : PowerSeries ℚ) * PowerSeries.coeff v (psDeriv ((fun g => (T_rat r M : PowerSeries ℚ) * psDeriv g)^[n] f)))]
          apply Finset.sum_eq_zero; intro u hu
          rw [coeff_psDeriv, ihn f N hf (t - u + 1) (by omega), mul_zero, mul_zero]
      intro k t ht
      exact hvan_step k.val L_0 O hL_0_van t (by have := k.isLt; omega)
    let j₀ : Fin s := ⟨0, by omega⟩
    have hcoord := congrFun hadj j₀
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at hcoord
    have hDelta_van : ∀ t : ℕ, t < O - (s - 1) → Delta_S.coeff t = 0 := by
      intro t
      induction t using Nat.strong_induction_on with
      | h t ih =>
        intro ht
        have hmul0 : PowerSeries.coeff t (M_ps.det * v j₀) = 0 := by
          rw [hcoord, map_sum]
          apply Finset.sum_eq_zero; intro k _
          rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v => PowerSeries.coeff u (M_ps.adjugate j₀ k) * PowerSeries.coeff v (L_vec k))]
          apply Finset.sum_eq_zero; intro u hu
          have htu : t - u < O - (s - 1) := by omega
          rw [hL_vec_van k (t - u) htu, mul_zero]
        rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u w => PowerSeries.coeff u M_ps.det * PowerSeries.coeff w (v j₀))] at hmul0
        rw [Finset.sum_eq_single t] at hmul0
        · have hv0 : PowerSeries.coeff 0 (v j₀) = 1 := by
            rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact unscaledMonomialSeries_const _ _ _
          rw [Nat.sub_self, hv0, mul_one] at hmul0
          have hdet_eq : M_ps.det = ι_ps Delta_S := (RingHom.map_det ι_ps M_S).symm
          rw [hdet_eq] at hmul0
          simp only [ι_ps, RingHom.comp_apply, Polynomial.coe_mapRingHom,
            Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
            Polynomial.coeff_map, eq_intCast, Int.cast_eq_zero] at hmul0
          exact hmul0
        · intro u hu hne
          have hult : u < t := by have := Finset.mem_range.mp hu; omega
          have hdet_eq : M_ps.det = ι_ps Delta_S := (RingHom.map_det ι_ps M_S).symm
          rw [hdet_eq]
          simp only [ι_ps, RingHom.comp_apply, Polynomial.coe_mapRingHom,
            Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
            Polynomial.coeff_map, eq_intCast, ih u hult (lt_trans hult ht), Int.cast_zero, zero_mul]
        · intro habs; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self t)) habs
    have hX_dvd : Polynomial.X ^ (O - (s - 1)) ∣ Delta_S := by
      rw [Polynomial.X_pow_dvd_iff]
      exact hDelta_van
    exact (Polynomial.le_rootMultiplicity_iff hDelta_ne_zero).mpr (by simpa using hX_dvd)
  -- 4. Package `SupportWronskianData`
  let Delta_Q : Polynomial ℚ := Delta_S.map (Int.castRingHom ℚ)
  have hDelta_Q_ne : Delta_Q ≠ 0 := by
    intro h0; apply hDelta_ne_zero; ext k
    have := congrArg (fun P : Polynomial ℚ => P.coeff k) h0
    simp only [Delta_Q, Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast, Int.cast_eq_zero] at this
    exact this
  have hDelta_Q_deg : Delta_Q.natDegree = Delta_S.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective Delta_S
  have hord_Q_eq : Delta_Q.rootMultiplicity 0 = Delta_S.rootMultiplicity 0 := by
    apply le_antisymm
    · rw [Polynomial.le_rootMultiplicity_iff hDelta_ne_zero]
      have hdvd := Polynomial.pow_rootMultiplicity_dvd Delta_Q 0
      simp only [map_zero, sub_zero] at hdvd ⊢
      rw [Polynomial.X_pow_dvd_iff] at hdvd ⊢
      intro k hk
      have h0 := hdvd k hk
      simp only [Delta_Q, Polynomial.coeff_map, eq_intCast, Int.cast_eq_zero] at h0
      exact h0
    · rw [Polynomial.le_rootMultiplicity_iff hDelta_Q_ne]
      have hdvd := Polynomial.pow_rootMultiplicity_dvd Delta_S 0
      simp only [map_zero, sub_zero] at hdvd ⊢
      rw [Polynomial.X_pow_dvd_iff] at hdvd ⊢
      intro k hk
      simp only [Delta_Q, Polynomial.coeff_map, eq_intCast, hdvd k hk, Int.cast_zero]
  exact
  { Delta := Delta_S
    Delta_ne_zero := hDelta_ne_zero
    deg_le := hdeg_le
    ord_zero := Delta_S.rootMultiplicity 0
    ord_zero_ge := hord_zero_ge
    ord_zero_le_deg := by
      have h1 := rootMultiplicity_zero_add_sum_le hDelta_Q_ne ∅ (fun _ hn => absurd hn (Finset.notMem_empty _))
      rw [hord_Q_eq, hDelta_Q_deg] at h1; simpa using h1
    multAt := fun n => Delta_Q.rootMultiplicity ((n : ℚ)⁻¹)
    sum_mult_le := fun T hT => by
      have h1 := rootMultiplicity_zero_add_sum_le hDelta_Q_ne T (fun n hn => by have := hT n hn; omega)
      rw [hord_Q_eq, hDelta_Q_deg] at h1
      omega
    prod_linear_dvd := fun T hT => by
      let Q_T : ℤ[X] := ∏ n ∈ T, (Polynomial.C (n : ℤ) * Polynomial.X - 1) ^ (Delta_Q.rootMultiplicity ((n : ℚ)⁻¹))
      have hpow_prim : ∀ (p : ℤ[X]), p.IsPrimitive → ∀ k : ℕ, (p ^ k).IsPrimitive := by
        intro p hp k
        induction k with
        | zero => simp [Polynomial.isPrimitive_one]
        | succ k ihk => rw [pow_succ]; exact ihk.mul hp
      have hQ_prim : Q_T.IsPrimitive := by
        dsimp only [Q_T]
        induction T using Finset.induction_on with
        | empty => simp [Polynomial.isPrimitive_one]
        | @insert a s has ih =>
          rw [Finset.prod_insert has]
          exact Polynomial.IsPrimitive.mul (hpow_prim _ (isPrimitive_C_mul_X_sub_one a) _)
            (ih (fun n hn => hT n (Finset.mem_insert_of_mem hn)))
      rw [Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map (K := ℚ) hQ_prim]
      change (Q_T.map (Int.castRingHom ℚ)) ∣ Delta_Q
      have hmap_Q : Q_T.map (Int.castRingHom ℚ) =
          ∏ n ∈ T, (Polynomial.C (n : ℚ) * Polynomial.X - 1) ^ (Delta_Q.rootMultiplicity ((n : ℚ)⁻¹)) := by
        dsimp only [Q_T]; simp [Polynomial.map_prod]
      rw [hmap_Q]
      -- Pairwise coprime factors in `Polynomial ℚ` each dividing `Delta_Q`
      clear hQ_prim hmap_Q Q_T
      induction T using Finset.induction_on with
      | empty => simp
      | @insert a s has ih =>
        rw [Finset.prod_insert has]
        have ha1 : 1 ≤ a := by have := hT a (Finset.mem_insert_self a s); omega
        have hdvd_a := pow_linear_dvd_of_rootMultiplicity ha1 Delta_Q
        have hdvd_s := ih (fun n hn => hT n (Finset.mem_insert_of_mem hn))
        have hcop : IsCoprime ((Polynomial.C (a : ℚ) * Polynomial.X - 1) ^ Delta_Q.rootMultiplicity ((a : ℚ)⁻¹))
            (∏ n ∈ s, (Polynomial.C (n : ℚ) * Polynomial.X - 1) ^ Delta_Q.rootMultiplicity ((n : ℚ)⁻¹)) := by
          apply IsCoprime.prod_right
          intro b hbs
          apply IsCoprime.pow
          have hab : a ≠ b := fun heq => has (heq ▸ hbs)
          have hdiff_ne : ((b : ℚ) - (a : ℚ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab.symm)
          refine ⟨Polynomial.C (-(((b : ℚ) - (a : ℚ))⁻¹ * (b : ℚ))),
            Polynomial.C (((b : ℚ) - (a : ℚ))⁻¹ * (a : ℚ)), ?_⟩
          have hc1 : (-(((b : ℚ) - (a : ℚ))⁻¹ * (b : ℚ))) * (a : ℚ) +
              (((b : ℚ) - (a : ℚ))⁻¹ * (a : ℚ)) * (b : ℚ) = 0 := by ring
          have hc0 : -(-(((b : ℚ) - (a : ℚ))⁻¹ * (b : ℚ))) -
              (((b : ℚ) - (a : ℚ))⁻¹ * (a : ℚ)) = 1 := by
            field_simp [hdiff_ne]
          calc Polynomial.C (-(((b : ℚ) - (a : ℚ))⁻¹ * (b : ℚ))) * (Polynomial.C (a : ℚ) * Polynomial.X - 1) +
                Polynomial.C (((b : ℚ) - (a : ℚ))⁻¹ * (a : ℚ)) * (Polynomial.C (b : ℚ) * Polynomial.X - 1)
              = Polynomial.C ((-(((b : ℚ) - (a : ℚ))⁻¹ * (b : ℚ))) * (a : ℚ) +
                  (((b : ℚ) - (a : ℚ))⁻¹ * (a : ℚ)) * (b : ℚ)) * Polynomial.X +
                Polynomial.C (-(-(((b : ℚ) - (a : ℚ))⁻¹ * (b : ℚ))) -
                  (((b : ℚ) - (a : ℚ))⁻¹ * (a : ℚ))) := by
                  simp only [Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_neg]; ring
            _ = 1 := by rw [hc1, hc0, map_zero, zero_mul, zero_add, map_one]
        exact hcop.mul_dvd hdvd_a hdvd_s
    C_Q := max 1 |(Delta_S.leadingCoeff : ℝ)|
    C_Q_ge_one := le_max_left 1 _
    lead_bound := by
      have hchoose_ge1 : 1 ≤ Nat.choose s 2 := by
        have : 2 ≤ s := hs_ge2
        have h1 : Nat.choose 2 2 ≤ Nat.choose s 2 := Nat.choose_le_choose 2 this
        simpa using h1
      have hfac_ge1 : (1 : ℝ) ≤ (Nat.factorial s : ℝ) := by exact_mod_cast Nat.factorial_pos s
      have hDM_ge1 : (1 : ℝ) ≤ ((D + s * M : ℕ) : ℝ) ^ (s ^ 2) :=
        one_le_pow₀ (by exact_mod_cast (show 1 ≤ D + s * M by omega))
      have hH_ge1 : (1 : ℝ) ≤ (((D + 1) * B + 1 : ℕ) : ℝ) ^ s :=
        one_le_pow₀ (by exact_mod_cast (show 1 ≤ (D + 1) * B + 1 by omega))
      have hCQ_ge1 : (1 : ℝ) ≤ max 1 |(Delta_S.leadingCoeff : ℝ)| := le_max_left 1 _
      have hCQ_pow : max 1 |(Delta_S.leadingCoeff : ℝ)| ≤ (max 1 |(Delta_S.leadingCoeff : ℝ)|) ^ (Nat.choose s 2) :=
        le_self_pow₀ hCQ_ge1 (by omega)
      have hlead_le : |(Delta_S.leadingCoeff : ℝ)| ≤ (max 1 |(Delta_S.leadingCoeff : ℝ)|) ^ (Nat.choose s 2) :=
        le_trans (le_max_right 1 _) hCQ_pow
      have hprod_ge1 : (1 : ℝ) ≤ (Nat.factorial s : ℝ) * ((D + s * M : ℕ) : ℝ) ^ (s ^ 2) *
          (((D + 1) * B + 1 : ℕ) : ℝ) ^ s := by
        nlinarith [mul_le_mul hfac_ge1 hDM_ge1 (by positivity) (by positivity)]
      calc |(Delta_S.leadingCoeff : ℝ)|
          ≤ 1 * (max 1 |(Delta_S.leadingCoeff : ℝ)|) ^ (Nat.choose s 2) := by simpa using hlead_le
        _ ≤ ((Nat.factorial s : ℝ) * ((D + s * M : ℕ) : ℝ) ^ (s ^ 2) *
              (((D + 1) * B + 1 : ℕ) : ℝ) ^ s) *
            (max 1 |(Delta_S.leadingCoeff : ℝ)|) ^ (Nat.choose s 2) :=
            mul_le_mul_of_nonneg_right hprod_ge1 (by positivity) }

end GrasGreenbergBrocard
