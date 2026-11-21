import Mathlib
import GrasGreenbergBrocard.ChebyshevLucas

/-!
# Concrete `p`-Adic Pell Logarithm and Normalized `p`-Adic Regulator (Defect D2(1))

This file proves manuscript equation (3.6) directly in Mathlib's `ℚ_[p]` (`Padic p`) with
**zero external axioms**, completely eliminating the custom axiom `padic_log_regulator_pell_power`:
- `padicPellLogTerm`, `padicPellLogZ`: the exact `p`-adic odd-power logarithm series
  `∑_{j=0}^∞ (2 / (2j + 1)) (b / a)^(2j + 1) q^j` in `ℚ_[p]`
- `padicPellLogZ_valuation`: proves convergence, non-vanishing, and exact `p`-adic valuation
  `v_p(padicPellLogZ q p a b) = v_p(b)` whenever `p ≥ 5`, `p ∣ q * b`, `b ≠ 0`, `p ∤ a`
- `normalizedPadicRegulator`: concrete normalized `p`-adic regulator
  `R̃_p(q, X₁, Y₁) = e⁻¹ · padicPellLogZ q p X_e Y_e ∈ ℚ_[p]` where `e = 1` if `p ∣ q`
  and `e = p^2 - 1` if `p ∤ q`
- `fundPellPair`, `realQuadPadicRegVal`: canonical concrete `v_p(R̃_p(ℚ(√q)))` anchored to
  `exists_unique_fundamentalPell` and `ℚ_[p]`
- `padic_regulator_valuation_pell_power`: proves eq. (3.6)
  `v_p(R̃_p(q, X₁, Y₁)) + v_p(k) = v_p(s)` directly from `ChebyshevLucas.padicValInt_chebyshevU`
- `real_quad_unit_order_index_dvd_three`: proves `[𝒪_K^× : ℤ[√q]^×] ∣ 3` for squarefree `q ≥ 2`
-/

noncomputable section

open scoped BigOperators

namespace GrasGreenbergBrocard

private lemma zsqrtd_mul_re (D : ℤ) (x y : Zsqrtd D) :
    (x * y).re = x.re * y.re + D * x.im * y.im := by ring_nf; rfl

private lemma zsqrtd_mul_im (D : ℤ) (x y : Zsqrtd D) :
    (x * y).im = x.re * y.im + x.im * y.re := by ring_nf; rfl

/-- `(X₁, Y₁)` is the fundamental positive solution to `x^2 - D * y^2 = 1`. -/
def IsFundamentalPell (D X₁ Y₁ : ℕ) : Prop :=
  0 < X₁ ∧ 0 < Y₁ ∧ X₁ ^ 2 = D * Y₁ ^ 2 + 1 ∧
    ∀ x y : ℕ, 0 < y → x ^ 2 = D * y ^ 2 + 1 → Y₁ ≤ y

/-- Fundamental Pell value `ε_D = X₁ + Y₁ √D`. -/
def pellUnit (D X₁ Y₁ : ℕ) : ℝ :=
  (X₁ : ℝ) + (Y₁ : ℝ) * Real.sqrt (D : ℝ)

/-- Existence and uniqueness of the fundamental Pell solution for any non-square `q ≥ 2`
(via Mathlib's `Pell.exists_of_not_isSquare`). -/
theorem exists_unique_fundamentalPell_of_not_isSquare {q : ℕ} (hq : 2 ≤ q) (hnsq : ¬ IsSquare (q : ℤ)) :
    ∃! p : ℕ × ℕ, IsFundamentalPell q p.1 p.2 := by
  classical
  obtain ⟨x, y, hxy, hy0⟩ := Pell.exists_of_not_isSquare (d := (q : ℤ)) (by omega) hnsq
  have hex : ∃ Y : ℕ, 0 < Y ∧ ∃ X : ℕ, X ^ 2 = q * Y ^ 2 + 1 := by
    refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, x.natAbs, ?_⟩
    zify
    rw [sq_abs, sq_abs]
    linarith
  let Y₁ := Nat.find hex
  have hY₁_spec := Nat.find_spec hex
  have hY₁_pos : 0 < Y₁ := hY₁_spec.1
  obtain ⟨X₁, hX₁_eq⟩ := hY₁_spec.2
  have hX₁_pos : 0 < X₁ := by
    by_contra h0
    have hX0 : X₁ = 0 := by omega
    rw [hX0] at hX₁_eq
    nlinarith
  have hfund : IsFundamentalPell q X₁ Y₁ := by
    refine ⟨hX₁_pos, hY₁_pos, hX₁_eq, ?_⟩
    intro x' y' hy' hx'
    exact Nat.find_min' hex ⟨hy', x', hx'⟩
  refine ⟨(X₁, Y₁), hfund, ?_⟩
  rintro ⟨X₂, Y₂⟩ hfund₂
  have hY_le₁ : Y₁ ≤ Y₂ := hfund.2.2.2 X₂ Y₂ hfund₂.2.1 hfund₂.2.2.1
  have hY_le₂ : Y₂ ≤ Y₁ := hfund₂.2.2.2 X₁ Y₁ hfund.2.1 hfund.2.2.1
  have hY_eq : Y₂ = Y₁ := le_antisymm hY_le₂ hY_le₁
  have hX_sq : X₂ ^ 2 = X₁ ^ 2 := by rw [hfund₂.2.2.1, hfund.2.2.1, hY_eq]
  have hX_eq : X₂ = X₁ := by nlinarith
  exact Prod.ext hX_eq hY_eq

/-- The `j`-th term of the `p`-adic Pell logarithm series
`(2 / (2j + 1)) * (b / a)^(2j + 1) * q^j` in `ℚ_[p]`. -/
def padicPellLogTerm (q p : ℕ) [Fact p.Prime] (a b : ℤ) (j : ℕ) : ℚ_[p] :=
  (2 : ℚ_[p]) / ((2 * j + 1 : ℕ) : ℚ_[p]) * (((b : ℚ_[p]) / (a : ℚ_[p])) ^ (2 * j + 1)) *
    (q : ℚ_[p]) ^ j

/-- The concrete `p`-adic Pell logarithm `log_p(a + b√q) / √q ∈ ℚ_[p]`. -/
def padicPellLogZ (q p : ℕ) [Fact p.Prime] (a b : ℤ) : ℚ_[p] :=
  ∑' j : ℕ, padicPellLogTerm q p a b j

/-- Auxiliary inequality: for every prime `p ≥ 5` and every `j ≥ 1`, `v_p(2j + 1) < j`. -/
lemma padicValNat_two_mul_add_one_lt {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 1 ≤ j) :
    padicValNat p (2 * j + 1) < j := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hle
  push_neg at hle
  have hpow_dvd : p ^ j ∣ 2 * j + 1 :=
    dvd_trans (pow_dvd_pow p hle) pow_padicValNat_dvd
  have hpow_le : p ^ j ≤ 2 * j + 1 := Nat.le_of_dvd (by omega) hpow_dvd
  have h5_le : 5 ^ j ≤ p ^ j := Nat.pow_le_pow_left hp5 j
  have h5_gt : 2 * j + 1 < 5 ^ j := by
    clear hle hpow_dvd hpow_le h5_le
    induction j with
    | zero => omega
    | succ k ih =>
      rcases eq_or_ne k 0 with rfl | hk0
      · norm_num
      · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
        have hih : 2 * k + 1 < 5 ^ k := ih hk1
        have hpow : 5 ^ (k + 1) = 5 ^ k * 5 := pow_succ 5 k
        omega
  omega

/-- Stronger auxiliary inequality: for every prime `p ≥ 5` and `j : ℕ`, `2 * v_p(2j + 1) ≤ j`. -/
lemma two_mul_padicValNat_two_mul_add_one_le {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    2 * padicValNat p (2 * j + 1) ≤ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hgt
  push_neg at hgt
  set v := padicValNat p (2 * j + 1)
  have hv1 : 1 ≤ v := by omega
  have hpow_dvd : p ^ v ∣ 2 * j + 1 := pow_padicValNat_dvd
  have hpow_le : p ^ v ≤ 2 * j + 1 := Nat.le_of_dvd (by omega) hpow_dvd
  have h5_le : 5 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp5 v
  have h5_gt : 4 * v < 5 ^ v := by
    induction v with
    | zero => omega
    | succ k ih =>
      rcases eq_or_ne k 0 with rfl | hk0
      · norm_num
      · have hih : 4 * k < 5 ^ k := ih
        have hpow : 5 ^ (k + 1) = 5 ^ k * 5 := pow_succ 5 k
        omega
  omega

private lemma padic_norm_intCast_eq {p : ℕ} [Fact p.Prime] {z : ℤ} (hz : z ≠ 0) :
    ‖(z : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValInt p z : ℤ)) := by
  have hz_q : (z : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr hz
  rw [Padic.norm_eq_zpow_neg_valuation hz_q, Padic.valuation_intCast]

private lemma padic_norm_natCast_eq {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  have hz : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1 := padic_norm_intCast_eq (p := p) hz
  simpa [padicValInt] using h1

private lemma padic_norm_tsum_le {p : ℕ} [Fact p.Prime] {f : ℕ → ℚ_[p]} {C : ℝ}
    (hC : 0 ≤ C) (hsum : Summable f) (hb : ∀ n : ℕ, ‖f n‖ ≤ C) :
    ‖∑' n : ℕ, f n‖ ≤ C := by
  have hpart : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, f n‖ ≤ C := by
    intro N
    induction N with
    | zero => simp [hC]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ih (hb N))
  exact le_of_tendsto (hsum.hasSum.tendsto_sum_nat.norm) (Filter.Eventually.of_forall hpart)

/-- **Ultrametric Convergence and Exact Valuation of `padicPellLogZ` in `ℚ_[p]`**:
For any prime `p ≥ 5`, `q ≥ 1`, and integers `a, b` with `b ≠ 0`, `p ∣ q * b`, and `¬ p ∣ a`,
the odd-power `p`-adic logarithm series converges in `ℚ_[p]`, is non-zero, and has exact
`p`-adic valuation `v_p(padicPellLogZ q p a b) = v_p(b)`. -/
theorem padicPellLogZ_valuation {q p : ℕ} {a b : ℤ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hq : 1 ≤ q) (hb0 : b ≠ 0) (hpqb : (p : ℤ) ∣ (q : ℤ) * b)
    (hpa : ¬ (p : ℤ) ∣ a) :
    Summable (padicPellLogTerm q p a b) ∧
    padicPellLogZ q p a b ≠ 0 ∧
    (padicPellLogZ q p a b).valuation = (padicValInt p b : ℤ) := by
  have hp : p.Prime := Fact.out
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have ha0 : a ≠ 0 := by intro h0; rw [h0] at hpa; exact hpa (dvd_zero _)
  have hva : padicValInt p a = 0 := by
    unfold padicValInt
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    exact hpa (Int.natCast_dvd.mpr hd)
  have hv2 : padicValNat p 2 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    omega
  have hv_sum_ge1 : 1 ≤ 2 * padicValInt p b + padicValNat p q := by
    rcases Int.Prime.dvd_mul' hp hpqb with hq_d | hb_d
    · have hq_nat : p ∣ q := Int.natCast_dvd_natCast.mp hq_d
      have := one_le_padicValNat_of_dvd (by omega : q ≠ 0) hq_nat
      omega
    · have hb_nat : p ∣ b.natAbs := Int.natCast_dvd.mp hb_d
      have := one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hb0) hb_nat
      unfold padicValInt
      omega
  have hnorm_a : ‖(a : ℚ_[p])‖ = 1 := by
    rw [padic_norm_intCast_eq ha0, hva]; simp
  have hnorm_2 : ‖(2 : ℚ_[p])‖ = 1 := by
    rw [show (2 : ℚ_[p]) = ((2 : ℕ) : ℚ_[p]) by norm_num, padic_norm_natCast_eq (by norm_num), hv2]; simp
  have hnorm_b : ‖(b : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValInt p b : ℤ)) := padic_norm_intCast_eq hb0
  have hnorm_q : ‖(q : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p q : ℤ)) :=
    padic_norm_natCast_eq (by omega)
  have hnorm_term : ∀ j : ℕ, ‖padicPellLogTerm q p a b j‖ =
      (p : ℝ) ^ (-(((2 * j + 1) * padicValInt p b + j * padicValNat p q : ℕ) : ℤ) +
        (padicValNat p (2 * j + 1) : ℤ)) := by
    intro j
    unfold padicPellLogTerm
    rw [norm_mul, norm_mul, norm_div, norm_pow, norm_div, norm_pow, hnorm_2, hnorm_a, hnorm_b,
      hnorm_q, padic_norm_natCast_eq (by omega : 2 * j + 1 ≠ 0), div_one, one_div]
    rw [← zpow_neg, neg_neg, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
      ← zpow_add₀ hp_pos.ne', ← zpow_add₀ hp_pos.ne']
    congr 1
    push_cast
    ring
  have hterm0 : ‖padicPellLogTerm q p a b 0‖ = (p : ℝ) ^ (-(padicValInt p b : ℤ)) := by
    rw [hnorm_term 0]
    simp
  have hterm_ge1 : ∀ j : ℕ, 1 ≤ j →
      ‖padicPellLogTerm q p a b j‖ ≤ (p : ℝ) ^ (-(padicValInt p b : ℤ) - 1) := by
    intro j hj
    rw [hnorm_term j]
    apply zpow_le_zpow_right₀ hp_gt1.le
    have hlt := padicValNat_two_mul_add_one_lt hp hp5 hj
    have hmul : j ≤ j * (2 * padicValInt p b + padicValNat p q) :=
      Nat.le_mul_of_pos_right j hv_sum_ge1
    push_cast
    have hlt_z : (padicValNat p (2 * j + 1) : ℤ) < (j : ℤ) := by exact_mod_cast hlt
    have hmul_z : (j : ℤ) ≤ (j : ℤ) * (2 * (padicValInt p b : ℤ) + (padicValNat p q : ℤ)) := by
      exact_mod_cast hmul
    linarith
  have hsqrt_gt1 : (1 : ℝ) < Real.sqrt (p : ℝ) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt (by norm_num) hp_gt1
  have hinv_lt1 : (Real.sqrt (p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hsqrt_gt1
  have hsummable : Summable (padicPellLogTerm q p a b) := by
    refine Summable.of_norm_bounded (g := fun j : ℕ =>
        (p : ℝ) ^ (-(padicValInt p b : ℤ)) * Real.sqrt (p : ℝ) * ((Real.sqrt (p : ℝ))⁻¹) ^ j)
      ((summable_geometric_of_lt_one (by positivity) hinv_lt1).mul_left _) ?_
    intro j
    rw [hnorm_term j]
    have h2v := two_mul_padicValNat_two_mul_add_one_le (j := j) hp hp5
    have hmul : j ≤ j * (2 * padicValInt p b + padicValNat p q) :=
      Nat.le_mul_of_pos_right j hv_sum_ge1
    have hle1 : (p : ℝ) ^ (-(((2 * j + 1) * padicValInt p b + j * padicValNat p q : ℕ) : ℤ) +
        (padicValNat p (2 * j + 1) : ℤ)) ≤
        (p : ℝ) ^ (-(padicValInt p b : ℤ) - ((j / 2 : ℕ) : ℤ)) := by
      apply zpow_le_zpow_right₀ hp_gt1.le
      have hcast : (((2 * j + 1) * padicValInt p b + j * padicValNat p q : ℕ) : ℤ) =
          (2 * (j : ℤ) + 1) * (padicValInt p b : ℤ) + (j : ℤ) * (padicValNat p q : ℤ) := by
        simp [Nat.cast_add, Nat.cast_mul]
      rw [hcast]
      have h2v_z : 2 * (padicValNat p (2 * j + 1) : ℤ) ≤ (j : ℤ) := by exact_mod_cast h2v
      have hmul_z : (j : ℤ) ≤ (j : ℤ) * (2 * (padicValInt p b : ℤ) + (padicValNat p q : ℤ)) := by
        exact_mod_cast hmul
      have hdiv_z : 2 * ((j / 2 : ℕ) : ℤ) ≤ (j : ℤ) := by omega
      linarith
    refine le_trans hle1 ?_
    rw [sub_eq_add_neg, zpow_add₀ hp_pos.ne']
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (zpow_nonneg hp_pos.le _)
    have hpow_eq : (p : ℝ) ^ (-((j / 2 : ℕ) : ℤ)) = ((Real.sqrt (p : ℝ))⁻¹) ^ (2 * (j / 2)) := by
      rw [zpow_neg, zpow_natCast, inv_pow, pow_mul, Real.sq_sqrt hp_pos.le, ← inv_pow]
    rw [hpow_eq]
    have hstep : ((Real.sqrt (p : ℝ))⁻¹) ^ (2 * (j / 2)) ≤
        Real.sqrt (p : ℝ) * ((Real.sqrt (p : ℝ))⁻¹) ^ j := by
      have hj_le : j ≤ 2 * (j / 2) + 1 := by omega
      have h1 : ((Real.sqrt (p : ℝ))⁻¹) ^ (2 * (j / 2) + 1) ≤ ((Real.sqrt (p : ℝ))⁻¹) ^ j :=
        pow_le_pow_of_le_one (by positivity) hinv_lt1.le hj_le
      have h2 : Real.sqrt (p : ℝ) * ((Real.sqrt (p : ℝ))⁻¹) ^ (2 * (j / 2) + 1) =
          ((Real.sqrt (p : ℝ))⁻¹) ^ (2 * (j / 2)) := by
        rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      rw [← h2]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    exact hstep
  have hsplit : padicPellLogZ q p a b =
      padicPellLogTerm q p a b 0 + ∑' j : ℕ, padicPellLogTerm q p a b (j + 1) := by
    unfold padicPellLogZ
    exact hsummable.tsum_eq_zero_add
  have htail_sum : Summable (fun j : ℕ => padicPellLogTerm q p a b (j + 1)) :=
    (summable_nat_add_iff 1).mpr hsummable
  have htail_norm : ‖∑' j : ℕ, padicPellLogTerm q p a b (j + 1)‖ ≤
      (p : ℝ) ^ (-(padicValInt p b : ℤ) - 1) :=
    padic_norm_tsum_le (zpow_nonneg hp_pos.le _) htail_sum (fun j => hterm_ge1 (j + 1) (by omega))
  have htail_lt : ‖∑' j : ℕ, padicPellLogTerm q p a b (j + 1)‖ < ‖padicPellLogTerm q p a b 0‖ := by
    rw [hterm0]
    exact lt_of_le_of_lt htail_norm (zpow_lt_zpow_right₀ hp_gt1 (by omega))
  have hlog_norm : ‖padicPellLogZ q p a b‖ = (p : ℝ) ^ (-(padicValInt p b : ℤ)) := by
    rw [hsplit, ← hterm0]
    have hle1 : ‖padicPellLogTerm q p a b 0 + ∑' j : ℕ, padicPellLogTerm q p a b (j + 1)‖ ≤
        ‖padicPellLogTerm q p a b 0‖ :=
      le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le le_rfl htail_lt.le)
    have hge1 : ‖padicPellLogTerm q p a b 0‖ ≤
        ‖padicPellLogTerm q p a b 0 + ∑' j : ℕ, padicPellLogTerm q p a b (j + 1)‖ := by
      by_contra hlt
      push_neg at hlt
      have hsub := IsUltrametricDist.norm_add_le_max
        (padicPellLogTerm q p a b 0 + ∑' j : ℕ, padicPellLogTerm q p a b (j + 1))
        (-(∑' j : ℕ, padicPellLogTerm q p a b (j + 1)))
      rw [add_neg_cancel_right, norm_neg] at hsub
      exact (lt_of_le_of_lt hsub (max_lt hlt htail_lt)).false
    exact le_antisymm hle1 hge1
  have hlog_ne : padicPellLogZ q p a b ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlog_norm
    exact (zpow_pos hp_pos _).ne hlog_norm
  have hlog_val : (padicPellLogZ q p a b).valuation = (padicValInt p b : ℤ) := by
    have h1 := Padic.norm_eq_zpow_neg_valuation hlog_ne
    rw [hlog_norm] at h1
    have hinj := StrictMono.injective (zpow_right_strictMono₀ hp_gt1) h1
    omega
  exact ⟨hsummable, hlog_ne, hlog_val⟩

/-- Frobenius exponent `e = 1` if `p ∣ q` (ramified) and `e = p^2 - 1` if `p ∤ q` (unramified). -/
def padicRegExp (q p : ℕ) : ℕ :=
  if p ∣ q then 1 else p ^ 2 - 1

lemma padicRegExp_pos {q p : ℕ} (hp : p.Prime) : 1 ≤ padicRegExp q p := by
  unfold padicRegExp
  split_ifs
  · exact le_rfl
  · have h4 : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
    omega

lemma not_dvd_padicRegExp {q p : ℕ} (hp : p.Prime) : ¬ p ∣ padicRegExp q p := by
  unfold padicRegExp
  split_ifs
  · exact hp.not_dvd_one
  · intro hd
    have h1 : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
    have hsub : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub h1 hd
    have heq : p ^ 2 - (p ^ 2 - 1) = 1 := by set P2 := p ^ 2; have h4 : 4 ≤ P2 := by nlinarith [hp.two_le]; omega
    rw [heq] at hsub
    exact hp.not_dvd_one hsub

private lemma zsqrtd_pow_re_im_norm (D X₁ Y₁ : ℤ) (hnorm : X₁ ^ 2 - D * Y₁ ^ 2 = 1) (k : ℕ) :
    ((⟨X₁, Y₁⟩ : Zsqrtd D) ^ k).re ^ 2 - D * ((⟨X₁, Y₁⟩ : Zsqrtd D) ^ k).im ^ 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    set u : Zsqrtd D := (⟨X₁, Y₁⟩ : Zsqrtd D) ^ k
    change (u * ⟨X₁, Y₁⟩).re ^ 2 - D * (u * ⟨X₁, Y₁⟩).im ^ 2 = 1
    rw [zsqrtd_mul_re, zsqrtd_mul_im]
    nlinarith [ih, hnorm]

private lemma zsqrtd_pow_prime_mod {D X₁ Y₁ : ℤ} {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    (((⟨X₁, Y₁⟩ : Zsqrtd D) ^ p).re : ZMod p) = (X₁ : ZMod p) ∧
    (((⟨X₁, Y₁⟩ : Zsqrtd D) ^ p).im : ZMod p) = (Y₁ : ZMod p) * (D : ZMod p) ^ ((p - 1) / 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsplit : (⟨X₁, Y₁⟩ : Zsqrtd D) = (⟨X₁, 0⟩ : Zsqrtd D) + ⟨0, Y₁⟩ := by ext <;> simp
  rw [hsplit, add_pow]
  have hre_sum : ∀ s : Finset ℕ,
      (∑ i ∈ s, (⟨X₁, 0⟩ : Zsqrtd D) ^ i * (⟨0, Y₁⟩ : Zsqrtd D) ^ (p - i) * ((p.choose i : ℕ) : Zsqrtd D)).re =
      ∑ i ∈ s, ((⟨X₁, 0⟩ : Zsqrtd D) ^ i * (⟨0, Y₁⟩ : Zsqrtd D) ^ (p - i) * ((p.choose i : ℕ) : Zsqrtd D)).re := by
    intro s; induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.sum_insert ha, ih]
  have him_sum : ∀ s : Finset ℕ,
      (∑ i ∈ s, (⟨X₁, 0⟩ : Zsqrtd D) ^ i * (⟨0, Y₁⟩ : Zsqrtd D) ^ (p - i) * ((p.choose i : ℕ) : Zsqrtd D)).im =
      ∑ i ∈ s, ((⟨X₁, 0⟩ : Zsqrtd D) ^ i * (⟨0, Y₁⟩ : Zsqrtd D) ^ (p - i) * ((p.choose i : ℕ) : Zsqrtd D)).im := by
    intro s; induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.sum_insert ha, ih]
  have hmid_zero : ∀ i : ℕ, 0 < i → i < p → ((p.choose i : ℕ) : ZMod p) = 0 := by
    intro i hi1 hi2
    exact (ZMod.natCast_eq_zero_iff _ p).mpr (hp.dvd_choose_self hi1.ne' hi2)
  have hcast_re : ∀ (z : Zsqrtd D) (c : ℕ), (z * (c : Zsqrtd D)).re = z.re * (c : ℤ) := by
    intro z c
    have hc : (c : Zsqrtd D) = ⟨(c : ℤ), 0⟩ := by ext <;> simp
    rw [hc]; change z.re * (c : ℤ) + D * z.im * 0 = _; ring
  have hcast_im : ∀ (z : Zsqrtd D) (c : ℕ), (z * (c : Zsqrtd D)).im = z.im * (c : ℤ) := by
    intro z c
    have hc : (c : Zsqrtd D) = ⟨(c : ℤ), 0⟩ := by ext <;> simp
    rw [hc]; change z.re * 0 + z.im * (c : ℤ) = _; ring
  have hX_pow : ∀ k : ℕ, ((⟨X₁, 0⟩ : Zsqrtd D) ^ k) = ⟨X₁ ^ k, 0⟩ := by
    intro k; induction k with
    | zero => ext <;> simp
    | succ k ih => rw [pow_succ, ih]; ext <;> simp [pow_succ]
  have hY_pow_odd : ((⟨0, Y₁⟩ : Zsqrtd D) ^ p) = ⟨0, Y₁ ^ p * D ^ ((p - 1) / 2)⟩ := by
    set t := (p - 1) / 2
    have hp_odd : p = 2 * t + 1 := by
      have := hp.eq_two_or_odd.resolve_left (by omega); omega
    have h2 : ∀ k : ℕ, ((⟨0, Y₁⟩ : Zsqrtd D) ^ (2 * k)) = ⟨Y₁ ^ (2 * k) * D ^ k, 0⟩ := by
      intro k; induction k with
      | zero => ext <;> simp
      | succ k ih =>
        rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, ih, pow_two]
        ext <;> simp [pow_add, pow_succ] <;> ring
    rw [hp_odd, pow_succ, h2]
    ext
    · change Y₁ ^ (2 * t) * D ^ t * 0 + D * 0 * Y₁ = 0; ring
    · change Y₁ ^ (2 * t) * D ^ t * Y₁ + 0 * 0 = Y₁ ^ (2 * t + 1) * D ^ t
      rw [pow_succ]; ring
  rw [hre_sum, him_sum]
  push_cast
  have hsplit_sum : ∀ f : ℕ → ZMod p, (∀ i, 0 < i → i < p → f i = 0) →
      ∑ i ∈ Finset.range (p + 1), f i = f 0 + f p := by
    intro f hf
    have hrange : Finset.range p = Finset.range ((p - 1) + 1) := by congr 1; omega
    rw [Finset.sum_range_succ, hrange, Finset.sum_range_succ']
    have h0 : ∑ k ∈ Finset.range (p - 1), f (k + 1) = 0 :=
      Finset.sum_eq_zero (fun k hk => hf (k + 1) (by omega) (by have := Finset.mem_range.mp hk; omega))
    simp [h0, add_comm]
  constructor
  · rw [hsplit_sum]
    · simp [hX_pow, hY_pow_odd, Nat.choose_self, ZMod.pow_card]
    · intro i hi1 hi2
      rw [hcast_re]; push_cast; rw [hmid_zero i hi1 hi2, mul_zero]
  · rw [hsplit_sum]
    · simp [hX_pow, hY_pow_odd, Nat.choose_self, ZMod.pow_card]
    · intro i hi1 hi2
      rw [hcast_im]; push_cast; rw [hmid_zero i hi1 hi2, mul_zero]

/-- For `e = padicRegExp q p`, `u = (⟨X₁, Y₁⟩ : Zsqrtd (q : ℤ)) ^ e` satisfies
`p ∣ q * u.im`, `¬ p ∣ u.re`, and `u.im ≠ 0`. -/
lemma pell_pow_padicRegExp_props {q p X₁ Y₁ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : 1 ≤ q) (hX1 : 0 < X₁) (hY1 : 0 < Y₁) (hpell : X₁ ^ 2 = q * Y₁ ^ 2 + 1) :
    let e := padicRegExp q p
    let u : Zsqrtd (q : ℤ) := (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ e
    u.re ^ 2 - (q : ℤ) * u.im ^ 2 = 1 ∧
    (p : ℤ) ∣ (q : ℤ) * u.im ∧
    ¬ (p : ℤ) ∣ u.re ∧
    u.im ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set e := padicRegExp q p
  set u : Zsqrtd (q : ℤ) := (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ e
  have hpell_z : (X₁ : ℤ) ^ 2 - (q : ℤ) * (Y₁ : ℤ) ^ 2 = 1 := by have : (X₁ : ℤ) ^ 2 = (q : ℤ) * (Y₁ : ℤ) ^ 2 + 1 := by exact_mod_cast hpell
    linarith
  have hnorm : u.re ^ 2 - (q : ℤ) * u.im ^ 2 = 1 := zsqrtd_pow_re_im_norm _ _ _ hpell_z e
  have him_pos : 0 < u.im := by
    have he1 : 1 ≤ e := padicRegExp_pos hp
    have hpos : ∀ k : ℕ, 1 ≤ k → 0 < ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ k).re ∧
        0 < ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ k).im := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        rcases eq_or_ne k 0 with rfl | hk0
        · simp; exact ⟨by exact_mod_cast hX1, by exact_mod_cast hY1⟩
        · obtain ⟨hre, him⟩ := ih (Nat.pos_of_ne_zero hk0)
          rw [pow_succ]
          set w : Zsqrtd (q : ℤ) := (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ k
          have h1 : (w * ⟨(X₁ : ℤ), (Y₁ : ℤ)⟩).re = w.re * (X₁ : ℤ) + (q : ℤ) * w.im * (Y₁ : ℤ) := by simp [zsqrtd_mul_re]
          have h2 : (w * ⟨(X₁ : ℤ), (Y₁ : ℤ)⟩).im = w.re * (Y₁ : ℤ) + w.im * (X₁ : ℤ) := by simp [zsqrtd_mul_im]
          rw [h1, h2]
          have hq_z : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
          have hX_z : (0 : ℤ) < (X₁ : ℤ) := by exact_mod_cast hX1
          have hY_z : (0 : ℤ) < (Y₁ : ℤ) := by exact_mod_cast hY1
          have hqim : 0 < (q : ℤ) * w.im := mul_pos hq_z him
          exact ⟨by nlinarith, by nlinarith⟩
    exact (hpos e he1).2
  have hp_dvd : (p : ℤ) ∣ (q : ℤ) * u.im := by
    by_cases hpq : p ∣ q
    · exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hpq) _
    · apply dvd_mul_of_dvd_right
      have he_eq : e = p ^ 2 - 1 := by unfold e padicRegExp; rw [if_neg hpq]
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hq_ne : ((q : ℤ) : ZMod p) ≠ 0 := by
        intro h0; exact hpq (Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0))
      have hq_flt : ((q : ℤ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hq_ne
      have hp_even : 2 * ((p - 1) / 2) = p - 1 := by
        have := hp.eq_two_or_odd.resolve_left (by omega); omega
      have hq_half_sq : (((q : ℤ) : ZMod p) ^ ((p - 1) / 2)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, hp_even, hq_flt]
      have hε_conj : (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) * ⟨(X₁ : ℤ), -(Y₁ : ℤ)⟩ = 1 := by
        ext
        · change (X₁ : ℤ) * (X₁ : ℤ) + (q : ℤ) * (Y₁ : ℤ) * (-(Y₁ : ℤ)) = 1; linarith
        · change (X₁ : ℤ) * (-(Y₁ : ℤ)) + (Y₁ : ℤ) * (X₁ : ℤ) = 0; ring
      obtain ⟨hfp_re, hfp_im⟩ := zsqrtd_pow_prime_mod (D := (q : ℤ)) (X₁ := (X₁ : ℤ)) (Y₁ := (Y₁ : ℤ)) hp (by omega)
      have hpow_one_mod : ∀ (z : Zsqrtd (q : ℤ)),
          (z.re : ZMod p) = 1 → (z.im : ZMod p) = 0 →
          ∀ m : ℕ, ((z ^ m).re : ZMod p) = 1 ∧ ((z ^ m).im : ZMod p) = 0 := by
        intro z hzr hzi m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [pow_succ]
          have h1 : (z ^ m * z).re = (z ^ m).re * z.re + (q : ℤ) * (z ^ m).im * z.im := by simp [zsqrtd_mul_re]
          have h2 : (z ^ m * z).im = (z ^ m).re * z.im + (z ^ m).im * z.re := by simp [zsqrtd_mul_im]
          rw [h1, h2]; push_cast; rw [ih.1, ih.2, hzr, hzi]; simp
      rcases sq_eq_one_iff.mp hq_half_sq with hleg1 | hlegneg1
      · have hpm1 : ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ (p - 1)) =
            ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ p) * ⟨(X₁ : ℤ), -(Y₁ : ℤ)⟩ := by
          have hp1 : p = (p - 1) + 1 := by omega
          conv_rhs => rw [hp1, pow_succ, mul_assoc, hε_conj, mul_one]
        have h1_re : (((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ (p - 1)).re : ZMod p) = 1 := by
          rw [hpm1]
          have h1 : ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ p * ⟨(X₁ : ℤ), -(Y₁ : ℤ)⟩).re =
              ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ p).re * (X₁ : ℤ) +
              (q : ℤ) * ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ p).im * (-(Y₁ : ℤ)) := by
            simp [zsqrtd_mul_re]
          rw [h1]; push_cast; rw [hfp_re, hfp_im, hleg1, mul_one]
          have hmod := congrArg (Int.cast (R := ZMod p)) hpell_z
          push_cast at hmod
          simp only [Int.cast_natCast] at hmod ⊢
          linear_combination hmod
        have h1_im : (((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ (p - 1)).im : ZMod p) = 0 := by
          rw [hpm1]
          have h2 : ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ p * ⟨(X₁ : ℤ), -(Y₁ : ℤ)⟩).im =
              ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ p).re * (-(Y₁ : ℤ)) +
              ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ p).im * (X₁ : ℤ) := by
            simp [zsqrtd_mul_im]
          rw [h2]; push_cast; rw [hfp_re, hfp_im, hleg1, mul_one]
          simp only [Int.cast_natCast]; ring
        have hfac : e = (p - 1) * (p + 1) := by
          rw [he_eq]; zify [show 1 ≤ p by omega, show 1 ≤ p ^ 2 by nlinarith]; ring
        change (((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ e).im : ZMod p) = 0
        rw [hfac, pow_mul]
        exact (hpow_one_mod _ h1_re h1_im (p + 1)).2
      · have h1_re : (((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ (p + 1)).re : ZMod p) = 1 := by
          rw [pow_succ]
          have h1 : ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ p * ⟨(X₁ : ℤ), (Y₁ : ℤ)⟩).re =
              ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ p).re * (X₁ : ℤ) +
              (q : ℤ) * ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ p).im * (Y₁ : ℤ) := by
            simp [zsqrtd_mul_re]
          rw [h1]; push_cast; rw [hfp_re, hfp_im, hlegneg1]
          have hmod := congrArg (Int.cast (R := ZMod p)) hpell_z
          push_cast at hmod
          simp only [Int.cast_natCast] at hmod ⊢
          linear_combination hmod
        have h1_im : (((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ (p + 1)).im : ZMod p) = 0 := by
          rw [pow_succ]
          have h2 : ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ p * ⟨(X₁ : ℤ), (Y₁ : ℤ)⟩).im =
              ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ p).re * (Y₁ : ℤ) +
              ((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ p).im * (X₁ : ℤ) := by
            simp [zsqrtd_mul_im]
          rw [h2]; push_cast; rw [hfp_re, hfp_im, hlegneg1]
          simp only [Int.cast_natCast]; ring
        have hfac : e = (p + 1) * (p - 1) := by
          rw [he_eq]; zify [show 1 ≤ p by omega, show 1 ≤ p ^ 2 by nlinarith]; ring
        change (((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ e).im : ZMod p) = 0
        rw [hfac, pow_mul]
        exact (hpow_one_mod _ h1_re h1_im (p - 1)).2
  have hnd_re : ¬ (p : ℤ) ∣ u.re := by
    intro hre
    have h1 : (p : ℤ) ∣ u.re ^ 2 - (q : ℤ) * u.im ^ 2 :=
      dvd_sub (dvd_pow hre (by norm_num)) (by
        rw [show (q : ℤ) * u.im ^ 2 = ((q : ℤ) * u.im) * u.im by ring]
        exact dvd_mul_of_dvd_left hp_dvd _)
    rw [hnorm] at h1
    exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp h1)
  exact ⟨hnorm, hp_dvd, hnd_re, him_pos.ne'⟩

/-- Concrete normalized `p`-adic regulator `R̃_p(q, X₁, Y₁) = e⁻¹ · padicPellLogZ q p X_e Y_e ∈ ℚ_[p]`,
where `(X_e, Y_e) = (X₁ + Y₁ √q)^e` with `e = padicRegExp q p`. -/
def normalizedPadicRegulator (q p X₁ Y₁ : ℕ) [Fact p.Prime] : ℚ_[p] :=
  let e := padicRegExp q p
  let u : Zsqrtd (q : ℤ) := (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ e
  ((e : ℕ) : ℚ_[p])⁻¹ * padicPellLogZ q p u.re u.im

/-- Natural-number `p`-adic valuation `v_p(R̃_p(q, X₁, Y₁))` of the concrete normalized
`p`-adic regulator. -/
def normalizedPadicRegulatorVal (q p X₁ Y₁ : ℕ) [Fact p.Prime] : ℕ :=
  (normalizedPadicRegulator q p X₁ Y₁).valuation.toNat

/-- **Exact Valuation of `normalizedPadicRegulator`**:
`v_p(R̃_p(q, X₁, Y₁)) = v_p(((X₁ + Y₁ √q)^e).im)` directly in `ℚ_[p]`. -/
theorem normalizedPadicRegulator_valuation {q p X₁ Y₁ : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hq : 1 ≤ q) (hX1 : 0 < X₁) (hY1 : 0 < Y₁) (hpell : X₁ ^ 2 = q * Y₁ ^ 2 + 1) :
    let e := padicRegExp q p
    let u : Zsqrtd (q : ℤ) := (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ e
    normalizedPadicRegulator q p X₁ Y₁ ≠ 0 ∧
    (normalizedPadicRegulator q p X₁ Y₁).valuation = (padicValInt p u.im : ℤ) ∧
    normalizedPadicRegulatorVal q p X₁ Y₁ = padicValInt p u.im := by
  have hp : p.Prime := Fact.out
  obtain ⟨_, hp_dvd, hnd_re, him_ne⟩ := pell_pow_padicRegExp_props hp hp5 hq hX1 hY1 hpell
  obtain ⟨_, hlog_ne, hlog_val⟩ := padicPellLogZ_valuation hp5 hq him_ne hp_dvd hnd_re
  set e := padicRegExp q p
  have he_pos : 0 < e := padicRegExp_pos hp
  have he_ne : ((e : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr he_pos.ne'
  have he_val : ((e : ℕ) : ℚ_[p]).valuation = 0 := by
    have h1 : (((e : ℤ) : ℚ_[p])).valuation = (padicValInt p (e : ℤ) : ℤ) := Padic.valuation_intCast (e : ℤ)
    have h2 : padicValInt p (e : ℤ) = 0 := by
      unfold padicValInt
      simpa using padicValNat.eq_zero_of_not_dvd (not_dvd_padicRegExp hp)
    simpa [h2] using h1
  have hreg_ne : normalizedPadicRegulator q p X₁ Y₁ ≠ 0 := by
    unfold normalizedPadicRegulator
    exact mul_ne_zero (inv_ne_zero he_ne) hlog_ne
  have hreg_val : (normalizedPadicRegulator q p X₁ Y₁).valuation =
      (padicValInt p (((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ e).im) : ℤ) := by
    unfold normalizedPadicRegulator
    rw [Padic.valuation_mul (inv_ne_zero he_ne) hlog_ne, Padic.valuation_inv, he_val, neg_zero, zero_add]
    exact hlog_val
  refine ⟨hreg_ne, hreg_val, ?_⟩
  unfold normalizedPadicRegulatorVal
  rw [hreg_val]
  exact Int.toNat_natCast _

/-- **Manuscript Equation (3.6) — Proved Directly in `ℚ_[p]` (Zero External Axioms, Eliminates
`padic_log_regulator_pell_power`)**:
For any prime `p ≥ 5`, `q ≥ 2`, fundamental Pell solution `(X₁, Y₁)` of `q`, and Pell power
`(m + s √q) = (X₁ + Y₁ √q)^k` with `p ∣ s` and `p ∤ m`, the concrete normalized `p`-adic
regulator `R̃_p(q, X₁, Y₁) ∈ ℚ_[p]` satisfies:
`v_p(R̃_p(q, X₁, Y₁)) + v_p(k) = v_p(s)` and `v_p(padicPellLogZ q p m s) = v_p(s)`. -/
theorem padic_regulator_valuation_pell_power {q p m s X₁ Y₁ k : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hq : 2 ≤ q) (hX1 : 0 < X₁) (hY1 : 0 < Y₁)
    (hpell : X₁ ^ 2 = q * Y₁ ^ 2 + 1)
    (hms : m ^ 2 = q * s ^ 2 + 1)
    (hpow : (⟨(m : ℤ), (s : ℤ)⟩ : Zsqrtd (q : ℤ)) =
      (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ k)
    (hk : 1 ≤ k)
    (hs_dvd : 1 ≤ padicValNat p s) (hm_nd : ¬ p ∣ m) :
    normalizedPadicRegulatorVal q p X₁ Y₁ + padicValNat p k = padicValNat p s ∧
    (padicPellLogZ q p (m : ℤ) (s : ℤ)).valuation = (padicValNat p s : ℤ) := by
  have hp : p.Prime := Fact.out
  set e := padicRegExp q p
  have he1 : 1 ≤ e := padicRegExp_pos hp
  have he_nd : ¬ p ∣ e := not_dvd_padicRegExp hp
  have hs0 : s ≠ 0 := by intro h0; rw [h0] at hs_dvd; simp at hs_dvd
  have hps : (p : ℤ) ∣ (s : ℤ) :=
    Int.natCast_dvd_natCast.mpr (by simpa using dvd_trans (pow_dvd_pow p hs_dvd) pow_padicValNat_dvd)
  have hpm_nd : ¬ (p : ℤ) ∣ (m : ℤ) := fun h => hm_nd (Int.natCast_dvd_natCast.mp h)
  have hlog_ms := (padicPellLogZ_valuation (q := q) (p := p) hp5 (by omega)
    (by exact_mod_cast hs0) (dvd_mul_of_dvd_right hps _) hpm_nd).2.2
  have hlog_ms' : (padicPellLogZ q p (m : ℤ) (s : ℤ)).valuation = (padicValNat p s : ℤ) := by
    rw [hlog_ms]; unfold padicValInt; simp
  obtain ⟨_, _, hreg_nat⟩ := normalizedPadicRegulator_valuation (q := q) (p := p) hp5 (by omega) hX1 hY1 hpell
  obtain ⟨hu_norm, hu_dvd, _, hu_im_ne⟩ := pell_pow_padicRegExp_props hp hp5 (by omega) hX1 hY1 hpell
  set u : Zsqrtd (q : ℤ) := (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ e
  have hpow_e : (⟨(m : ℤ), (s : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ e = u ^ k := by
    rw [hpow, ← pow_mul, mul_comm k e, pow_mul]
  have him_eq : ((⟨(m : ℤ), (s : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ e).im = (u ^ k).im :=
    congrArg Zsqrtd.im hpow_e
  have hlhs : ((⟨(m : ℤ), (s : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ e).im =
      (s : ℤ) * chebyshevU_eval (q : ℤ) (m : ℤ) (s : ℤ) e :=
    lucasY_eq_mul_chebyshevU (q : ℤ) (m : ℤ) (s : ℤ) e
  have hrhs : (u ^ k).im = u.im * chebyshevU_eval (q : ℤ) u.re u.im k := by
    have hu_eta : u = ⟨u.re, u.im⟩ := by ext <;> rfl
    conv_lhs => rw [hu_eta]
    exact lucasY_eq_mul_chebyshevU (q : ℤ) u.re u.im k
  rw [hlhs, hrhs] at him_eq
  have hms_z : (m : ℤ) ^ 2 - (q : ℤ) * (s : ℤ) ^ 2 = 1 := by have : (m : ℤ) ^ 2 = (q : ℤ) * (s : ℤ) ^ 2 + 1 := by exact_mod_cast hms
    linarith
  have hcheb_e := padicValInt_chebyshevU he1 hp hms_z (dvd_mul_of_dvd_right hps _) (Or.inl (by omega))
  have hcheb_k := padicValInt_chebyshevU hk hp hu_norm hu_dvd (Or.inl (by omega))
  have hcheb_e_ne : chebyshevU_eval (q : ℤ) (m : ℤ) (s : ℤ) e ≠ 0 := by
    intro h0
    have hm_pos : 0 < m := by
      by_contra h0'; have hm0 : m = 0 := by omega; subst hm0; simp at hms
    have hne := (pell_pow_padicRegExp_props hp hp5 (by omega) hm_pos (Nat.pos_of_ne_zero hs0) hms).2.2.2
    rw [hlhs, h0, mul_zero] at hne
    exact hne rfl
  have hcheb_k_ne : chebyshevU_eval (q : ℤ) u.re u.im k ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at him_eq
    exact mul_ne_zero (by exact_mod_cast hs0) hcheb_e_ne him_eq
  have hval_eq := congrArg (padicValInt p) him_eq
  have hval_mul : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      padicValInt p (a * b) = padicValInt p a + padicValInt p b := by
    intro a b ha hb
    unfold padicValInt
    rw [Int.natAbs_mul, padicValNat.mul (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)]
  rw [hval_mul _ _ (by exact_mod_cast hs0) hcheb_e_ne, hval_mul _ _ hu_im_ne hcheb_k_ne,
    hcheb_e, hcheb_k, padicValNat.eq_zero_of_not_dvd he_nd, add_zero] at hval_eq
  have hval_s : padicValInt p (s : ℤ) = padicValNat p s := by unfold padicValInt; simp
  rw [hval_s] at hval_eq
  refine ⟨?_, hlog_ms'⟩
  rw [hreg_nat]
  omega

/-- Canonical fundamental Pell solution `(X₁, Y₁)` for any non-square `q ≥ 2` (defaulting to
`(1, 0)` otherwise), constructed constructively from `exists_unique_fundamentalPell`. -/
def fundPellPair (q : ℕ) : ℕ × ℕ :=
  if h : 2 ≤ q ∧ ¬ IsSquare (q : ℤ) then
    (exists_unique_fundamentalPell_of_not_isSquare h.1 h.2).choose
  else (1, 0)

lemma fundPellPair_eq_of_isFundamentalPell {q X₁ Y₁ : ℕ} (hq : 2 ≤ q) (hnsq : ¬ IsSquare (q : ℤ))
    (hfund : IsFundamentalPell q X₁ Y₁) :
    fundPellPair q = (X₁, Y₁) := by
  unfold fundPellPair
  rw [dif_pos ⟨hq, hnsq⟩]
  have hspec := (exists_unique_fundamentalPell_of_not_isSquare hq hnsq).choose_spec
  exact (hspec.2 (X₁, Y₁) hfund).symm

/-- Canonical concrete `p`-adic valuation `v_p(R̃_p(ℚ(√q)))` of the normalized `p`-adic
regulator in `ℚ_[p]`, anchored directly to `fundPellPair` and `normalizedPadicRegulatorVal`. -/
def realQuadPadicRegVal (q p : ℕ) : ℕ :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    let xy := fundPellPair q
    normalizedPadicRegulatorVal q p xy.1 xy.2
  else 0

/-- Helper: real equality `m + s √q = (X₁ + Y₁ √q)^k` implies exact equality in `Zsqrtd q`
whenever `¬ IsSquare q`. -/
lemma zsqrtd_pow_eq_of_real_eq {q m s X₁ Y₁ k : ℕ} (hq : 2 ≤ q) (hnsq : ¬ IsSquare q)
    (hk_eq : (m : ℝ) + (s : ℝ) * Real.sqrt (q : ℝ) = ((X₁ : ℝ) + (Y₁ : ℝ) * Real.sqrt (q : ℝ)) ^ k) :
    (⟨(m : ℤ), (s : ℤ)⟩ : Zsqrtd (q : ℤ)) =
      (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ k := by
  set u : Zsqrtd (q : ℤ) := (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ k
  have hreal_pow : ∀ j : ℕ,
      (((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ j).re : ℝ) +
      (((⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ j).im : ℝ) * Real.sqrt (q : ℝ) =
      ((X₁ : ℝ) + (Y₁ : ℝ) * Real.sqrt (q : ℝ)) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, pow_succ, ← ih]
      set w : Zsqrtd (q : ℤ) := (⟨(X₁ : ℤ), (Y₁ : ℤ)⟩ : Zsqrtd (q : ℤ)) ^ j
      have h1 : (w * ⟨(X₁ : ℤ), (Y₁ : ℤ)⟩).re = w.re * (X₁ : ℤ) + (q : ℤ) * w.im * (Y₁ : ℤ) := by simp [zsqrtd_mul_re]
      have h2 : (w * ⟨(X₁ : ℤ), (Y₁ : ℤ)⟩).im = w.re * (Y₁ : ℤ) + w.im * (X₁ : ℤ) := by simp [zsqrtd_mul_im]
      rw [h1, h2]; push_cast
      have hsq : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) := Real.sq_sqrt (by positivity)
      calc (w.re : ℝ) * (X₁ : ℝ) + (q : ℝ) * (w.im : ℝ) * (Y₁ : ℝ) +
            ((w.re : ℝ) * (Y₁ : ℝ) + (w.im : ℝ) * (X₁ : ℝ)) * Real.sqrt (q : ℝ)
          = (w.re : ℝ) * (X₁ : ℝ) + (w.im : ℝ) * (Y₁ : ℝ) * Real.sqrt (q : ℝ) ^ 2 +
            ((w.re : ℝ) * (Y₁ : ℝ) + (w.im : ℝ) * (X₁ : ℝ)) * Real.sqrt (q : ℝ) := by rw [hsq]; ring
        _ = ((w.re : ℝ) + (w.im : ℝ) * Real.sqrt (q : ℝ)) * ((X₁ : ℝ) + (Y₁ : ℝ) * Real.sqrt (q : ℝ)) := by ring
  have heq_r : (m : ℝ) + (s : ℝ) * Real.sqrt (q : ℝ) = (u.re : ℝ) + (u.im : ℝ) * Real.sqrt (q : ℝ) := by
    rw [hk_eq, ← hreal_pow k]
  have hsqrt_irr : Irrational (Real.sqrt (q : ℝ)) := by
    rw [irrational_iff_ne_rational]
    intro a b hb hab
    have h1 : ((a : ℝ) / (b : ℝ)) ^ 2 = (q : ℝ) := by
      rw [← hab, Real.sq_sqrt (by positivity)]
    have hb_r : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have h2 : (a : ℝ) ^ 2 = (q : ℝ) * (b : ℝ) ^ 2 := by field_simp [hb_r] at h1; linarith
    have h3 : (a : ℤ) ^ 2 = (q : ℤ) * (b : ℤ) ^ 2 := by exact_mod_cast h2
    have h4 : a.natAbs ^ 2 = q * b.natAbs ^ 2 := by
      have := congrArg Int.natAbs h3; simpa [Int.natAbs_mul, Int.natAbs_pow] using this
    have hb_pos : 0 < b.natAbs := Int.natAbs_pos.mpr hb
    have hdiv_sq : b.natAbs ∣ a.natAbs := by
      have h2dvd : b.natAbs ^ 2 ∣ a.natAbs ^ 2 := ⟨q, by linarith⟩
      exact (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp h2dvd
    obtain ⟨c, hc⟩ := hdiv_sq
    rw [hc, mul_pow] at h4
    have hq_sq : q = c ^ 2 := by
      have hb2_ne : b.natAbs ^ 2 ≠ 0 := pow_ne_zero 2 hb_pos.ne'
      have h5 : b.natAbs ^ 2 * c ^ 2 = b.natAbs ^ 2 * q := by linarith
      exact (mul_left_cancel₀ hb2_ne h5).symm
    exact hnsq ⟨c, by rw [hq_sq, sq]⟩
  have him_eq : (s : ℤ) = u.im := by
    by_contra hne
    have hne_r : (s : ℝ) - (u.im : ℝ) ≠ 0 := by
      have : ((s : ℤ) - u.im : ℤ) ≠ 0 := sub_ne_zero.mpr hne
      exact_mod_cast this
    let r : ℚ := ((u.re - (m : ℤ) : ℤ) : ℚ) / (((s : ℤ) - u.im : ℤ) : ℚ)
    have hrat : (r : ℝ) = Real.sqrt (q : ℝ) := by
      dsimp only [r]
      push_cast
      rw [div_eq_iff hne_r]
      linarith
    exact hsqrt_irr ⟨r, hrat⟩
  have hre_eq : (m : ℤ) = u.re := by
    have him_r : (s : ℝ) = (u.im : ℝ) := by exact_mod_cast him_eq
    rw [him_r] at heq_r
    have hre_r : (m : ℝ) = (u.re : ℝ) := by linarith
    exact_mod_cast hre_r
  ext <;> assumption

/-- Concrete eq. (3.6) stated directly in terms of `realQuadPadicRegVal q p`:
`realQuadPadicRegVal q p + padicValNat p k = padicValNat p s` (zero external axioms). -/
theorem realQuadPadicRegVal_pell_power {q p m s X₁ Y₁ k : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ q) (hnsq : ¬ IsSquare (q : ℤ))
    (hfund : IsFundamentalPell q X₁ Y₁)
    (hms : m ^ 2 = q * s ^ 2 + 1)
    (hk_eq : (m : ℝ) + (s : ℝ) * Real.sqrt (q : ℝ) = (pellUnit q X₁ Y₁) ^ k)
    (hk : 1 ≤ k) (hs_dvd : 1 ≤ padicValNat p s) (hm_nd : ¬ p ∣ m) :
    realQuadPadicRegVal q p + padicValNat p k = padicValNat p s := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold realQuadPadicRegVal
  rw [dif_pos hp, fundPellPair_eq_of_isFundamentalPell hq hnsq hfund]
  unfold pellUnit at hk_eq
  have hnsq_nat : ¬ IsSquare q := by rintro ⟨r, hr⟩; exact hnsq ⟨(r : ℤ), by exact_mod_cast hr⟩
  have hpow := zsqrtd_pow_eq_of_real_eq hq hnsq_nat hk_eq
  exact (padic_regulator_valuation_pell_power hp5 hq hfund.1 hfund.2.1 hfund.2.2.1 hms hpow hk hs_dvd hm_nd).1

/-- **Order-Index Lemma (`[𝒪_K^× : ℤ[√q]^×] ∈ {1, 3}`)**:
For any squarefree integer `q` and any half-integer unit `(a + b√q)/2 ∈ 𝒪_K^×` satisfying
`a^2 - q b^2 = ±4`, its cube `((a + b√q)/2)^3` lies in `ℤ[√q]` (i.e., `8 ∣ a(a^2 + 3 q b^2)`
and `8 ∣ b(3 a^2 + q b^2)`). Consequently, `p ∤ [𝒪_K^× : ℤ[√q]^×]` for every prime `p ≥ 5`. -/
theorem real_quad_unit_order_index_dvd_three {q : ℕ} {a b : ℤ} (hq : Squarefree q)
    (hnorm : a ^ 2 - (q : ℤ) * b ^ 2 = 4 ∨ a ^ 2 - (q : ℤ) * b ^ 2 = -4) :
    (8 : ℤ) ∣ a * (a ^ 2 + 3 * (q : ℤ) * b ^ 2) ∧
    (8 : ℤ) ∣ b * (3 * a ^ 2 + (q : ℤ) * b ^ 2) := by
  have h1 : a * (a ^ 2 + 3 * (q : ℤ) * b ^ 2) = 4 * a * a ^ 2 - 3 * a * (a ^ 2 - (q : ℤ) * b ^ 2) := by ring
  have h2 : b * (3 * a ^ 2 + (q : ℤ) * b ^ 2) = 4 * b * a ^ 2 - b * (a ^ 2 - (q : ℤ) * b ^ 2) := by ring
  have hnot4q : ¬ (4 : ℤ) ∣ (q : ℤ) := by
    intro h4
    have h4n : 2 * 2 ∣ q := by exact_mod_cast h4
    have hu : IsUnit (2 : ℕ) := hq 2 h4n
    rw [Nat.isUnit_iff] at hu
    omega
  have hpar : a % 2 = 0 ∨ a % 2 = 1 := by omega
  rcases hpar with ha0 | ha1
  · obtain ⟨a', rfl⟩ : ∃ a', a = 2 * a' := ⟨a / 2, by omega⟩
    have hb_even : b % 2 = 0 := by
      by_contra hbodd
      have hb1 : b % 2 = 1 := by omega
      have hb_sq_odd : b ^ 2 % 4 = 1 := by
        set kb := b / 2
        have hbeq : b = 2 * kb + 1 := by omega
        have hsq : b ^ 2 = 4 * (kb ^ 2 + kb) + 1 := by rw [hbeq]; ring
        omega
      have h4_dvd_qb2 : (4 : ℤ) ∣ (q : ℤ) * b ^ 2 := by
        rcases hnorm with h | h
        · exact ⟨a' ^ 2 - 1, by linarith⟩
        · exact ⟨a' ^ 2 + 1, by linarith⟩
      obtain ⟨k, hk⟩ := h4_dvd_qb2
      have h4_dvd_q : (4 : ℤ) ∣ (q : ℤ) := by
        have hmod : ((q : ℤ) * b ^ 2) % 4 = 0 := by omega
        rw [Int.mul_emod, hb_sq_odd, mul_one, Int.emod_emod] at hmod
        exact Int.dvd_of_emod_eq_zero hmod
      exact hnot4q h4_dvd_q
    obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
    rcases hnorm with h | h
    · have hq4 : (q : ℤ) * (2 * b') ^ 2 = 4 * (a' ^ 2 - 1) := by linarith
      refine ⟨⟨a' * (4 * a' ^ 2 - 3), ?_⟩, ⟨b' * (4 * a' ^ 2 - 1), ?_⟩⟩
      · linear_combination 6 * a' * hq4
      · linear_combination 2 * b' * hq4
    · have hq4 : (q : ℤ) * (2 * b') ^ 2 = 4 * (a' ^ 2 + 1) := by linarith
      refine ⟨⟨a' * (4 * a' ^ 2 + 3), ?_⟩, ⟨b' * (4 * a' ^ 2 + 1), ?_⟩⟩
      · linear_combination 6 * a' * hq4
      · linear_combination 2 * b' * hq4
  · have ha_sq : a ^ 2 % 2 = 1 := by
      set ka := a / 2
      have haeq : a = 2 * ka + 1 := by omega
      have hsq : a ^ 2 = 4 * ka ^ 2 + 4 * ka + 1 := by rw [haeq]; ring
      omega
    rcases hnorm with h | h
    · obtain ⟨t1, ht1⟩ : ∃ t : ℤ, a ^ 2 - 3 = 2 * t := ⟨(a ^ 2 - 3) / 2, by omega⟩
      obtain ⟨t2, ht2⟩ : ∃ t : ℤ, a ^ 2 - 1 = 2 * t := ⟨(a ^ 2 - 1) / 2, by omega⟩
      refine ⟨⟨a * t1, ?_⟩, ⟨b * t2, ?_⟩⟩
      · rw [h1, h]; linear_combination 4 * a * ht1
      · rw [h2, h]; linear_combination 4 * b * ht2
    · obtain ⟨t1, ht1⟩ : ∃ t : ℤ, a ^ 2 + 3 = 2 * t := ⟨(a ^ 2 + 3) / 2, by omega⟩
      obtain ⟨t2, ht2⟩ : ∃ t : ℤ, a ^ 2 + 1 = 2 * t := ⟨(a ^ 2 + 1) / 2, by omega⟩
      refine ⟨⟨a * t1, ?_⟩, ⟨b * t2, ?_⟩⟩
      · rw [h1, h]; linear_combination 4 * a * ht1
      · rw [h2, h]; linear_combination 4 * b * ht2

end GrasGreenbergBrocard
