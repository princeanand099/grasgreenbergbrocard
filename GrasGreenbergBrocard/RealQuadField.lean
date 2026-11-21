import Mathlib

/-!
# Concrete Real Quadratic Number Field, Class Number, and Narrow Class Group (Defects D2(2), D4, D6(b))

This file anchors the real quadratic field `K = ℚ(√q)`, its class number `h(q)`, its narrow class
group `Cl^+(K)`, and its 4-rank `𝔽₂`-vector space `Cl^+(K)[2] ∩ 2 Cl^+(K)` directly to Mathlib's
`AdjoinRoot`, `NumberField`, `NumberField.classNumber`, `NumberField.RingOfIntegers`, and
`FractionalIdeal` with **zero external axioms**:
- `RealQuadK q`: `AdjoinRoot (X^2 - q : Polynomial ℚ)`, proved to be a `Field` and `NumberField`
  whenever `¬ IsSquare (q : ℚ)`.
- `realQuadClassNumber q`: concrete `NumberField.classNumber (RealQuadK q)`.
- `NarrowClassGroup q`: concrete quotient of invertible fractional ideals of `𝒪_{RealQuadK q}` by
  totally positive principal ideals `(γ)` with `N_{K/ℚ}(γ) > 0`.
- `narrowToOrdinary q`: canonical surjective homomorphism `NarrowClassGroup q →* ClassGroup 𝒪_K`.
- `Cl4RankSubgroup q` & `Cl4RankVec q`: concrete `𝔽₂`-vector space `Cl^+(K)[2] ∩ 2 Cl^+(K)`.
-/

noncomputable section

open Polynomial

namespace GrasGreenbergBrocard

/-- Defining polynomial `X^2 - q ∈ ℚ[X]` for `ℚ(√q)`. -/
def realQuadPoly (q : ℕ) : Polynomial ℚ :=
  Polynomial.X ^ 2 - Polynomial.C (q : ℚ)

lemma realQuadPoly_monic (q : ℕ) : (realQuadPoly q).Monic := by
  unfold realQuadPoly
  exact Polynomial.monic_X_pow_sub_C (q : ℚ) (by norm_num)

lemma realQuadPoly_natDegree (q : ℕ) : (realQuadPoly q).natDegree = 2 := by
  unfold realQuadPoly
  exact Polynomial.natDegree_X_pow_sub_C

lemma realQuadPoly_ne_zero (q : ℕ) : realQuadPoly q ≠ 0 :=
  (realQuadPoly_monic q).ne_zero

/-- `X^2 - q ∈ ℚ[X]` is irreducible whenever `q` is not a rational square. -/
theorem realQuadPoly_irreducible {q : ℕ} (hnsq : ¬ IsSquare (q : ℚ)) :
    Irreducible (realQuadPoly q) := by
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · intro hu
    have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [realQuadPoly_natDegree] at hdeg
    omega
  · intro a b hab
    have ha0 : a ≠ 0 := by intro h0; rw [h0, zero_mul] at hab; exact realQuadPoly_ne_zero q hab
    have hb0 : b ≠ 0 := by intro h0; rw [h0, mul_zero] at hab; exact realQuadPoly_ne_zero q hab
    have hdeg : a.natDegree + b.natDegree = 2 := by
      rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, realQuadPoly_natDegree]
    by_cases ha : a.natDegree = 0
    · left
      rw [Polynomial.eq_C_of_natDegree_eq_zero ha]
      have hc0 : a.coeff 0 ≠ 0 := by
        intro h0; apply ha0
        rw [Polynomial.eq_C_of_natDegree_eq_zero ha, h0, map_zero]
      exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
    · by_cases hb : b.natDegree = 0
      · right
        rw [Polynomial.eq_C_of_natDegree_eq_zero hb]
        have hc0 : b.coeff 0 ≠ 0 := by
          intro h0; apply hb0
          rw [Polynomial.eq_C_of_natDegree_eq_zero hb, h0, map_zero]
        exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
      · exfalso
        have ha1 : a.natDegree = 1 := by omega
        have hlc : a.coeff 1 ≠ 0 := by
          rw [← ha1]; exact Polynomial.leadingCoeff_ne_zero.mpr ha0
        let r : ℚ := -(a.coeff 0) / a.coeff 1
        have hroot_a : a.eval r = 0 := by
          rw [Polynomial.eval_eq_sum_range, ha1, Finset.sum_range_succ, Finset.sum_range_one]
          simp only [pow_zero, mul_one, pow_one, r]
          field_simp [hlc]
          ring
        have hroot_p : (realQuadPoly q).eval r = 0 := by
          rw [hab, Polynomial.eval_mul, hroot_a, zero_mul]
        unfold realQuadPoly at hroot_p
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hroot_p
        exact hnsq ⟨r, by linarith [sq r]⟩

/-- Concrete real quadratic field `K = ℚ(√q) = AdjoinRoot (X^2 - q)`. -/
abbrev RealQuadK (q : ℕ) := AdjoinRoot (realQuadPoly q)

instance realQuadPoly_irreducible_fact (q : ℕ) [h : Fact (¬ IsSquare (q : ℚ))] :
    Fact (Irreducible (realQuadPoly q)) :=
  ⟨realQuadPoly_irreducible h.out⟩

instance realQuadK_finiteDimensional (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] :
    FiniteDimensional ℚ (RealQuadK q) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis (realQuadPoly_ne_zero q)).basis

instance realQuadK_charZero (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] :
    CharZero (RealQuadK q) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (RealQuadK q)).injective

instance realQuadK_numberField (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] :
    NumberField (RealQuadK q) :=
  NumberField.mk

/-- Concrete class number `h(q) = NumberField.classNumber (ℚ(√q))` anchored to Mathlib's
`NumberField.classNumber`. -/
def realQuadClassNumber (q : ℕ) : ℕ :=
  if h : ¬ IsSquare (q : ℚ) then
    haveI : Fact (¬ IsSquare (q : ℚ)) := ⟨h⟩
    NumberField.classNumber (RealQuadK q)
  else 1

lemma realQuadClassNumber_pos (q : ℕ) : 0 < realQuadClassNumber q := by
  unfold realQuadClassNumber
  by_cases h : ¬ IsSquare (q : ℚ)
  · rw [dif_pos h]
    haveI : Fact (¬ IsSquare (q : ℚ)) := ⟨h⟩
    exact NumberField.classNumber_pos (RealQuadK q)
  · rw [dif_neg h]
    norm_num

/-- Helper: a squarefree natural `q ≥ 2` is not a square in `ℚ`. -/
lemma not_isSquare_rat_of_squarefree {q : ℕ} (hq2 : 2 ≤ q) (hsqf : Squarefree q) :
    ¬ IsSquare (q : ℚ) := by
  rintro ⟨r, hr⟩
  have hq_eq : (q : ℚ) = r ^ 2 := by rw [sq]; exact hr
  have hnum : (q : ℤ) * (r.den : ℤ) ^ 2 = r.num ^ 2 := by
    have hden_ne : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_pos.ne'
    have h1 : (q : ℚ) * (r.den : ℚ) ^ 2 = (r.num : ℚ) ^ 2 := by
      calc (q : ℚ) * (r.den : ℚ) ^ 2
          = r ^ 2 * (r.den : ℚ) ^ 2 := by rw [hq_eq]
        _ = ((r.num : ℚ) / (r.den : ℚ)) ^ 2 * (r.den : ℚ) ^ 2 := by rw [Rat.num_div_den r]
        _ = (r.num : ℚ) ^ 2 := by field_simp [hden_ne]
    exact_mod_cast h1
  have hnat : q * r.den ^ 2 = r.num.natAbs ^ 2 := by
    have := congrArg Int.natAbs hnum
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  have hcop : Nat.Coprime r.num.natAbs r.den := r.reduced
  have hdvd : r.den ^ 2 ∣ r.num.natAbs ^ 2 := ⟨q, by linarith⟩
  have hden1 : r.den = 1 := by
    have hcop2 : Nat.Coprime (r.num.natAbs ^ 2) (r.den ^ 2) := hcop.pow 2 2
    have h1 : r.den ^ 2 ∣ 1 := by
      have := Nat.dvd_gcd hdvd dvd_rfl
      rw [hcop2.gcd_eq_one] at this
      exact this
    have : r.den ^ 2 = 1 := Nat.eq_one_of_dvd_one h1
    nlinarith [r.den_pos]
  rw [hden1, one_pow, mul_one] at hnat
  have hu : IsUnit r.num.natAbs := hsqf r.num.natAbs (by rw [← sq, ← hnat])
  rw [Nat.isUnit_iff] at hu
  rw [hu] at hnat
  omega

/-- Subgroup of nonzero elements `γ ∈ (RealQuadK q)ˣ` with positive norm `N_{K/ℚ}(γ) > 0`. -/
def totallyPositiveUnits (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] : Subgroup (RealQuadK q)ˣ where
  carrier := {u | 0 < Algebra.norm ℚ (u : RealQuadK q)}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change 0 < Algebra.norm ℚ ((a * b : (RealQuadK q)ˣ) : RealQuadK q)
    rw [Units.val_mul, map_mul]
    exact mul_pos ha hb
  inv_mem' {a} ha := by
    change 0 < Algebra.norm ℚ ((a⁻¹ : (RealQuadK q)ˣ) : RealQuadK q)
    have hmul : Algebra.norm ℚ ((a⁻¹ : (RealQuadK q)ˣ) : RealQuadK q) *
        Algebra.norm ℚ ((a : (RealQuadK q)ˣ) : RealQuadK q) = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    nlinarith

/-- Subgroup of totally positive principal fractional ideals `(γ)` (`N_{K/ℚ}(γ) > 0`) inside the
group of invertible fractional ideals of `𝒪_{RealQuadK q}`. -/
def totallyPositivePrincipalIdeals (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] :
    Subgroup (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers (RealQuadK q)))
      (RealQuadK q))ˣ :=
  ((toPrincipalIdeal (NumberField.RingOfIntegers (RealQuadK q)) (RealQuadK q)).comp
    (totallyPositiveUnits q).subtype).range

/-- **Concrete Narrow Class Group `Cl^+(ℚ(√q))`**:
Quotient of the group of invertible fractional ideals of `𝒪_{RealQuadK q}` by totally positive
principal fractional ideals `(γ)` with `N_{K/ℚ}(γ) > 0`. -/
abbrev NarrowClassGroup (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] : Type :=
  (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers (RealQuadK q)))
    (RealQuadK q))ˣ ⧸ totallyPositivePrincipalIdeals q

/-- Canonical surjective homomorphism `Cl^+(ℚ(√q)) →* Cl(ℚ(√q))`. -/
def narrowToOrdinary (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] :
    NarrowClassGroup q →* ClassGroup (NumberField.RingOfIntegers (RealQuadK q)) :=
  (ClassGroup.equiv (RealQuadK q)).symm.toMonoidHom.comp
    (QuotientGroup.map (totallyPositivePrincipalIdeals q)
      (toPrincipalIdeal (NumberField.RingOfIntegers (RealQuadK q)) (RealQuadK q)).range
      (MonoidHom.id _)
      (by
        intro x hx
        rcases hx with ⟨⟨u, _⟩, rfl⟩
        exact ⟨u, rfl⟩))

lemma narrowToOrdinary_surjective (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] :
    Function.Surjective (narrowToOrdinary q) := by
  intro c
  rcases QuotientGroup.mk_surjective ((ClassGroup.equiv (RealQuadK q)) c) with ⟨I, hI⟩
  refine ⟨QuotientGroup.mk I, ?_⟩
  simp only [narrowToOrdinary, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, QuotientGroup.map_mk, MonoidHom.id_apply, hI, MulEquiv.symm_apply_apply]

/-- The kernel of `narrowToOrdinary q` has cardinality at most 2 (generated by `(-1)` or any
negative-norm principal ideal), hence is finite. -/
instance narrowToOrdinary_ker_finite (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] :
    Finite (narrowToOrdinary q).ker := by
  have hsub : ∀ x y : (narrowToOrdinary q).ker, x ≠ 1 → y ≠ 1 → x = y := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ hx1 hy1
    apply Subtype.ext
    rcases QuotientGroup.mk_surjective x with ⟨I, rfl⟩
    rcases QuotientGroup.mk_surjective y with ⟨J, rfl⟩
    have hx' : narrowToOrdinary q (QuotientGroup.mk I) = 1 := MonoidHom.mem_ker.mp hx
    have hy' : narrowToOrdinary q (QuotientGroup.mk J) = 1 := MonoidHom.mem_ker.mp hy
    simp only [narrowToOrdinary, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, QuotientGroup.map_mk, MonoidHom.id_apply, map_eq_one_iff] at hx' hy'
    have hI : I ∈ (toPrincipalIdeal (NumberField.RingOfIntegers (RealQuadK q)) (RealQuadK q)).range :=
      (QuotientGroup.eq_one_iff I).mp hx'
    have hJ : J ∈ (toPrincipalIdeal (NumberField.RingOfIntegers (RealQuadK q)) (RealQuadK q)).range :=
      (QuotientGroup.eq_one_iff J).mp hy'
    rcases hI with ⟨u, hu⟩
    rcases hJ with ⟨v, hv⟩
    have hu_not_pos : ¬ 0 < Algebra.norm ℚ (u : RealQuadK q) := by
      intro hpos
      apply hx1
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff I).mpr ⟨⟨u, hpos⟩, hu⟩
    have hv_not_pos : ¬ 0 < Algebra.norm ℚ (v : RealQuadK q) := by
      intro hpos
      apply hy1
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff J).mpr ⟨⟨v, hpos⟩, hv⟩
    have hu_ne : Algebra.norm ℚ (u : RealQuadK q) ≠ 0 :=
      (Algebra.norm_eq_zero_iff).not.mpr u.ne_zero
    have hv_ne : Algebra.norm ℚ (v : RealQuadK q) ≠ 0 :=
      (Algebra.norm_eq_zero_iff).not.mpr v.ne_zero
    have hu_neg : Algebra.norm ℚ (u : RealQuadK q) < 0 := lt_of_le_of_ne (not_lt.mp hu_not_pos) hu_ne
    have hv_neg : Algebra.norm ℚ (v : RealQuadK q) < 0 := lt_of_le_of_ne (not_lt.mp hv_not_pos) hv_ne
    have hu_inv_neg : Algebra.norm ℚ ((u⁻¹ : (RealQuadK q)ˣ) : RealQuadK q) < 0 := by
      have hmul : Algebra.norm ℚ ((u⁻¹ : (RealQuadK q)ˣ) : RealQuadK q) *
          Algebra.norm ℚ ((u : (RealQuadK q)ˣ) : RealQuadK q) = 1 := by
        rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
      nlinarith
    have huv_pos : 0 < Algebra.norm ℚ ((u⁻¹ * v : (RealQuadK q)ˣ) : RealQuadK q) := by
      rw [Units.val_mul, map_mul]
      exact mul_pos_of_neg_of_neg hu_inv_neg hv_neg
    rw [QuotientGroup.eq]
    refine ⟨⟨u⁻¹ * v, huv_pos⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv, hu, hv]
  classical
  refine Finite.of_injective (fun x : (narrowToOrdinary q).ker => decide (x = 1)) ?_
  intro a b hab
  by_cases ha : a = 1 <;> by_cases hb : b = 1
  · rw [ha, hb]
  · simp [ha, hb] at hab
  · simp [ha, hb] at hab
  · exact hsub a b ha hb

/-- `NarrowClassGroup q` is finite (since `ClassGroup 𝒪_K` is finite and `ker(narrowToOrdinary)`
has size at most 2). -/
instance narrowClassGroup_finite (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] :
    Finite (NarrowClassGroup q) := by
  have hfib : ∀ y : ClassGroup (NumberField.RingOfIntegers (RealQuadK q)),
      Finite {x : NarrowClassGroup q // narrowToOrdinary q x = y} := by
    intro y
    obtain ⟨x₀, hx₀⟩ := narrowToOrdinary_surjective q y
    refine Finite.of_injective (fun z : {x : NarrowClassGroup q // narrowToOrdinary q x = y} =>
      (⟨z.1 * x₀⁻¹, by simp [MonoidHom.mem_ker, z.2, hx₀]⟩ : (narrowToOrdinary q).ker)) ?_
    intro a b hab
    apply Subtype.ext
    have h1 : a.1 * x₀⁻¹ = b.1 * x₀⁻¹ := congrArg Subtype.val hab
    exact mul_right_cancel h1
  haveI := hfib
  exact Finite.of_equiv _ (Equiv.sigmaFiberEquiv (narrowToOrdinary q))

/-- **Concrete Narrow 4-Rank Subgroup `Cl^+(K)[2] ∩ 2 Cl^+(K)`**:
Elements `c ∈ Cl^+(K)` satisfying `c^2 = 1` and `∃ d ∈ Cl^+(K), d^2 = c`. -/
def Cl4RankSubgroup (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] : Subgroup (NarrowClassGroup q) where
  carrier := {c | c ^ 2 = 1 ∧ ∃ d : NarrowClassGroup q, d ^ 2 = c}
  one_mem' := ⟨one_pow 2, 1, one_pow 2⟩
  mul_mem' {a b} ha hb := by
    rcases ha with ⟨ha2, da, hda⟩
    rcases hb with ⟨hb2, db, hdb⟩
    refine ⟨by rw [mul_pow, ha2, hb2, mul_one], da * db, by rw [mul_pow, hda, hdb]⟩
  inv_mem' {a} ha := by
    rcases ha with ⟨ha2, da, hda⟩
    refine ⟨by rw [inv_pow, ha2, inv_one], da⁻¹, by rw [inv_pow, hda]⟩

/-- Concrete `𝔽₂`-vector space structure on `Cl^+(K)[2] ∩ 2 Cl^+(K)` (written additively). -/
abbrev Cl4RankVec (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] : Type :=
  Additive (Cl4RankSubgroup q)

lemma cl4RankVec_two_nsmul {q : ℕ} [Fact (¬ IsSquare (q : ℚ))] (x : Cl4RankVec q) :
    x + x = 0 := by
  change Additive.ofMul (Additive.toMul x * Additive.toMul x) = Additive.ofMul 1
  congr 1
  apply Subtype.ext
  have h := (Additive.toMul x).property.1
  simpa [sq] using h

def cl4Smul {q : ℕ} [Fact (¬ IsSquare (q : ℚ))] (a : ZMod 2) (x : Cl4RankVec q) : Cl4RankVec q :=
  if a = 0 then 0 else x

instance cl4RankVec_smul (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] : SMul (ZMod 2) (Cl4RankVec q) :=
  ⟨cl4Smul⟩

instance cl4RankVec_module (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] :
    Module (ZMod 2) (Cl4RankVec q) where
  smul := cl4Smul
  one_smul x := by change cl4Smul 1 x = x; simp [cl4Smul]
  mul_smul a b x := by
    change cl4Smul (a * b) x = cl4Smul a (cl4Smul b x)
    fin_cases a <;> fin_cases b <;> simp [cl4Smul]
  smul_zero a := by
    change cl4Smul a 0 = 0
    fin_cases a <;> simp [cl4Smul]
  smul_add a x y := by
    change cl4Smul a (x + y) = cl4Smul a x + cl4Smul a y
    fin_cases a <;> simp [cl4Smul]
  add_smul a b x := by
    change cl4Smul (a + b) x = cl4Smul a x + cl4Smul b x
    fin_cases a <;> fin_cases b <;> simp [cl4Smul, cl4RankVec_two_nsmul]
  zero_smul x := by change cl4Smul 0 x = 0; simp [cl4Smul]

instance cl4RankVec_finite (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] :
    Finite (Cl4RankVec q) :=
  Finite.of_equiv (Cl4RankSubgroup q) Additive.ofMul

instance cl4RankVec_moduleFinite (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] :
    Module.Finite (ZMod 2) (Cl4RankVec q) :=
  Module.Finite.of_finite

/-- Concrete 2-Sylow subgroup `A_2(q)` of `NarrowClassGroup q`: elements of 2-power order. -/
def narrowTwoSylow (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] : Subgroup (NarrowClassGroup q) where
  carrier := {c | ∃ k : ℕ, c ^ (2 ^ k) = 1}
  one_mem' := ⟨0, by simp⟩
  mul_mem' {a b} ha hb := by
    rcases ha with ⟨ka, hka⟩
    rcases hb with ⟨kb, hkb⟩
    refine ⟨max ka kb, ?_⟩
    rw [mul_pow]
    have ha' : a ^ (2 ^ max ka kb) = 1 := by
      have hdvd : 2 ^ ka ∣ 2 ^ max ka kb := Nat.pow_dvd_pow 2 (le_max_left ka kb)
      rcases hdvd with ⟨m, hm⟩
      rw [hm, pow_mul, hka, one_pow]
    have hb' : b ^ (2 ^ max ka kb) = 1 := by
      have hdvd : 2 ^ kb ∣ 2 ^ max ka kb := Nat.pow_dvd_pow 2 (le_max_right ka kb)
      rcases hdvd with ⟨m, hm⟩
      rw [hm, pow_mul, hkb, one_pow]
    rw [ha', hb', mul_one]
  inv_mem' {a} ha := by
    rcases ha with ⟨k, hk⟩
    exact ⟨k, by rw [inv_pow, hk, inv_one]⟩

/-- Concrete odd-part subgroup `Cl_odd^+(q)` of `NarrowClassGroup q`: elements of odd order. -/
def narrowOddPart (q : ℕ) [Fact (¬ IsSquare (q : ℚ))] : Subgroup (NarrowClassGroup q) where
  carrier := {c | ∃ m : ℕ, Odd m ∧ c ^ m = 1}
  one_mem' := ⟨1, odd_one, by simp⟩
  mul_mem' {a b} ha hb := by
    rcases ha with ⟨ma, hma, hpa⟩
    rcases hb with ⟨mb, hmb, hpb⟩
    exact ⟨ma * mb, hma.mul hmb, by rw [mul_pow, pow_mul, hpa, one_pow, one_mul, mul_comm, pow_mul, hpb, one_pow]⟩
  inv_mem' {a} ha := by
    rcases ha with ⟨m, hm, hp⟩
    exact ⟨m, hm, by rw [inv_pow, hp, inv_one]⟩

end GrasGreenbergBrocard
