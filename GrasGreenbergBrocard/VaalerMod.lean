import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsAnalytic
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.ValuationParityDigits
import GrasGreenbergBrocard.ValuationParityVaaler
import GrasGreenbergBrocard.ExpSumBounds
import GrasGreenbergBrocard.ValuationParityThmHelpers
import GrasGreenbergBrocard.ValuationParityThm
import GrasGreenbergBrocard.ExpSumBoundsMod

set_option pp.maxSteps 50
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 3
set_option pp.proofs false

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard


theorem eExp_int (k : ℤ) : eExp (k : ℝ) = 1 := by
  unfold eExp
  push_cast
  rw [show (2 : ℂ) * Real.pi * Complex.I * (k : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) from by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem norm_eExp (t : ℝ) : ‖eExp t‖ = 1 := by
  unfold eExp
  rw [show (2 : ℂ) * Real.pi * Complex.I * (t : ℂ) = (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem eExp_nsmul (k : ℕ) (t : ℝ) : (eExp t) ^ k = eExp ((k : ℝ) * t) := by
  unfold eExp
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem sum_eExp_range_eq_zero (h_mod : ℕ) (hh_mod : 2 ≤ h_mod)
    (z : ℕ) (hz1 : 1 ≤ z) (hz2 : z < h_mod) :
    ∑ k ∈ Finset.range h_mod, eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ)) = 0 := by
  let ζ : ℂ := eExp ((z : ℝ) / (h_mod : ℝ))
  have hh_pos : (0 : ℝ) < (h_mod : ℝ) := by exact_mod_cast (by omega : 0 < h_mod)
  have hsum_eq : ∑ k ∈ Finset.range h_mod, eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ)) =
      ∑ k ∈ Finset.range h_mod, ζ ^ k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    dsimp only [ζ]
    rw [eExp_nsmul]
    congr 1; ring
  have hζ_pow : ζ ^ h_mod = 1 := by
    dsimp only [ζ]
    rw [eExp_nsmul, mul_div_cancel₀ _ hh_pos.ne']
    exact_mod_cast eExp_int (z : ℤ)
  have hζ_ne : ζ ≠ 1 := by
    intro h1
    dsimp only [ζ, eExp] at h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨m, hm⟩ := h1
    have h2piI : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hC : (((z : ℝ) / (h_mod : ℝ) : ℝ) : ℂ) = (m : ℂ) := by
      apply mul_left_cancel₀ h2piI
      rw [hm]; ring
    have hR : (z : ℝ) / (h_mod : ℝ) = (m : ℝ) := by
      exact_mod_cast congrArg Complex.re hC
    have hZ : (z : ℤ) = m * (h_mod : ℤ) := by
      have := (div_eq_iff hh_pos.ne').mp hR
      exact_mod_cast this
    have hz_pos : (0 : ℤ) < (z : ℤ) := by exact_mod_cast hz1
    have hz_lt : (z : ℤ) < (h_mod : ℤ) := by exact_mod_cast hz2
    have hm_pos : 0 < m := by nlinarith
    nlinarith
  have hgeom := geom_sum_mul ζ h_mod
  rw [hζ_pow, sub_self] at hgeom
  rw [hsum_eq]
  exact mul_right_cancel₀ (sub_ne_zero.mpr hζ_ne) (by simpa using hgeom)

theorem indicator_mod_eq_sum_eExp (v c h_mod : ℕ) (hh_mod : 1 ≤ h_mod) :
    (if v ≡ c [MOD h_mod] then (1 : ℂ) else 0) =
      (1 / (h_mod : ℂ)) * ∑ z ∈ Finset.range h_mod,
        eExp ((z : ℝ) * ((v : ℝ) - (c : ℝ)) / (h_mod : ℝ)) := by
  have hh_pos : (0 : ℝ) < (h_mod : ℝ) := by exact_mod_cast hh_mod
  have hhC : (h_mod : ℂ) ≠ 0 := by exact_mod_cast (by omega : h_mod ≠ 0)
  by_cases hvc : v ≡ c [MOD h_mod]
  · rw [if_pos hvc]
    have hdvd : (h_mod : ℤ) ∣ (v : ℤ) - (c : ℤ) :=
      Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hvc.symm)
    obtain ⟨k, hk⟩ := hdvd
    have heach : ∀ z ∈ Finset.range h_mod,
        eExp ((z : ℝ) * ((v : ℝ) - (c : ℝ)) / (h_mod : ℝ)) = 1 := by
      intro z _
      have harg : (z : ℝ) * ((v : ℝ) - (c : ℝ)) / (h_mod : ℝ) = ((z * k : ℤ) : ℝ) := by
        have hkR : (v : ℝ) - (c : ℝ) = (h_mod : ℝ) * (k : ℝ) := by exact_mod_cast hk
        rw [hkR]
        push_cast
        field_simp [hh_pos.ne']
      rw [harg]
      exact eExp_int (z * k)
    rw [Finset.sum_congr rfl heach, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    field_simp [hhC]
  · rw [if_neg hvc]
    let ζ : ℂ := eExp (((v : ℝ) - (c : ℝ)) / (h_mod : ℝ))
    have hsum_eq : ∑ z ∈ Finset.range h_mod, eExp ((z : ℝ) * ((v : ℝ) - (c : ℝ)) / (h_mod : ℝ)) =
        ∑ z ∈ Finset.range h_mod, ζ ^ z := by
      refine Finset.sum_congr rfl (fun z _ => ?_)
      dsimp only [ζ]
      rw [eExp_nsmul]
      congr 1; ring
    have hζ_pow : ζ ^ h_mod = 1 := by
      dsimp only [ζ]
      rw [eExp_nsmul, mul_div_cancel₀ _ hh_pos.ne']
      have hZ : ((v : ℝ) - (c : ℝ)) = (((v : ℤ) - (c : ℤ) : ℤ) : ℝ) := by push_cast; rfl
      rw [hZ]
      exact eExp_int ((v : ℤ) - (c : ℤ))
    have hζ_ne : ζ ≠ 1 := by
      intro h1
      dsimp only [ζ, eExp] at h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨m, hm⟩ := h1
      have h2piI : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hC : ((((v : ℝ) - (c : ℝ)) / (h_mod : ℝ) : ℝ) : ℂ) = (m : ℂ) := by
        apply mul_left_cancel₀ h2piI
        rw [hm]; ring
      have hR : ((v : ℝ) - (c : ℝ)) / (h_mod : ℝ) = (m : ℝ) := by
        exact_mod_cast congrArg Complex.re hC
      have hZ : (v : ℤ) - (c : ℤ) = (h_mod : ℤ) * m := by
        have := (div_eq_iff hh_pos.ne').mp hR
        exact_mod_cast (by linarith : (v : ℝ) - (c : ℝ) = (h_mod : ℝ) * (m : ℝ))
      have hdvd : (h_mod : ℤ) ∣ (c : ℤ) - (v : ℤ) := ⟨-m, by linarith⟩
      exact hvc (Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr hdvd))
    have hgeom := geom_sum_mul ζ h_mod
    rw [hζ_pow, sub_self] at hgeom
    have h0 : ∑ z ∈ Finset.range h_mod, ζ ^ z = 0 :=
      mul_right_cancel₀ (sub_ne_zero.mpr hζ_ne) (by simpa using hgeom)
    rw [hsum_eq, h0, mul_zero]

theorem floor_mod_eq_sawtooth (h_mod : ℕ) (hh_mod : 2 ≤ h_mod)
    (x : ℝ) (k : ℕ) (hk : k < h_mod) :
    (if Int.floor x % (h_mod : ℤ) = (k : ℤ) then (1 : ℝ) else 0) =
      sawtoothPsi ((x - (k : ℝ) - 1) / (h_mod : ℝ)) -
      sawtoothPsi ((x - (k : ℝ)) / (h_mod : ℝ)) + 1 / (h_mod : ℝ) := by
  have hh_pos : (0 : ℝ) < (h_mod : ℝ) := by exact_mod_cast (by omega : 0 < h_mod)
  have hsaw : sawtoothPsi ((x - (k : ℝ) - 1) / (h_mod : ℝ)) -
      sawtoothPsi ((x - (k : ℝ)) / (h_mod : ℝ)) + 1 / (h_mod : ℝ) =
      (Int.floor ((x - (k : ℝ)) / (h_mod : ℝ)) : ℝ) -
      (Int.floor ((x - (k : ℝ) - 1) / (h_mod : ℝ)) : ℝ) := by
    unfold sawtoothPsi
    field_simp [hh_pos.ne']
    ring
  rw [hsaw]
  set q := Int.floor x / (h_mod : ℤ)
  set r := Int.floor x % (h_mod : ℤ)
  have hqr : Int.floor x = (h_mod : ℤ) * q + r := (Int.mul_ediv_add_emod (Int.floor x) (h_mod : ℤ)).symm
  have hr_ge : 0 ≤ r := Int.emod_nonneg _ (by exact_mod_cast (by omega : (h_mod : ℤ) ≠ 0))
  have hr_lt : r < (h_mod : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast (by omega : 0 < h_mod))
  have hx_lo : ((h_mod : ℝ) * (q : ℝ) + (r : ℝ)) ≤ x := by
    have := Int.floor_le x
    have hqrR : (Int.floor x : ℝ) = (h_mod : ℝ) * (q : ℝ) + (r : ℝ) := by exact_mod_cast hqr
    linarith
  have hx_hi : x < (h_mod : ℝ) * (q : ℝ) + (r : ℝ) + 1 := by
    have := Int.lt_floor_add_one x
    have hqrR : (Int.floor x : ℝ) = (h_mod : ℝ) * (q : ℝ) + (r : ℝ) := by exact_mod_cast hqr
    linarith
  rcases lt_trichotomy r (k : ℤ) with hrk | hrk | hrk
  · rw [if_neg hrk.ne]
    have hfl1 : Int.floor ((x - (k : ℝ)) / (h_mod : ℝ)) = q - 1 := by
      rw [Int.floor_eq_iff, le_div_iff₀ hh_pos, div_lt_iff₀ hh_pos]
      have hrkR : (r : ℝ) ≤ (k : ℝ) - 1 := by exact_mod_cast (by omega : r ≤ (k : ℤ) - 1)
      have hkR : (k : ℝ) ≤ (h_mod : ℝ) - 1 := by
        have : (k : ℝ) + 1 ≤ (h_mod : ℝ) := by exact_mod_cast hk
        linarith
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge
      push_cast; constructor <;> nlinarith
    have hfl2 : Int.floor ((x - (k : ℝ) - 1) / (h_mod : ℝ)) = q - 1 := by
      rw [Int.floor_eq_iff, le_div_iff₀ hh_pos, div_lt_iff₀ hh_pos]
      have hrkR : (r : ℝ) ≤ (k : ℝ) - 1 := by exact_mod_cast (by omega : r ≤ (k : ℤ) - 1)
      have hkR : (k : ℝ) ≤ (h_mod : ℝ) - 1 := by
        have : (k : ℝ) + 1 ≤ (h_mod : ℝ) := by exact_mod_cast hk
        linarith
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge
      push_cast; constructor <;> nlinarith
    rw [hfl1, hfl2]; ring
  · rw [if_pos hrk]
    have hrkR : (r : ℝ) = (k : ℝ) := by exact_mod_cast hrk
    have hfl1 : Int.floor ((x - (k : ℝ)) / (h_mod : ℝ)) = q := by
      rw [Int.floor_eq_iff, le_div_iff₀ hh_pos, div_lt_iff₀ hh_pos]
      have hh2 : (2 : ℝ) ≤ (h_mod : ℝ) := by exact_mod_cast hh_mod
      push_cast; constructor <;> nlinarith
    have hfl2 : Int.floor ((x - (k : ℝ) - 1) / (h_mod : ℝ)) = q - 1 := by
      rw [Int.floor_eq_iff, le_div_iff₀ hh_pos, div_lt_iff₀ hh_pos]
      have hh2 : (2 : ℝ) ≤ (h_mod : ℝ) := by exact_mod_cast hh_mod
      push_cast; constructor <;> nlinarith
    rw [hfl1, hfl2]; push_cast; ring
  · rw [if_neg hrk.ne']
    have hfl1 : Int.floor ((x - (k : ℝ)) / (h_mod : ℝ)) = q := by
      rw [Int.floor_eq_iff, le_div_iff₀ hh_pos, div_lt_iff₀ hh_pos]
      have hrkR : (k : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast (by omega : (k : ℤ) + 1 ≤ r)
      have hr_h : (r : ℝ) ≤ (h_mod : ℝ) - 1 := by exact_mod_cast (by omega : r ≤ (h_mod : ℤ) - 1)
      push_cast; constructor <;> nlinarith
    have hfl2 : Int.floor ((x - (k : ℝ) - 1) / (h_mod : ℝ)) = q := by
      rw [Int.floor_eq_iff, le_div_iff₀ hh_pos, div_lt_iff₀ hh_pos]
      have hrkR : (k : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast (by omega : (k : ℤ) + 1 ≤ r)
      have hr_h : (r : ℝ) ≤ (h_mod : ℝ) - 1 := by exact_mod_cast (by omega : r ≤ (h_mod : ℤ) - 1)
      push_cast; constructor <;> nlinarith
    rw [hfl1, hfl2]; ring

theorem vaaler_mod_approx (h_mod : ℕ) (hh_mod : 2 ≤ h_mod)
    (z : ℕ) (hz1 : 1 ≤ z) (hz2 : z < h_mod) (H : ℕ) (hH : 1 ≤ H) :
    ∃ (c_mod : ℤ → ℂ) (b_mod : ℤ → ℂ),
      (b_mod 0 = ((h_mod : ℝ) / ((H : ℝ) + 1) : ℂ)) ∧
      (∀ m : ℤ, ‖b_mod m‖ ≤ (h_mod : ℝ) / ((H : ℝ) + 1)) ∧
      (let Psi_mod : ℝ → ℂ := fun x =>
          ∑ m ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (· ≠ 0),
            c_mod m * eExp ((m : ℝ) * x / (h_mod : ℝ))
       let B_mod : ℝ → ℂ := fun x =>
          ∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
            b_mod m * eExp ((m : ℝ) * x / (h_mod : ℝ))
       (∀ x : ℝ, ‖eExp ((z : ℝ) * (Int.floor x : ℝ) / (h_mod : ℝ)) - Psi_mod x‖ ≤ (B_mod x).re) ∧
       (∑ m ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (· ≠ 0),
          ‖c_mod m‖ ≤ 2 * (h_mod : ℝ) * (Real.log (H : ℝ) + 1))) := by
  obtain ⟨W, hW_bounds, hVaaler⟩ := vaaler_extremal_polynomials
  obtain ⟨b, hb0, hb_bound, hV⟩ := hVaaler H hH
  let c : ℤ → ℂ := fun m =>
    if m = 0 then 0
    else -(1 / (2 * Real.pi * Complex.I * (m : ℂ))) * (W (|(m : ℝ)| / ((H : ℝ) + 1)) : ℂ)
  let c_mod : ℤ → ℂ := fun m =>
    c m * ∑ k ∈ Finset.range h_mod,
      eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ)) *
        (eExp (-(m : ℝ) * ((k : ℝ) + 1) / (h_mod : ℝ)) - eExp (-(m : ℝ) * (k : ℝ) / (h_mod : ℝ)))
  let b_mod : ℤ → ℂ := fun m =>
    b m * ∑ k ∈ Finset.range h_mod,
      (eExp (-(m : ℝ) * ((k : ℝ) + 1) / (h_mod : ℝ)) + eExp (-(m : ℝ) * (k : ℝ) / (h_mod : ℝ)))
  have hh_pos : (0 : ℝ) < (h_mod : ℝ) := by exact_mod_cast (by omega : 0 < h_mod)
  refine ⟨c_mod, b_mod, ?_, ?_, ?_⟩
  · dsimp only [b_mod]
    rw [hb0]
    have heach0 : ∀ k ∈ Finset.range h_mod,
        (eExp (-((0 : ℤ) : ℝ) * ((k : ℝ) + 1) / (h_mod : ℝ)) +
          eExp (-((0 : ℤ) : ℝ) * (k : ℝ) / (h_mod : ℝ))) = 2 := by
      intro k _
      simp [eExp]; norm_num
    rw [Finset.sum_congr rfl heach0, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    have hH0 : (H : ℂ) + 1 ≠ 0 := by exact_mod_cast (by positivity : (H : ℝ) + 1 ≠ 0)
    have h2H0 : 2 * (H : ℂ) + 2 ≠ 0 := by exact_mod_cast (by positivity : 2 * (H : ℝ) + 2 ≠ 0)
    field_simp [hH0, h2H0]
  · intro m
    dsimp only [b_mod]
    rw [norm_mul]
    have hsum_norm : ‖∑ k ∈ Finset.range h_mod,
        (eExp (-(m : ℝ) * ((k : ℝ) + 1) / (h_mod : ℝ)) + eExp (-(m : ℝ) * (k : ℝ) / (h_mod : ℝ)))‖ ≤
        2 * (h_mod : ℝ) := by
      calc ‖∑ k ∈ Finset.range h_mod, _‖
          ≤ ∑ k ∈ Finset.range h_mod,
              ‖eExp (-(m : ℝ) * ((k : ℝ) + 1) / (h_mod : ℝ)) + eExp (-(m : ℝ) * (k : ℝ) / (h_mod : ℝ))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range h_mod, (2 : ℝ) := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            calc ‖eExp _ + eExp _‖ ≤ ‖eExp _‖ + ‖eExp _‖ := norm_add_le _ _
              _ = 1 + 1 := by rw [norm_eExp, norm_eExp]
              _ = 2 := by norm_num
        _ = 2 * (h_mod : ℝ) := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    calc ‖b m‖ * ‖∑ k ∈ Finset.range h_mod, _‖
        ≤ (1 / (2 * (H : ℝ) + 2)) * (2 * (h_mod : ℝ)) :=
          mul_le_mul (hb_bound m) hsum_norm (norm_nonneg _) (by positivity)
      _ = (h_mod : ℝ) / ((H : ℝ) + 1) := by
          have hH0 : (H : ℝ) + 1 ≠ 0 := by positivity
          field_simp [hH0]
  · dsimp only
    let Psi : ℝ → ℂ := fun t =>
      ∑ m ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (· ≠ 0), c m * eExp ((m : ℝ) * t)
    let B : ℝ → ℂ := fun t =>
      ∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), b m * eExp ((m : ℝ) * t)
    constructor
    · intro x
      have hexp_eq : eExp ((z : ℝ) * (Int.floor x : ℝ) / (h_mod : ℝ)) =
          ∑ k ∈ Finset.range h_mod,
            ((if Int.floor x % (h_mod : ℤ) = (k : ℤ) then (1 : ℝ) else 0) : ℂ) *
              eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ)) := by
        let r := (Int.floor x % (h_mod : ℤ)).toNat
        have hr_ge : 0 ≤ Int.floor x % (h_mod : ℤ) :=
          Int.emod_nonneg _ (by exact_mod_cast (by omega : (h_mod : ℤ) ≠ 0))
        have hr_lt : Int.floor x % (h_mod : ℤ) < (h_mod : ℤ) :=
          Int.emod_lt_of_pos _ (by exact_mod_cast (by omega : 0 < h_mod))
        have hr_mem : r ∈ Finset.range h_mod := Finset.mem_range.mpr (by omega)
        have hr_cast : (r : ℤ) = Int.floor x % (h_mod : ℤ) := by omega
        rw [Finset.sum_eq_single r]
        · rw [if_pos hr_cast.symm, Complex.ofReal_one, one_mul]
          have hqr : Int.floor x = (h_mod : ℤ) * (Int.floor x / (h_mod : ℤ)) + (r : ℤ) := by
            rw [hr_cast]; exact (Int.mul_ediv_add_emod (Int.floor x) (h_mod : ℤ)).symm
          have hqrR : (Int.floor x : ℝ) = (h_mod : ℝ) * ((Int.floor x / (h_mod : ℤ) : ℤ) : ℝ) + (r : ℝ) := by
            exact_mod_cast hqr
          rw [hqrR]
          have harg : (z : ℝ) * ((h_mod : ℝ) * ((Int.floor x / (h_mod : ℤ) : ℤ) : ℝ) + (r : ℝ)) / (h_mod : ℝ) =
              ((z * (Int.floor x / (h_mod : ℤ)) : ℤ) : ℝ) + (z : ℝ) * (r : ℝ) / (h_mod : ℝ) := by
            push_cast; field_simp [hh_pos.ne']
          rw [harg, ← eExp_add, eExp_int, one_mul]
        · intro k _ hkr
          have hne : Int.floor x % (h_mod : ℤ) ≠ (k : ℤ) := by omega
          simp [if_neg hne]
        · intro hnot; exact absurd hr_mem hnot
      have hPsi_id : ∑ m ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (· ≠ 0),
            c_mod m * eExp ((m : ℝ) * x / (h_mod : ℝ)) =
          ∑ k ∈ Finset.range h_mod,
            (Psi ((x - (k : ℝ) - 1) / (h_mod : ℝ)) - Psi ((x - (k : ℝ)) / (h_mod : ℝ))) *
              eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ)) := by
        dsimp only [c_mod, Psi]
        have h_swap : ∑ k ∈ Finset.range h_mod,
              ((∑ m ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (· ≠ 0), c m * eExp ((m : ℝ) * ((x - (k : ℝ) - 1) / (h_mod : ℝ)))) -
               (∑ m ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (· ≠ 0), c m * eExp ((m : ℝ) * ((x - (k : ℝ)) / (h_mod : ℝ))))) *
                eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ)) =
            ∑ k ∈ Finset.range h_mod, ∑ m ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (· ≠ 0),
              c m * eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ)) *
                (eExp (-(m : ℝ) * ((k : ℝ) + 1) / (h_mod : ℝ)) - eExp (-(m : ℝ) * (k : ℝ) / (h_mod : ℝ))) *
                  eExp ((m : ℝ) * x / (h_mod : ℝ)) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← Finset.sum_sub_distrib, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          have h1 : eExp ((m : ℝ) * ((x - (k : ℝ) - 1) / (h_mod : ℝ))) =
              eExp (-(m : ℝ) * ((k : ℝ) + 1) / (h_mod : ℝ)) * eExp ((m : ℝ) * x / (h_mod : ℝ)) := by
            rw [eExp_add]; congr 1; ring
          have h2 : eExp ((m : ℝ) * ((x - (k : ℝ)) / (h_mod : ℝ))) =
              eExp (-(m : ℝ) * (k : ℝ) / (h_mod : ℝ)) * eExp ((m : ℝ) * x / (h_mod : ℝ)) := by
            rw [eExp_add]; congr 1; ring
          rw [h1, h2]; ring
        rw [h_swap, Finset.sum_comm]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun k _ => by ring)
      have hB_id : (∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
            b_mod m * eExp ((m : ℝ) * x / (h_mod : ℝ))).re =
          ∑ k ∈ Finset.range h_mod,
            ((B ((x - (k : ℝ) - 1) / (h_mod : ℝ))).re + (B ((x - (k : ℝ)) / (h_mod : ℝ))).re) := by
        dsimp only [b_mod, B]
        rw [Complex.re_sum]
        have h_swap : ∑ k ∈ Finset.range h_mod,
              ((∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), b m * eExp ((m : ℝ) * ((x - (k : ℝ) - 1) / (h_mod : ℝ)))).re +
               (∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), b m * eExp ((m : ℝ) * ((x - (k : ℝ)) / (h_mod : ℝ)))).re) =
            (∑ k ∈ Finset.range h_mod, ∑ m ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
              b m * (eExp (-(m : ℝ) * ((k : ℝ) + 1) / (h_mod : ℝ)) + eExp (-(m : ℝ) * (k : ℝ) / (h_mod : ℝ))) *
                eExp ((m : ℝ) * x / (h_mod : ℝ))).re := by
          rw [Complex.re_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← Complex.add_re, ← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl (fun m _ => ?_)
          have h1 : eExp ((m : ℝ) * ((x - (k : ℝ) - 1) / (h_mod : ℝ))) =
              eExp (-(m : ℝ) * ((k : ℝ) + 1) / (h_mod : ℝ)) * eExp ((m : ℝ) * x / (h_mod : ℝ)) := by
            rw [eExp_add]; congr 1; ring
          have h2 : eExp ((m : ℝ) * ((x - (k : ℝ)) / (h_mod : ℝ))) =
              eExp (-(m : ℝ) * (k : ℝ) / (h_mod : ℝ)) * eExp ((m : ℝ) * x / (h_mod : ℝ)) := by
            rw [eExp_add]; congr 1; ring
          rw [h1, h2]; ring
        rw [h_swap, Finset.sum_comm, Complex.re_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        congr 1
        rw [Finset.mul_sum, Finset.sum_mul]
      rw [hexp_eq, hPsi_id, hB_id]
      have h0_cancel : ∑ k ∈ Finset.range h_mod,
          ((1 / (h_mod : ℝ) : ℝ) : ℂ) * eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ)) = 0 := by
        rw [← Finset.mul_sum, sum_eExp_range_eq_zero h_mod hh_mod z hz1 hz2, mul_zero]
      have h_diff_eq :
          (∑ k ∈ Finset.range h_mod,
              ((if Int.floor x % (h_mod : ℤ) = (k : ℤ) then (1 : ℝ) else 0) : ℂ) *
                eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ))) -
          (∑ k ∈ Finset.range h_mod,
              (Psi ((x - (k : ℝ) - 1) / (h_mod : ℝ)) - Psi ((x - (k : ℝ)) / (h_mod : ℝ))) *
                eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ))) =
          ∑ k ∈ Finset.range h_mod,
            (((sawtoothPsi ((x - (k : ℝ) - 1) / (h_mod : ℝ)) : ℂ) - Psi ((x - (k : ℝ) - 1) / (h_mod : ℝ))) -
             ((sawtoothPsi ((x - (k : ℝ)) / (h_mod : ℝ)) : ℂ) - Psi ((x - (k : ℝ)) / (h_mod : ℝ)))) *
              eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ)) := by
        rw [← sub_zero (∑ k ∈ Finset.range h_mod,
            (Psi ((x - (k : ℝ) - 1) / (h_mod : ℝ)) - Psi ((x - (k : ℝ)) / (h_mod : ℝ))) *
              eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ)))]
        conv_lhs => rhs; rhs; rw [← h0_cancel]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hfl := floor_mod_eq_sawtooth h_mod hh_mod x k (Finset.mem_range.mp hk)
        have hflC : ((if Int.floor x % (h_mod : ℤ) = (k : ℤ) then (1 : ℝ) else 0) : ℂ) =
            ((sawtoothPsi ((x - (k : ℝ) - 1) / (h_mod : ℝ)) : ℂ) -
              (sawtoothPsi ((x - (k : ℝ)) / (h_mod : ℝ)) : ℂ) + ((1 / (h_mod : ℝ) : ℝ) : ℂ)) := by
          have h1 := congrArg Complex.ofReal hfl
          simpa only [Complex.ofReal_add, Complex.ofReal_sub] using h1
        rw [hflC]
        ring
      rw [h_diff_eq]
      calc ‖∑ k ∈ Finset.range h_mod, _‖
          ≤ ∑ k ∈ Finset.range h_mod,
              ‖(((sawtoothPsi ((x - (k : ℝ) - 1) / (h_mod : ℝ)) : ℂ) - Psi ((x - (k : ℝ) - 1) / (h_mod : ℝ))) -
               ((sawtoothPsi ((x - (k : ℝ)) / (h_mod : ℝ)) : ℂ) - Psi ((x - (k : ℝ)) / (h_mod : ℝ)))) *
                eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ))‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range h_mod,
              ((B ((x - (k : ℝ) - 1) / (h_mod : ℝ))).re + (B ((x - (k : ℝ)) / (h_mod : ℝ))).re) := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            rw [norm_mul, norm_eExp, mul_one]
            refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
            · have h1 := (hV.1 ((x - (k : ℝ) - 1) / (h_mod : ℝ))).2
              dsimp only [Psi, B, c]; simpa [sawtoothPsi] using h1
            · have h2 := (hV.1 ((x - (k : ℝ)) / (h_mod : ℝ))).2
              dsimp only [Psi, B, c]; simpa [sawtoothPsi] using h2
    · have hc_each : ∀ m ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (· ≠ 0),
          ‖c_mod m‖ ≤ (h_mod : ℝ) / (Real.pi * |(m : ℝ)|) := by
        intro m hm
        have hm0 : m ≠ 0 := (Finset.mem_filter.mp hm).2
        dsimp only [c_mod]
        rw [norm_mul]
        have hc_norm : ‖c m‖ ≤ 1 / (2 * Real.pi * |(m : ℝ)|) := by
          dsimp only [c]; rw [if_neg hm0]
          rw [norm_mul, norm_neg, norm_div, norm_one, Complex.norm_real]
          have hden : ‖(2 : ℂ) * Real.pi * Complex.I * (m : ℂ)‖ = 2 * Real.pi * |(m : ℝ)| := by
            rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one,
              show ‖(2 : ℂ)‖ = 2 from by norm_num,
              show ‖(Real.pi : ℂ)‖ = Real.pi from by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos],
              show ‖(m : ℂ)‖ = |(m : ℝ)| from by rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]]
          have hW : |W (|(m : ℝ)| / ((H : ℝ) + 1))| ≤ 1 := by
            have hb := hW_bounds (|(m : ℝ)| / ((H : ℝ) + 1))
            rw [abs_of_nonneg hb.1]; exact hb.2
          rw [hden]
          calc (1 / (2 * Real.pi * |(m : ℝ)|)) * |W (|(m : ℝ)| / ((H : ℝ) + 1))|
              ≤ (1 / (2 * Real.pi * |(m : ℝ)|)) * 1 := mul_le_mul_of_nonneg_left hW (by positivity)
            _ = 1 / (2 * Real.pi * |(m : ℝ)|) := mul_one _
        have hsum_norm : ‖∑ k ∈ Finset.range h_mod,
              eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ)) *
                (eExp (-(m : ℝ) * ((k : ℝ) + 1) / (h_mod : ℝ)) - eExp (-(m : ℝ) * (k : ℝ) / (h_mod : ℝ)))‖ ≤
            2 * (h_mod : ℝ) := by
          calc ‖∑ k ∈ Finset.range h_mod, _‖
              ≤ ∑ k ∈ Finset.range h_mod,
                  ‖eExp ((z : ℝ) * (k : ℝ) / (h_mod : ℝ)) *
                    (eExp (-(m : ℝ) * ((k : ℝ) + 1) / (h_mod : ℝ)) - eExp (-(m : ℝ) * (k : ℝ) / (h_mod : ℝ)))‖ :=
                norm_sum_le _ _
            _ ≤ ∑ _k ∈ Finset.range h_mod, (2 : ℝ) := by
                refine Finset.sum_le_sum (fun k _ => ?_)
                rw [norm_mul, norm_eExp, one_mul]
                calc ‖eExp _ - eExp _‖ ≤ ‖eExp _‖ + ‖eExp _‖ := norm_sub_le _ _
                  _ = 1 + 1 := by rw [norm_eExp, norm_eExp]
                  _ = 2 := by norm_num
            _ = 2 * (h_mod : ℝ) := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        calc ‖c m‖ * ‖∑ k ∈ Finset.range h_mod, _‖
            ≤ (1 / (2 * Real.pi * |(m : ℝ)|)) * (2 * (h_mod : ℝ)) :=
              mul_le_mul hc_norm hsum_norm (norm_nonneg _) (by positivity)
          _ = (h_mod : ℝ) / (Real.pi * |(m : ℝ)|) := by ring
      let posSet : Finset ℤ := (Finset.Icc (1 : ℕ) H).image (fun k : ℕ => (k : ℤ))
      let negSet : Finset ℤ := (Finset.Icc (1 : ℕ) H).image (fun k : ℕ => -(k : ℤ))
      have hsub : ((Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (· ≠ 0)) ⊆ posSet ∪ negSet := by
        intro m hm
        simp only [Finset.mem_filter, Finset.mem_Icc] at hm
        rw [Finset.mem_union]
        rcases lt_trichotomy m 0 with hneg | rfl | hpos
        · right; rw [Finset.mem_image]; refine ⟨(-m).toNat, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · exact absurd rfl hm.2
        · left; rw [Finset.mem_image]; refine ⟨m.toNat, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      have hdisj_pn : Disjoint posSet negSet := by
        rw [Finset.disjoint_left]; intro m hp hn
        rw [Finset.mem_image] at hp hn
        obtain ⟨k1, hk1, rfl⟩ := hp; obtain ⟨k2, hk2, _⟩ := hn
        have h1 : 1 ≤ k1 := (Finset.mem_Icc.mp hk1).1
        have h2 : 1 ≤ k2 := (Finset.mem_Icc.mp hk2).1
        omega
      have h_pos_sum : ∑ m ∈ posSet, ((h_mod : ℝ) / (Real.pi * |(m : ℝ)|)) =
          ∑ k ∈ Finset.Icc (1 : ℕ) H, ((h_mod : ℝ) / (Real.pi * (k : ℝ))) := by
        dsimp only [posSet]
        rw [Finset.sum_image (g := fun k : ℕ => (k : ℤ)) (fun _ _ _ _ h => Int.ofNat.inj h)]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Int.cast_natCast, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
      have h_neg_sum : ∑ m ∈ negSet, ((h_mod : ℝ) / (Real.pi * |(m : ℝ)|)) =
          ∑ k ∈ Finset.Icc (1 : ℕ) H, ((h_mod : ℝ) / (Real.pi * (k : ℝ))) := by
        dsimp only [negSet]
        rw [Finset.sum_image (g := fun k : ℕ => -(k : ℤ)) (fun _ _ _ _ h => Int.ofNat.inj (neg_inj.mp h))]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp only [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
      calc ∑ m ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (· ≠ 0), ‖c_mod m‖
          ≤ ∑ m ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (· ≠ 0), ((h_mod : ℝ) / (Real.pi * |(m : ℝ)|)) :=
            Finset.sum_le_sum hc_each
        _ ≤ ∑ m ∈ posSet ∪ negSet, ((h_mod : ℝ) / (Real.pi * |(m : ℝ)|)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ = 2 * ∑ k ∈ Finset.Icc (1 : ℕ) H, ((h_mod : ℝ) / (Real.pi * (k : ℝ))) := by
            rw [Finset.sum_union hdisj_pn, h_pos_sum, h_neg_sum]; ring
        _ = (2 * (h_mod : ℝ) / Real.pi) * ∑ k ∈ Finset.Icc (1 : ℕ) H, (1 : ℝ) / (k : ℝ) := by
            rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
        _ ≤ (2 * (h_mod : ℝ) / Real.pi) * (Real.log (H : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (harmonic_sum_le_log_add_one hH) (by positivity)
        _ ≤ 2 * (h_mod : ℝ) * (Real.log (H : ℝ) + 1) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
            exact div_le_self (by positivity) hpi


end GrasGreenbergBrocard
