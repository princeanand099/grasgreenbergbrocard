import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.PellFundamental

/-!
# Proposition 3.3: Imaginary Quadratic Picard 2-Torsion Dichotomy

Formalizes Section 3.3 (Proposition 3.3, eq. 3.8) of the manuscript completely without
external axioms:
- `J_n_sq_eq`: in `O_n^- = ℤ[√(-q_n)]`, `(m, 1 + s_n √(-q_n))^2 = (1 + s_n √(-q_n))`
- `zsqrtd_neg_units`: for `q_n ≥ 6`, the unit group of `ℤ[√(-q_n)]` is `{±1}`
- `J_n_principal_iff_k_eq_2`: `𝔍_n` is principal iff `k = 2` (using `neg_pell_no_int_sol`)
- `k_eq_1_picard_identity`: in the `k = 1` regime, `δ₂ * (1 + s_n √(-q_n)) = (δ₂ z₂ + z₁ √(-q_n))^2`
- `second_stage_nonprincipal_k_eq_2`: in the `k = 2` regime, `1 + Y₁ √(-q_n)` is not `±(u + v√(-q_n))^2`
-/

namespace GrasGreenbergBrocard

@[simp] private lemma zsqrtd_mul_re' (D : ℤ) (x y : Zsqrtd D) :
    (x * y).re = x.re * y.re + D * x.im * y.im := by ring_nf; rfl

@[simp] private lemma zsqrtd_natCast_re (D : ℤ) (a : ℕ) : ((a : Zsqrtd D)).re = (a : ℤ) := rfl

@[simp] private lemma zsqrtd_natCast_im (D : ℤ) (a : ℕ) : ((a : Zsqrtd D)).im = 0 := rfl

@[simp] private lemma zsqrtd_neg_re (D : ℤ) (x : Zsqrtd D) : (-x).re = -x.re := rfl

@[simp] private lemma zsqrtd_mul_im' (D : ℤ) (x y : Zsqrtd D) :
    (x * y).im = x.re * y.im + x.im * y.re := by ring_nf; rfl

/-- For `n ≥ 4`, `n! + 1 = m^2` implies `m` is odd (`m % 2 = 1`). -/
lemma m_odd_of_brocard {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    m % 2 = 1 := by
  have h2_dvd : 2 ∣ Nat.factorial n :=
    (Nat.Prime.dvd_factorial (by decide : Nat.Prime 2)).mpr (by omega)
  have hmod : m ^ 2 % 2 = 1 := by omega
  by_contra h0
  have hev : m % 2 = 0 := by omega
  have h2m : 2 ∣ m := Nat.dvd_of_mod_eq_zero hev
  have h4m : 2 ∣ m ^ 2 := dvd_pow h2m (by norm_num)
  omega

/-- For `D ≥ 2`, any unit `w : Zsqrtd (-D)` satisfies `w = 1 ∨ w = -1`. -/
theorem zsqrtd_neg_units {D : ℕ} (hD : 2 ≤ D) (w : (Zsqrtd (-(D : ℤ)))ˣ) :
    (w : Zsqrtd (-(D : ℤ))) = 1 ∨ (w : Zsqrtd (-(D : ℤ))) = -1 := by
  set a := (w : Zsqrtd (-(D : ℤ))).re
  set b := (w : Zsqrtd (-(D : ℤ))).im
  set w' := (w⁻¹ : (Zsqrtd (-(D : ℤ)))ˣ)
  have hmul : (w : Zsqrtd (-(D : ℤ))) * (w' : Zsqrtd (-(D : ℤ))) = 1 := by
    exact_mod_cast w.mul_inv
  -- Norm of `w` is `a^2 + D * b^2`, and `norm(w) * norm(w') = 1`
  have hnorm : (a ^ 2 + (D : ℤ) * b ^ 2) *
      ((w' : Zsqrtd (-(D : ℤ))).re ^ 2 + (D : ℤ) * (w' : Zsqrtd (-(D : ℤ))).im ^ 2) = 1 := by
    have h1 := congrArg Zsqrtd.norm hmul
    rw [Zsqrtd.norm_mul] at h1
    simp only [Zsqrtd.norm, Zsqrtd.one_re, Zsqrtd.one_im] at h1
    have hD_neg : -( -(D : ℤ) ) = (D : ℤ) := neg_neg _
    simpa [a, b, mul_comm, sub_neg_eq_add] using h1
  have hnn1 : 0 ≤ a ^ 2 + (D : ℤ) * b ^ 2 := by positivity
  have hnorm_one : a ^ 2 + (D : ℤ) * b ^ 2 = 1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hnorm with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · linarith
  have hb0 : b = 0 := by
    by_contra hb
    have hb2 : 1 ≤ b ^ 2 := by nlinarith
    have hD2 : (2 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
    have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
    nlinarith
  have ha2 : a ^ 2 = 1 := by
    rw [hb0] at hnorm_one
    linarith
  rcases sq_eq_one_iff.mp ha2 with ha1 | ha_neg1
  · left
    ext <;> simp [a, b, ha1, hb0]
  · right
    ext <;> simp [a, b, ha_neg1, hb0]

/-- **Proposition 3.3, part 1**: In `O_n^- = ℤ[√(-q_n)]`, the ideal `𝔍_n = (m, 1 + s_n √(-q_n))`
satisfies `𝔍_n^2 = (1 + s_n √(-q_n))`. -/
theorem J_n_sq_eq {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    (Ideal.span {(m : Zsqrtd (-(q_n n : ℤ))), ⟨1, (s_n n : ℤ)⟩}) ^ 2 =
      Ideal.span {⟨1, (s_n n : ℤ)⟩} := by
  set R := Zsqrtd (-(q_n n : ℤ))
  set α : R := ⟨1, (s_n n : ℤ)⟩
  set β : R := ⟨1, -(s_n n : ℤ)⟩
  have hfac := factorial_eq_q_n_mul_s_n_sq n
  have hαβ : α * β = ((m : R) ^ 2) := by
    ext
    · simp only [α, β, zsqrtd_mul_re', zsqrtd_natCast_re, zsqrtd_natCast_im]
      have h1 : (m : ℤ) ^ 2 = (q_n n : ℤ) * (s_n n : ℤ) ^ 2 + 1 := by
        exact_mod_cast (by linarith : q_n n * (s_n n) ^ 2 + 1 = m ^ 2)
      linarith
    · simp only [α, β, zsqrtd_mul_im']
      ring
  have hsum_2 : α + β = (2 : R) := by
    ext <;> simp [α, β]
  have hm_odd : m % 2 = 1 := m_odd_of_brocard hn hm
  have hcop_int : (2 : ℤ) ∣ 1 - (m : ℤ) ^ 2 := by
    have : (m : ℤ) % 2 = 1 := by exact_mod_cast hm_odd
    omega
  obtain ⟨t, ht⟩ := hcop_int
  have h1_in_sum : (1 : R) ∈ Ideal.span {α} + Ideal.span {β} := by
    have h2_mem : (2 : R) ∈ Ideal.span {α} + Ideal.span {β} := by
      rw [← hsum_2]
      exact Ideal.add_mem _ (Ideal.subset_span rfl) (Ideal.subset_span rfl)
    have hm2_mem : (m : R) ^ 2 ∈ Ideal.span {α} + Ideal.span {β} := by
      rw [← hαβ]
      exact Ideal.mem_sup_left (Ideal.mul_mem_right β _ (Ideal.subset_span rfl))
    have h1_eq : (1 : R) = (t : R) * (2 : R) + (m : R) ^ 2 := by
      have : (1 : ℤ) = t * 2 + (m : ℤ) ^ 2 := by linarith
      ext <;> simp [this]
    rw [h1_eq]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2_mem) hm2_mem
  have hcop_ideals : Ideal.span {α} + Ideal.span {β} = ⊤ :=
    Ideal.eq_top_iff_one.mpr h1_in_sum
  apply le_antisymm
  · rw [sq, Ideal.span_mul_span]
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_mul, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · -- `m * m = α * β ∈ span {α}`
      rw [← sq, ← hαβ]
      exact Ideal.mem_span_singleton.mpr ⟨β, rfl⟩
    · -- `m * α ∈ span {α}`
      exact Ideal.mem_span_singleton.mpr ⟨(m : R), mul_comm _ _⟩
    · -- `α * m ∈ span {α}`
      exact Ideal.mem_span_singleton.mpr ⟨(m : R), rfl⟩
    · -- `α * α ∈ span {α}`
      exact Ideal.mem_span_singleton.mpr ⟨α, rfl⟩
  · -- `α = 1 * α ∈ (span {α} + span {β}) * span {m, α}?`
    -- Since `1 = t * (α + β) + α * β`, `α = t * α * α + t * (α * β) + α * (α * β) = t * α^2 + (t + α) * m^2 ∈ span {m, α}^2`!
    rw [Ideal.span_singleton_le_iff_mem]
    have hα_eq : α = (t : R) * α ^ 2 + ((t : R) + α) * (m : R) ^ 2 := by
      have h1 : (1 : R) = (t : R) * (α + β) + α * β := by
        rw [hsum_2, hαβ]
        have : (1 : ℤ) = t * 2 + (m : ℤ) ^ 2 := by linarith
        ext <;> simp [this]
      calc α = α * 1 := (mul_one α).symm
        _ = α * ((t : R) * (α + β) + α * β) := by rw [← h1]
        _ = (t : R) * α ^ 2 + ((t : R) + α) * (α * β) := by ring
        _ = (t : R) * α ^ 2 + ((t : R) + α) * (m : R) ^ 2 := by rw [hαβ]
    rw [hα_eq]
    have hα_in : α ∈ Ideal.span {(m : R), α} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hm_in : (m : R) ∈ Ideal.span {(m : R), α} := Ideal.subset_span (Set.mem_insert _ _)
    have hα2_in : α ^ 2 ∈ (Ideal.span {(m : R), α}) ^ 2 := by
      rw [sq]; exact Ideal.mul_mem_mul hα_in hα_in
    have hm2_in : (m : R) ^ 2 ∈ (Ideal.span {(m : R), α}) ^ 2 := by
      rw [sq]; exact Ideal.mul_mem_mul hm_in hm_in
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hα2_in) (Ideal.mul_mem_left _ _ hm2_in)

/-- **Proposition 3.3, part 2 (`[𝔍_n] = 1 ⟺ k = 2`)**:
For `n ≥ 4`, `n ≠ 6` with `n! + 1 = m^2`, the ideal `𝔍_n = (m, 1 + s_n √(-q_n))` is principal
in `ℤ[√(-q_n)]` if and only if there exist positive integers `u, v` with `u^2 - q_n * v^2 = 1`
and `m + s_n √q_n = (u + v √q_n)^2`. -/
theorem J_n_principal_iff_k_eq_2 {n m : ℕ} (hn : 4 ≤ n) (hn6 : n ≠ 6)
    (hm : Nat.factorial n + 1 = m ^ 2) :
    (∃ z : Zsqrtd (-(q_n n : ℤ)),
        Ideal.span {(m : Zsqrtd (-(q_n n : ℤ))), ⟨1, (s_n n : ℤ)⟩} = Ideal.span {z}) ↔
      (∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u ^ 2 = q_n n * v ^ 2 + 1 ∧
        (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = ((u : ℝ) + (v : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2) := by
  set R := Zsqrtd (-(q_n n : ℤ))
  have hq_ge2 : 2 ≤ q_n n := by
    obtain ⟨p, hp, hpq, _⟩ := q_n_has_prime_mod4 (by omega) hn6
    have hq_pos : 0 < q_n n := by
      unfold q_n
      exact Finset.prod_pos (fun q hq => (Finset.mem_filter.mp hq).2.1.pos)
    exact le_trans hp.two_le (Nat.le_of_dvd hq_pos hpq)
  constructor
  · rintro ⟨z, hz⟩
    have hsq : Ideal.span {z ^ 2} = Ideal.span {⟨1, (s_n n : ℤ)⟩} := by
      rw [← Ideal.span_singleton_pow, ← hz, J_n_sq_eq hn hm]
    obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp hsq
    have hunit : w = 1 ∨ w = -1 := by
      have := zsqrtd_neg_units hq_ge2 w
      rcases this with h1 | h1
      · left; exact Units.ext h1
      · right; exact Units.ext h1
    have hneg_impossible : z ^ 2 * (-1 : R) ≠ ⟨1, (s_n n : ℤ)⟩ := by
      intro heq
      have hre : -(z.re ^ 2 - (q_n n : ℤ) * z.im ^ 2) = 1 := by
        have := congrArg Zsqrtd.re heq
        simp only [zsqrtd_mul_re', zsqrtd_neg_re, Zsqrtd.one_re, Zsqrtd.neg_im, Zsqrtd.one_im,
          sq, zsqrtd_mul_im'] at this
        linarith
      obtain ⟨p, hp, hpq, hmod⟩ := q_n_has_prime_mod4 (by omega) hn6
      exact neg_pell_no_int_sol hp hpq hmod z.re z.im (by linarith)
    have hz2_eq : z ^ 2 = ⟨1, (s_n n : ℤ)⟩ := by
      rcases hunit with rfl | rfl
      · simpa using hw
      · exfalso; exact hneg_impossible (by simpa using hw)
    have hre : z.re ^ 2 - (q_n n : ℤ) * z.im ^ 2 = 1 := by
      have := congrArg Zsqrtd.re hz2_eq
      simp only [sq, zsqrtd_mul_re'] at this
      linarith
    have him : 2 * z.re * z.im = (s_n n : ℤ) := by
      have := congrArg Zsqrtd.im hz2_eq
      simp only [sq, zsqrtd_mul_im'] at this
      linarith
    refine ⟨z.re.natAbs, z.im.natAbs, ?_, ?_, ?_, ?_⟩
    · by_contra h0
      have hz0 : z.re = 0 := Int.natAbs_eq_zero.mp (by omega)
      rw [hz0] at him; simp at him
      have hs_pos : 0 < s_n n := by
        unfold s_n; exact Finset.prod_pos (fun q hq => pow_pos (Finset.mem_filter.mp hq).2.pos _)
      omega
    · by_contra h0
      have hz0 : z.im = 0 := Int.natAbs_eq_zero.mp (by omega)
      rw [hz0] at him; simp at him
      have hs_pos : 0 < s_n n := by
        unfold s_n; exact Finset.prod_pos (fun q hq => pow_pos (Finset.mem_filter.mp hq).2.pos _)
      omega
    · zify
      rw [sq_abs, sq_abs]
      linarith
    · have hsign : (z.re.natAbs : ℝ) * (z.im.natAbs : ℝ) = (z.re : ℝ) * (z.im : ℝ) := by
        have him_pos : (0 : ℤ) < z.re * z.im := by
          have hs_pos : 0 < s_n n := by
            unfold s_n; exact Finset.prod_pos (fun q hq => pow_pos (Finset.mem_filter.mp hq).2.pos _)
          linarith
        have h1 : (z.re.natAbs : ℤ) * (z.im.natAbs : ℤ) = |z.re * z.im| := by
          rw [← Int.abs_eq_natAbs, ← Int.abs_eq_natAbs, abs_mul]
        rw [abs_of_pos him_pos] at h1
        exact_mod_cast h1
      have hsq_q : Real.sqrt (q_n n : ℝ) ^ 2 = (q_n n : ℝ) := Real.sq_sqrt (by positivity)
      have hu2_v2 : (z.re.natAbs : ℝ) ^ 2 + (q_n n : ℝ) * (z.im.natAbs : ℝ) ^ 2 = (m : ℝ) := by
        have hm_sq : (m : ℝ) ^ 2 = ((z.re.natAbs : ℝ) ^ 2 + (q_n n : ℝ) * (z.im.natAbs : ℝ) ^ 2) ^ 2 := by
          have h1 : (z.re.natAbs : ℝ) ^ 2 - (q_n n : ℝ) * (z.im.natAbs : ℝ) ^ 2 = 1 := by
            have : (z.re : ℝ) ^ 2 - (q_n n : ℝ) * (z.im : ℝ) ^ 2 = 1 := by exact_mod_cast hre
            rw [← sq_abs (z.re : ℝ), ← sq_abs (z.im : ℝ), Int.cast_natAbs, Int.cast_natAbs]
            exact this
          have h2 : (2 * (z.re.natAbs : ℝ) * (z.im.natAbs : ℝ)) ^ 2 = (s_n n : ℝ) ^ 2 := by
            rw [mul_assoc, hsign]
            have : 2 * (z.re : ℝ) * (z.im : ℝ) = (s_n n : ℝ) := by exact_mod_cast him
            rw [← mul_assoc, this]
          have hfac := factorial_eq_q_n_mul_s_n_sq n
          have hm_r : (m : ℝ) ^ 2 = (q_n n : ℝ) * (s_n n : ℝ) ^ 2 + 1 := by
            exact_mod_cast (by linarith : q_n n * (s_n n) ^ 2 + 1 = m ^ 2)
          nlinarith
        have hm_nn : 0 ≤ (m : ℝ) := by positivity
        have hr_nn : 0 ≤ (z.re.natAbs : ℝ) ^ 2 + (q_n n : ℝ) * (z.im.natAbs : ℝ) ^ 2 := by positivity
        nlinarith [sq_nonneg ((m : ℝ) - ((z.re.natAbs : ℝ) ^ 2 + (q_n n : ℝ) * (z.im.natAbs : ℝ) ^ 2))]
      calc (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)
          = ((z.re.natAbs : ℝ) ^ 2 + (q_n n : ℝ) * (z.im.natAbs : ℝ) ^ 2) +
              (2 * (z.re.natAbs : ℝ) * (z.im.natAbs : ℝ)) * Real.sqrt (q_n n : ℝ) := by
            rw [hu2_v2, mul_assoc, hsign]; congr 2; exact_mod_cast him.symm
        _ = ((z.re.natAbs : ℝ) + (z.im.natAbs : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2 := by
            ring_nf; rw [hsq_q]; ring
  · rintro ⟨u, v, _, _, huv, hms⟩
    have hq_nsq : ¬ IsSquare (q_n n) := by
      rintro ⟨r, hr⟩
      have hsqf := q_n_squarefree n
      have hr2 : r ^ 2 ∣ q_n n := ⟨1, by linarith⟩
      have hru : IsUnit r := hsqf r hr2
      have hr1 : r = 1 := Nat.isUnit_iff.mp hru
      subst hr1
      omega
    have hsqrt_irr : Irrational (Real.sqrt (q_n n : ℝ)) := by
      rw [irrational_iff_ne_rational]
      intro a b hb hab
      have hb0 : b ≠ 0 := hb
      have hrat : (a : ℤ) ^ 2 = (q_n n : ℤ) * (b : ℤ) ^ 2 := by
        have h1 : ((a : ℝ) / (b : ℝ)) ^ 2 = (q_n n : ℝ) := by
          rw [← hab, Real.sq_sqrt (by positivity)]
        have hb_r : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
        have h2 : (a : ℝ) ^ 2 = (q_n n : ℝ) * (b : ℝ) ^ 2 := by
          field_simp [hb_r] at h1; exact h1
        exact_mod_cast h2
      obtain ⟨p, hp, hpq, _⟩ := q_n_has_prime_mod4 (by omega) hn6
      haveI : Fact p.Prime := ⟨hp⟩
      have hsqf : ¬ p ^ 2 ∣ q_n n := (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp
      have ha_ne : a.natAbs ≠ 0 := by
        intro h0
        have ha0 : a = 0 := Int.natAbs_eq_zero.mp h0
        rw [ha0] at hrat; simp at hrat
        rcases hrat with hq0 | hb_eq0
        · exact hq_ge2.not_lt (by omega)
        · exact hb0 (by exact_mod_cast hb_eq0)
      have hnat : a.natAbs ^ 2 = q_n n * b.natAbs ^ 2 := by
        have := congrArg Int.natAbs hrat
        simpa [Int.natAbs_mul, Int.natAbs_pow] using this
      have hv_lhs : padicValNat p (a.natAbs ^ 2) = 2 * padicValNat p a.natAbs :=
        (by rw [sq]; exact padicValNat.mul ha_ne ha_ne)
      have hv_q : padicValNat p (q_n n) = 1 := by
        have hq_ne : q_n n ≠ 0 := by omega
        have h1 : 1 ≤ padicValNat p (q_n n) := (padicValNat_dvd_iff_le hq_ne).mp (by simpa using hpq)
        have h2 : ¬ 2 ≤ padicValNat p (q_n n) := by
          intro hle; exact hsqf ((padicValNat_dvd_iff_le hq_ne).mpr hle)
        omega
      have hv_rhs : padicValNat p (q_n n * b.natAbs ^ 2) = 1 + 2 * padicValNat p b.natAbs := by
        have hb_nat_ne : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb0
        rw [padicValNat.mul (by omega) (pow_ne_zero 2 hb_nat_ne), hv_q, (by rw [sq]; exact padicValNat.mul hb_nat_ne hb_nat_ne)]
      omega
    have hm_eq : m = u ^ 2 + q_n n * v ^ 2 := by
      have hsq : Real.sqrt (q_n n : ℝ) ^ 2 = (q_n n : ℝ) := Real.sq_sqrt (by positivity)
      have h_lin : ((m : ℝ) - ((u : ℝ) ^ 2 + (q_n n : ℝ) * (v : ℝ) ^ 2)) =
          (2 * (u : ℝ) * (v : ℝ) - (s_n n : ℝ)) * Real.sqrt (q_n n : ℝ) := by
        have hms' : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) =
            ((u : ℝ) ^ 2 + (q_n n : ℝ) * (v : ℝ) ^ 2) + (2 * (u : ℝ) * (v : ℝ)) * Real.sqrt (q_n n : ℝ) := by
          calc (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)
              = ((u : ℝ) + (v : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2 := hms
            _ = (u : ℝ) ^ 2 + (v : ℝ) ^ 2 * (Real.sqrt (q_n n : ℝ)) ^ 2 +
                  2 * (u : ℝ) * (v : ℝ) * Real.sqrt (q_n n : ℝ) := by ring
            _ = ((u : ℝ) ^ 2 + (q_n n : ℝ) * (v : ℝ) ^ 2) +
                  (2 * (u : ℝ) * (v : ℝ)) * Real.sqrt (q_n n : ℝ) := by rw [hsq]; ring
        linarith
      have hcoeff0 : 2 * (u : ℝ) * (v : ℝ) - (s_n n : ℝ) = 0 := by
        by_contra hne
        have hrat : Real.sqrt (q_n n : ℝ) =
            ((m : ℤ) - ((u : ℤ) ^ 2 + (q_n n : ℤ) * (v : ℤ) ^ 2) : ℤ) /
              ((2 * (u : ℤ) * (v : ℤ) - (s_n n : ℤ) : ℤ) : ℝ) := by
          push_cast
          field_simp [hne]
          linarith
        exact hsqrt_irr ⟨_, hrat.symm⟩
      have hm_r : (m : ℝ) = (u : ℝ) ^ 2 + (q_n n : ℝ) * (v : ℝ) ^ 2 := by
        rw [hcoeff0, zero_mul] at h_lin; linarith
      exact_mod_cast hm_r
    have hs_eq : s_n n = 2 * u * v := by
      have hsq : Real.sqrt (q_n n : ℝ) ^ 2 = (q_n n : ℝ) := Real.sq_sqrt (by positivity)
      have h_lin : (2 * (u : ℝ) * (v : ℝ) - (s_n n : ℝ)) * Real.sqrt (q_n n : ℝ) = 0 := by
        have hm_r : (m : ℝ) = (u : ℝ) ^ 2 + (q_n n : ℝ) * (v : ℝ) ^ 2 := by exact_mod_cast hm_eq
        calc (2 * (u : ℝ) * (v : ℝ) - (s_n n : ℝ)) * Real.sqrt (q_n n : ℝ)
            = ((u : ℝ) + (v : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2 -
                ((u : ℝ) ^ 2 + (q_n n : ℝ) * (v : ℝ) ^ 2) - (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) := by
              ring_nf; rw [hsq]; ring
          _ = (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) - (m : ℝ) -
                (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) := by rw [← hms, ← hm_r]
          _ = 0 := by ring
      have hsqrt_ne : Real.sqrt (q_n n : ℝ) ≠ 0 := by positivity
      have h0 : 2 * (u : ℝ) * (v : ℝ) - (s_n n : ℝ) = 0 := (mul_eq_zero.mp h_lin).resolve_right hsqrt_ne
      exact_mod_cast (by linarith : (s_n n : ℝ) = 2 * (u : ℝ) * (v : ℝ))
    let z : R := ⟨(u : ℤ), (v : ℤ)⟩
    refine ⟨z, ?_⟩
    have hz_conj : z * ⟨(u : ℤ), -(v : ℤ)⟩ = (m : R) := by
      ext
      · simp only [z, zsqrtd_mul_re', zsqrtd_natCast_re]
        have : (m : ℤ) = (u : ℤ) ^ 2 + (q_n n : ℤ) * (v : ℤ) ^ 2 := by exact_mod_cast hm_eq
        linarith
      · simp only [z, zsqrtd_mul_im', zsqrtd_natCast_im]; ring
    have hz_sq : z ^ 2 = ⟨1, (s_n n : ℤ)⟩ := by
      ext
      · simp only [z, sq, zsqrtd_mul_re']
        have : (u : ℤ) ^ 2 - (q_n n : ℤ) * (v : ℤ) ^ 2 = 1 := by exact_mod_cast (by linarith : (u ^ 2 : ℕ) = q_n n * v ^ 2 + 1)
        linarith
      · simp only [z, sq, zsqrtd_mul_im']
        have : (s_n n : ℤ) = 2 * (u : ℤ) * (v : ℤ) := by exact_mod_cast hs_eq
        linarith
    apply le_antisymm
    · rw [Ideal.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · rw [← hz_conj]
        exact Ideal.mem_span_singleton.mpr ⟨⟨(u : ℤ), -(v : ℤ)⟩, rfl⟩
      · rw [← hz_sq, sq]
        exact Ideal.mem_span_singleton.mpr ⟨z, rfl⟩
    · rw [Ideal.span_singleton_le_iff_mem]
      have hcop_2u_m : IsCoprime (2 * (u : ℤ)) (m : ℤ) := by
        have h2u2 : 2 * (u : ℤ) ^ 2 - (m : ℤ) = 1 := by
          have : 2 * u ^ 2 = m + 1 := by omega
          exact_mod_cast (by omega : (2 * (u : ℤ) ^ 2) - (m : ℤ) = 1)
        refine ⟨(u : ℤ), -1, ?_⟩
        linarith
      obtain ⟨c₁, c₂, hc⟩ := hcop_2u_m
      have h1_eq : (1 : R) = (c₁ : R) * (z + ⟨(u : ℤ), -(v : ℤ)⟩) + (c₂ : R) * (m : R) := by
        have h2u : z + ⟨(u : ℤ), -(v : ℤ)⟩ = ((2 * (u : ℤ) : ℤ) : R) := by
          ext <;> simp [z]; ring
        rw [h2u]
        ext <;> simp [hc]
      have hz_eq : z = (c₁ : R) * (z ^ 2 + (m : R)) + (c₂ : R) * (z * (m : R)) := by
        calc z = z * 1 := (mul_one z).symm
          _ = z * ((c₁ : R) * (z + ⟨(u : ℤ), -(v : ℤ)⟩) + (c₂ : R) * (m : R)) := by rw [← h1_eq]
          _ = (c₁ : R) * (z ^ 2 + z * ⟨(u : ℤ), -(v : ℤ)⟩) + (c₂ : R) * (z * (m : R)) := by ring
          _ = (c₁ : R) * (z ^ 2 + (m : R)) + (c₂ : R) * (z * (m : R)) := by rw [hz_conj]
      rw [hz_eq, hz_sq]
      have hm_in : (m : R) ∈ Ideal.span {(m : R), ⟨1, (s_n n : ℤ)⟩} :=
        Ideal.subset_span (Set.mem_insert _ _)
      have hα_in : (⟨1, (s_n n : ℤ)⟩ : R) ∈ Ideal.span {(m : R), ⟨1, (s_n n : ℤ)⟩} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.add_mem _ hα_in hm_in))
        (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hm_in))

/-- **Proposition 3.3, part 3 (`k = 1` Picard class identity)**:
In the `k = 1` regime, writing `(m - 1)/2 = δ₁ z₁^2` and `(m + 1)/2 = δ₂ z₂^2` with
`δ₁ δ₂ = q_n` and `2 z₁ z₂ = s_n`, we have
`δ₂ * (1 + s_n √(-q_n)) = (δ₂ z₂ + z₁ √(-q_n))^2` in `ℤ[√(-q_n)]`. -/
theorem k_eq_1_picard_identity {n m δ₁ δ₂ z₁ z₂ : ℕ}
    (h1 : (m : ℤ) - 1 = 2 * (δ₁ : ℤ) * (z₁ : ℤ) ^ 2)
    (h2 : (m : ℤ) + 1 = 2 * (δ₂ : ℤ) * (z₂ : ℤ) ^ 2)
    (hq : δ₁ * δ₂ = q_n n)
    (hs : 2 * z₁ * z₂ = s_n n) :
    ((δ₂ : Zsqrtd (-(q_n n : ℤ))) * ⟨1, (s_n n : ℤ)⟩) =
      (⟨(δ₂ : ℤ) * (z₂ : ℤ), (z₁ : ℤ)⟩ : Zsqrtd (-(q_n n : ℤ))) ^ 2 := by
  ext
  · simp only [zsqrtd_mul_re', zsqrtd_natCast_re, zsqrtd_natCast_im, sq]
    have hq_z : (q_n n : ℤ) = (δ₁ : ℤ) * (δ₂ : ℤ) := by exact_mod_cast hq.symm
    rw [hq_z]
    linarith
  · simp only [zsqrtd_mul_im', zsqrtd_natCast_re, zsqrtd_natCast_im, sq]
    have hs_z : (s_n n : ℤ) = 2 * (z₁ : ℤ) * (z₂ : ℤ) := by exact_mod_cast hs.symm
    rw [hs_z]
    ring

/-- **Proposition 3.3, part 4 (Second-stage ideal in `k = 2` regime)**:
If `(X₁, Y₁)` is the fundamental Pell solution for `q_n` (`n ≥ 3, n ≠ 6`), then
`1 + Y₁ √(-q_n)` is not `± (u + v √(-q_n))^2` for any `u, v : ℤ`. -/
theorem second_stage_nonprincipal_k_eq_2 {n X₁ Y₁ : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁) (u v : ℤ) :
    (⟨u, v⟩ : Zsqrtd (-(q_n n : ℤ))) ^ 2 ≠ ⟨1, (Y₁ : ℤ)⟩ ∧
    -(⟨u, v⟩ : Zsqrtd (-(q_n n : ℤ))) ^ 2 ≠ ⟨1, (Y₁ : ℤ)⟩ := by
  constructor
  · intro h
    have hre : u ^ 2 - (q_n n : ℤ) * v ^ 2 = 1 := by
      have := congrArg Zsqrtd.re h
      simp only [sq, zsqrtd_mul_re'] at this
      linarith
    have him : 2 * u * v = (Y₁ : ℤ) := by
      have := congrArg Zsqrtd.im h
      simp only [sq, zsqrtd_mul_im'] at this
      linarith
    have hv_pos : 0 < v.natAbs := by
      by_contra h0
      have hv0 : v = 0 := Int.natAbs_eq_zero.mp (by omega)
      rw [hv0] at him; simp at him
      have := hfund.2.1
      omega
    have huv_nat : u.natAbs ^ 2 = q_n n * v.natAbs ^ 2 + 1 := by
      zify
      rw [sq_abs, sq_abs]
      linarith
    have hY_le : Y₁ ≤ v.natAbs := hfund.2.2.2 u.natAbs v.natAbs hv_pos huv_nat
    have him_abs : 2 * u.natAbs * v.natAbs = Y₁ := by
      have := congrArg Int.natAbs him
      simpa [Int.natAbs_mul] using this
    have hu_pos : 1 ≤ u.natAbs := by
      by_contra h0
      have hu0 : u.natAbs = 0 := by omega
      rw [hu0] at him_abs; simp at him_abs
      have := hfund.2.1
      omega
    nlinarith
  · intro h
    have hre : -(u ^ 2 - (q_n n : ℤ) * v ^ 2) = 1 := by
      have := congrArg Zsqrtd.re h
      simp only [sq, zsqrtd_neg_re, zsqrtd_mul_re'] at this
      linarith
    obtain ⟨p, hp, hpq, hmod⟩ := q_n_has_prime_mod4 hn hn6
    exact neg_pell_no_int_sol hp hpq hmod u v (by linarith)

end GrasGreenbergBrocard
