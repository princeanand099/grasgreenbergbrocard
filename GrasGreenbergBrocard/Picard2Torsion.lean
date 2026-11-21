import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.PellFundamental

/-!
# Proposition 3.3: Imaginary Quadratic Picard 2-Torsion Dichotomy (Defect D5 Resolved)

Formalizes Section 3.3 (Proposition 3.3, eq. 3.8) of the manuscript completely without
external axioms, lifted directly into Mathlib's `ClassGroup (Zsqrtd (-(q_n n : ℤ)))` and
Picard group `CommRing.Pic (Zsqrtd (-(q_n n : ℤ)))` (via `ClassGroup.equivPic`):
- `zsqrtd_neg_isDomain`: `IsDomain (Zsqrtd (-D))` for every `D ≥ 1`
- `J_n_sq_eq`: in `O_n^- = ℤ[√(-q_n)]`, `(m, 1 + s_n √(-q_n))^2 = (1 + s_n √(-q_n))`
- `J_n_mul_conj_eq`: `𝔍_n * 𝔍_n̄ = (m)`, establishing invertibility of `𝔍_n` as a fractional ideal
- `J_n_class`, `J_n_pic`: genuine elements `[𝔍_n] ∈ ClassGroup O_n^-` and `CommRing.Pic O_n^-`
- `J_n_pic_sq_eq_one`: `[𝔍_n]^2 = 1` in `ClassGroup O_n^-` and `Pic(O_n^-)`
- `J_n_pic_eq_one_iff_k_eq_2`: `[𝔍_n] = 1 ⟺ k = 2` in `CommRing.Pic O_n^-`
- `k_eq_1_picard_class_eq`: in the `k = 1` regime, `[𝔍_n] = [(δ₂, √(-q_n))]` in `Pic(O_n^-)`
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

/-- For every `D ≥ 1`, `ℤ[√(-D)]` is an integral domain (`IsDomain`), proved directly from
multiplicativity and positive-definiteness of `Zsqrtd.norm`. -/
lemma zsqrtd_neg_isDomain {D : ℕ} (hD : 1 ≤ D) : IsDomain (Zsqrtd (-(D : ℤ))) := by
  have hnt : Nontrivial (Zsqrtd (-(D : ℤ))) := ⟨⟨0, 1, by intro h; have := congrArg Zsqrtd.re h; simp at this⟩⟩
  have hnzd : NoZeroDivisors (Zsqrtd (-(D : ℤ))) := by
    refine ⟨fun {a b} hab => ?_⟩
    have hnorm : Zsqrtd.norm a * Zsqrtd.norm b = 0 := by
      rw [← Zsqrtd.norm_mul, hab, Zsqrtd.norm_zero]
    have hzero : ∀ z : Zsqrtd (-(D : ℤ)), Zsqrtd.norm z = 0 → z = 0 := by
      intro z hz
      have h1 : z.re ^ 2 + (D : ℤ) * z.im ^ 2 = 0 := by
        have : Zsqrtd.norm z = z.re * z.re - (-(D : ℤ)) * (z.im * z.im) := rfl
        rw [this] at hz; linarith
      have hD_pos : (0 : ℤ) < (D : ℤ) := by exact_mod_cast hD
      have hre0 : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
      have him0 : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
      ext <;> simp [hre0, him0]
    rcases mul_eq_zero.mp hnorm with ha | hb
    · exact Or.inl (hzero a ha)
    · exact Or.inr (hzero b hb)
  exact NoZeroDivisors.to_isDomain _

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
  have hnorm : (a ^ 2 + (D : ℤ) * b ^ 2) *
      ((w' : Zsqrtd (-(D : ℤ))).re ^ 2 + (D : ℤ) * (w' : Zsqrtd (-(D : ℤ))).im ^ 2) = 1 := by
    have h1 := congrArg Zsqrtd.norm hmul
    rw [Zsqrtd.norm_mul] at h1
    simp only [Zsqrtd.norm, Zsqrtd.one_re, Zsqrtd.one_im] at h1
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
  apply le_antisymm
  · rw [sq, Ideal.span_mul_span]
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_mul, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rw [← sq, ← hαβ]
      exact Ideal.mem_span_singleton.mpr ⟨β, rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨(m : R), mul_comm _ _⟩
    · exact Ideal.mem_span_singleton.mpr ⟨(m : R), rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨α, rfl⟩
  · rw [Ideal.span_singleton_le_iff_mem]
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

/-- **Invertibility of `𝔍_n` in `O_n^-`**:
`𝔍_n * 𝔍_n̄ = (m)` in `ℤ[√(-q_n)]`, proving `𝔍_n` is an invertible ideal (hence defines a
canonical class in `ClassGroup O_n^-` and `CommRing.Pic O_n^-`). -/
theorem J_n_mul_conj_eq {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    Ideal.span {(m : Zsqrtd (-(q_n n : ℤ))), ⟨1, (s_n n : ℤ)⟩} *
      Ideal.span {(m : Zsqrtd (-(q_n n : ℤ))), ⟨1, -(s_n n : ℤ)⟩} =
      Ideal.span {(m : Zsqrtd (-(q_n n : ℤ)))} := by
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
  have hsum_2 : α + β = (2 : R) := by ext <;> simp [α, β]
  have hm_odd : m % 2 = 1 := m_odd_of_brocard hn hm
  have hcop_int : (2 : ℤ) ∣ 1 - (m : ℤ) ^ 2 := by
    have : (m : ℤ) % 2 = 1 := by exact_mod_cast hm_odd
    omega
  obtain ⟨t, ht⟩ := hcop_int
  apply le_antisymm
  · rw [Ideal.span_mul_span]
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_mul, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Ideal.mem_span_singleton.mpr ⟨(m : R), rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨β, rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨α, mul_comm _ _⟩
    · rw [hαβ, sq]; exact Ideal.mem_span_singleton.mpr ⟨(m : R), rfl⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have h1 : (1 : R) = (t : R) * (α + β) + α * β := by
      rw [hsum_2, hαβ]
      have : (1 : ℤ) = t * 2 + (m : ℤ) ^ 2 := by linarith
      ext <;> simp [this]
    have hm_eq : (m : R) = (t : R) * (α * (m : R)) + (t : R) * ((m : R) * β) + (m : R) * (α * β) := by
      calc (m : R) = (m : R) * 1 := (mul_one _).symm
        _ = (m : R) * ((t : R) * (α + β) + α * β) := by rw [← h1]
        _ = (t : R) * (α * (m : R)) + (t : R) * ((m : R) * β) + (m : R) * (α * β) := by ring
    rw [hm_eq]
    have hm_J : (m : R) ∈ Ideal.span {(m : R), α} := Ideal.subset_span (Set.mem_insert _ _)
    have hα_J : α ∈ Ideal.span {(m : R), α} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hm_Jb : (m : R) ∈ Ideal.span {(m : R), β} := Ideal.subset_span (Set.mem_insert _ _)
    have hβ_Jb : β ∈ Ideal.span {(m : R), β} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    exact Ideal.add_mem _
      (Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hα_J hm_Jb))
        (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hm_J hβ_Jb)))
      (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hα_J hβ_Jb))

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
            exact_mod_cast (by linarith : m ^ 2 = q_n n * (s_n n) ^ 2 + 1)
          nlinarith
        have hm_nn : 0 ≤ (m : ℝ) := by positivity
        have hr_nn : 0 ≤ (z.re.natAbs : ℝ) ^ 2 + (q_n n : ℝ) * (z.im.natAbs : ℝ) ^ 2 := by positivity
        nlinarith [sq_nonneg ((m : ℝ) - ((z.re.natAbs : ℝ) ^ 2 + (q_n n : ℝ) * (z.im.natAbs : ℝ) ^ 2))]
      calc (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)
          = ((z.re.natAbs : ℝ) ^ 2 + (q_n n : ℝ) * (z.im.natAbs : ℝ) ^ 2) +
              (2 * (z.re.natAbs : ℝ) * (z.im.natAbs : ℝ)) * Real.sqrt (q_n n : ℝ) := by
            have hs_r : (s_n n : ℝ) = 2 * (z.re : ℝ) * (z.im : ℝ) := by exact_mod_cast him.symm
            rw [hu2_v2, hs_r, show 2 * (z.re : ℝ) * (z.im : ℝ) = 2 * ((z.re : ℝ) * (z.im : ℝ)) by ring, ← hsign]; ring
        _ = ((z.re.natAbs : ℝ) + (z.im.natAbs : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2 := by
            ring_nf; rw [hsq_q]; ring
  · rintro ⟨u, v, _, _, huv, hms⟩
    have hsqrt_irr : Irrational (Real.sqrt (q_n n : ℝ)) := by
      rw [irrational_iff_ne_rational]
      intro a b hb hab
      have hb0 : b ≠ 0 := hb
      have hrat : (a : ℤ) ^ 2 = (q_n n : ℤ) * (b : ℤ) ^ 2 := by
        have h1 : ((a : ℝ) / (b : ℝ)) ^ 2 = (q_n n : ℝ) := by
          rw [← hab, Real.sq_sqrt (by positivity)]
        have hb_r : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
        have h2 : (a : ℝ) ^ 2 = (q_n n : ℝ) * (b : ℝ) ^ 2 := by
          field_simp [hb_r] at h1; linarith
        exact_mod_cast h2
      obtain ⟨p, hp, hpq, _⟩ := q_n_has_prime_mod4 (by omega) hn6
      haveI : Fact p.Prime := ⟨hp⟩
      have hsqf : ¬ p ^ 2 ∣ q_n n := by simpa [sq] using (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp
      have ha_ne : a.natAbs ≠ 0 := by
        intro h0
        have ha0 : a = 0 := Int.natAbs_eq_zero.mp h0
        rw [ha0] at hrat; simp at hrat
        rcases hrat with hq0 | hb_eq0
        · exact absurd hq_ge2 (by omega)
        · exact hb0 (by exact_mod_cast hb_eq0)
      have hnat : a.natAbs ^ 2 = q_n n * b.natAbs ^ 2 := by
        have := congrArg Int.natAbs hrat
        simpa [Int.natAbs_mul, Int.natAbs_pow] using this
      have hv_lhs : padicValNat p (a.natAbs ^ 2) = 2 * padicValNat p a.natAbs := by
        rw [sq, padicValNat.mul ha_ne ha_ne]; ring
      have hv_q : padicValNat p (q_n n) = 1 := by
        have hq_ne : q_n n ≠ 0 := by omega
        have h1 : 1 ≤ padicValNat p (q_n n) := (padicValNat_dvd_iff_le hq_ne).mp (by simpa using hpq)
        have h2 : ¬ 2 ≤ padicValNat p (q_n n) := by
          intro hle; exact hsqf ((padicValNat_dvd_iff_le hq_ne).mpr hle)
        omega
      have hv_rhs : padicValNat p (q_n n * b.natAbs ^ 2) = 1 + 2 * padicValNat p b.natAbs := by
        have hb_nat_ne : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb0
        have hvb : padicValNat p (b.natAbs ^ 2) = 2 * padicValNat p b.natAbs := by
          rw [sq, padicValNat.mul hb_nat_ne hb_nat_ne]; ring
        rw [padicValNat.mul (by omega) (pow_ne_zero 2 hb_nat_ne), hv_q, hvb]
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
            ((((m : ℤ) - ((u : ℤ) ^ 2 + (q_n n : ℤ) * (v : ℤ) ^ 2) : ℤ) : ℚ) /
              (((2 * (u : ℤ) * (v : ℤ) - (s_n n : ℤ) : ℤ) : ℚ)) : ℝ) := by
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
      · dsimp only [z]
        rw [zsqrtd_mul_re', zsqrtd_natCast_re]
        have : (m : ℤ) = (u : ℤ) ^ 2 + (q_n n : ℤ) * (v : ℤ) ^ 2 := by exact_mod_cast hm_eq
        linarith
      · dsimp only [z]
        rw [zsqrtd_mul_im', zsqrtd_natCast_im]
        ring
    have hz_sq : z ^ 2 = ⟨1, (s_n n : ℤ)⟩ := by
      ext
      · dsimp only [z]
        rw [sq, zsqrtd_mul_re']
        have h1 : (u : ℤ) ^ 2 = (q_n n : ℤ) * (v : ℤ) ^ 2 + 1 := by exact_mod_cast huv
        linarith
      · dsimp only [z]
        rw [sq, zsqrtd_mul_im']
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
        have h2u2_nat : 2 * u ^ 2 = m + 1 := by nlinarith [hm_eq, huv]
        have h2u2 : 2 * (u : ℤ) ^ 2 - (m : ℤ) = 1 := by
          have h1 : (2 : ℤ) * (u : ℤ) ^ 2 = (m : ℤ) + 1 := by exact_mod_cast h2u2_nat
          linarith
        refine ⟨(u : ℤ), -1, ?_⟩
        linarith
      obtain ⟨c₁, c₂, hc⟩ := hcop_2u_m
      have h1_eq : (1 : R) = (c₁ : R) * (z + ⟨(u : ℤ), -(v : ℤ)⟩) + (c₂ : R) * (m : R) := by
        have h2u : z + ⟨(u : ℤ), -(v : ℤ)⟩ = ((2 * (u : ℤ) : ℤ) : R) := by
          ext <;> simp [z] <;> ring
        rw [h2u]
        ext <;> simp [hc] <;> ring
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
    have hsub : (δ₂ : ℤ) * (z₂ : ℤ) ^ 2 - (δ₁ : ℤ) * (z₁ : ℤ) ^ 2 = 1 := by linarith
    rw [hq_z]
    nlinarith
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

/-!
### Lifting Proposition 3.3 into `ClassGroup (O_n^-)` and `CommRing.Pic (O_n^-)` (Defect D5)
-/

noncomputable section PicardLift

/-- Generic helper: given integral ideals `I, J` of a domain `R` with `I * J = Ideal.span {d}`
and `d ≠ 0`, `I` defines a unit in `FractionalIdeal (nonZeroDivisors R) (FractionRing R)`. -/
def invertibleIdealToFracUnit {R : Type*} [CommRing R] [IsDomain R]
    (I J : Ideal R) (d : R) (hd : d ≠ 0) (hIJ : I * J = Ideal.span {d}) :
    (FractionalIdeal (nonZeroDivisors R) (FractionRing R))ˣ :=
  let K := FractionRing R
  let S := nonZeroDivisors R
  let fI : FractionalIdeal S K := (I : FractionalIdeal S K)
  let fJ : FractionalIdeal S K := (J : FractionalIdeal S K)
  let fd : FractionalIdeal S K := FractionalIdeal.spanSingleton S (algebraMap R K d)
  let fd_inv : FractionalIdeal S K := FractionalIdeal.spanSingleton S (algebraMap R K d)⁻¹
  have hdK : algebraMap R K d ≠ 0 := by
    intro h0; exact hd (IsFractionRing.injective R K (by simpa using h0))
  have hmul : fI * (fJ * fd_inv) = 1 := by
    rw [← mul_assoc]
    have hIJ_f : fI * fJ = fd := by
      change (I : FractionalIdeal S K) * (J : FractionalIdeal S K) = _
      rw [← FractionalIdeal.coeIdeal_mul, hIJ, FractionalIdeal.coeIdeal_span_singleton]
    rw [hIJ_f]
    exact FractionalIdeal.spanSingleton_mul_spanSingleton_inv S hdK
  { val := fI
    inv := fJ * fd_inv
    val_inv := hmul
    inv_val := by rw [mul_comm]; exact hmul }

/-- An integral ideal unit `u` (with `u.val = (I : FractionalIdeal S K)`) has trivial class in
`ClassGroup R` if and only if `I` is a principal ideal of `R`. -/
lemma classGroup_mk_coeIdeal_eq_one_iff {R : Type*} [CommRing R] [IsDomain R]
    (I J : Ideal R) (d : R) (hd : d ≠ 0) (hIJ : I * J = Ideal.span {d}) :
    ClassGroup.mk (invertibleIdealToFracUnit I J d hd hIJ) = 1 ↔ ∃ z : R, I = Ideal.span {z} := by
  let K := FractionRing R
  let S := nonZeroDivisors R
  rw [ClassGroup.mk_eq_one_iff]
  constructor
  · rintro ⟨x, hx⟩
    have hx_mem : x ∈ (I : FractionalIdeal S K) := by
      change x ∈ (invertibleIdealToFracUnit I J d hd hIJ : FractionalIdeal S K)
      rw [← hx]
      exact FractionalIdeal.mem_spanSingleton_self S x
    rcases (FractionalIdeal.mem_coeIdeal S).mp hx_mem with ⟨z, hzI, hzx⟩
    refine ⟨z, le_antisymm ?_ (Ideal.span_singleton_le_iff_mem.mpr hzI)⟩
    intro r hr
    have hr_mem : algebraMap R K r ∈ FractionalIdeal.spanSingleton S x := by
      rw [hx]; exact FractionalIdeal.mem_coeIdeal.mpr ⟨r, hr, rfl⟩
    rcases FractionalIdeal.mem_spanSingleton.mp hr_mem with ⟨c, hc⟩
    rw [← hzx, Algebra.smul_def, ← map_mul] at hc
    have hrz : c * z = r := IsFractionRing.injective R K hc
    exact Ideal.mem_span_singleton.mpr ⟨c, by rw [mul_comm, hrz]⟩
  · rintro ⟨z, hz⟩
    refine ⟨algebraMap R K z, ?_⟩
    change FractionalIdeal.spanSingleton S (algebraMap R K z) = (I : FractionalIdeal S K)
    rw [hz, FractionalIdeal.coeIdeal_span_singleton]

/-- Helper: `1 ≤ q_n n` for all `n`. -/
lemma one_le_q_n (n : ℕ) : 1 ≤ q_n n := by
  unfold q_n
  exact Nat.succ_le_of_lt (Finset.prod_pos (fun q hq => (Finset.mem_filter.mp hq).2.1.pos))

/-- The genuine ideal class `[𝔍_n] ∈ ClassGroup (ℤ[√(-q_n)])` of `𝔍_n = (m, 1 + s_n √(-q_n))`. -/
def J_n_class {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    letI : IsDomain (Zsqrtd (-(q_n n : ℤ))) := zsqrtd_neg_isDomain (one_le_q_n n)
    ClassGroup (Zsqrtd (-(q_n n : ℤ))) :=
  letI : IsDomain (Zsqrtd (-(q_n n : ℤ))) := zsqrtd_neg_isDomain (one_le_q_n n)
  have hm_ne : (m : Zsqrtd (-(q_n n : ℤ))) ≠ 0 := by
    intro h0
    have hm0 : m = 0 := by
      have := congrArg Zsqrtd.re h0; simp at this; exact this
    rw [hm0] at hm; simp at hm
  ClassGroup.mk (invertibleIdealToFracUnit
    (Ideal.span {(m : Zsqrtd (-(q_n n : ℤ))), ⟨1, (s_n n : ℤ)⟩})
    (Ideal.span {(m : Zsqrtd (-(q_n n : ℤ))), ⟨1, -(s_n n : ℤ)⟩})
    (m : Zsqrtd (-(q_n n : ℤ))) hm_ne (J_n_mul_conj_eq hn hm))

/-- The genuine Picard class `[𝔍_n] ∈ CommRing.Pic (ℤ[√(-q_n)])` via `ClassGroup.equivPic`. -/
def J_n_pic {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    CommRing.Pic (Zsqrtd (-(q_n n : ℤ))) :=
  letI : IsDomain (Zsqrtd (-(q_n n : ℤ))) := zsqrtd_neg_isDomain (one_le_q_n n)
  ClassGroup.equivPic (Zsqrtd (-(q_n n : ℤ))) (J_n_class hn hm)

/-- **Proposition 3.3 (Picard 2-Torsion)**: `[𝔍_n]^2 = 1` in `ClassGroup (ℤ[√(-q_n)])`
and in `CommRing.Pic (ℤ[√(-q_n)])`. -/
theorem J_n_pic_sq_eq_one {n m : ℕ} (hn : 4 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    letI : IsDomain (Zsqrtd (-(q_n n : ℤ))) := zsqrtd_neg_isDomain (one_le_q_n n)
    (J_n_class hn hm) ^ 2 = 1 ∧ (J_n_pic hn hm) ^ 2 = 1 := by
  letI : IsDomain (Zsqrtd (-(q_n n : ℤ))) := zsqrtd_neg_isDomain (one_le_q_n n)
  set R := Zsqrtd (-(q_n n : ℤ))
  have hcls : (J_n_class hn hm) ^ 2 = 1 := by
    unfold J_n_class
    rw [← map_pow, ClassGroup.mk_eq_one_iff]
    refine ⟨algebraMap R (FractionRing R) ⟨1, (s_n n : ℤ)⟩, ?_⟩
    rw [Units.val_pow_eq_pow_val]
    change FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R (FractionRing R) ⟨1, (s_n n : ℤ)⟩) =
      ((Ideal.span {(m : R), ⟨1, (s_n n : ℤ)⟩} : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) ^ 2)
    rw [← FractionalIdeal.coeIdeal_pow, J_n_sq_eq hn hm, FractionalIdeal.coeIdeal_span_singleton]
  refine ⟨hcls, ?_⟩
  unfold J_n_pic
  rw [← map_pow, hcls, map_one]

/-- **Proposition 3.3 (Picard Triviality Dichotomy, eq. 3.8)**:
`[𝔍_n] = 1` in `CommRing.Pic (ℤ[√(-q_n)])` if and only if `k = 2`. -/
theorem J_n_pic_eq_one_iff_k_eq_2 {n m : ℕ} (hn : 4 ≤ n) (hn6 : n ≠ 6)
    (hm : Nat.factorial n + 1 = m ^ 2) :
    (J_n_pic hn hm = 1) ↔
      (∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u ^ 2 = q_n n * v ^ 2 + 1 ∧
        (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = ((u : ℝ) + (v : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2) := by
  letI : IsDomain (Zsqrtd (-(q_n n : ℤ))) := zsqrtd_neg_isDomain (one_le_q_n n)
  unfold J_n_pic
  rw [MulEquiv.map_eq_one_iff]
  unfold J_n_class
  rw [classGroup_mk_coeIdeal_eq_one_iff]
  exact J_n_principal_iff_k_eq_2 hn hn6 hm

/-- **Proposition 3.3 (`k = 1` Regime in `CommRing.Pic (ℤ[√(-q_n)])`)**:
In the `k = 1` regime, the ramified ideal `I_{δ₂} = (δ₂, √(-q_n))` satisfies `I_{δ₂}^2 = (δ₂)` and
`[𝔍_n] = [I_{δ₂}]` in `CommRing.Pic (ℤ[√(-q_n)])`. -/
theorem k_eq_1_picard_class_eq {n m δ₁ δ₂ z₁ z₂ : ℕ} (hn : 4 ≤ n)
    (hm : Nat.factorial n + 1 = m ^ 2)
    (h1 : (m : ℤ) - 1 = 2 * (δ₁ : ℤ) * (z₁ : ℤ) ^ 2)
    (h2 : (m : ℤ) + 1 = 2 * (δ₂ : ℤ) * (z₂ : ℤ) ^ 2)
    (hq : δ₁ * δ₂ = q_n n)
    (hs : 2 * z₁ * z₂ = s_n n) :
    letI : IsDomain (Zsqrtd (-(q_n n : ℤ))) := zsqrtd_neg_isDomain (one_le_q_n n)
    let R := Zsqrtd (-(q_n n : ℤ))
    let Iδ : Ideal R := Ideal.span {(δ₂ : R), ⟨0, 1⟩}
    Iδ * Iδ = Ideal.span {(δ₂ : R)} ∧
    ∃ (hδ2 : (δ₂ : R) ≠ 0) (hsq : Iδ * Iδ = Ideal.span {(δ₂ : R)}),
      ClassGroup.equivPic R (ClassGroup.mk (invertibleIdealToFracUnit Iδ Iδ (δ₂ : R) hδ2 hsq)) =
        J_n_pic hn hm := by
  letI : IsDomain (Zsqrtd (-(q_n n : ℤ))) := zsqrtd_neg_isDomain (one_le_q_n n)
  set R := Zsqrtd (-(q_n n : ℤ))
  set Iδ : Ideal R := Ideal.span {(δ₂ : R), ⟨0, 1⟩}
  have hq_pos : 0 < q_n n := one_le_q_n n
  have hδ2_pos : 0 < δ₂ := by
    by_contra h0; have : δ₂ = 0 := by omega; rw [this, mul_zero] at hq; omega
  have hδ2_ne : (δ₂ : R) ≠ 0 := by
    intro h0; have := congrArg Zsqrtd.re h0; simp at this; omega
  have hcop_δ : IsCoprime (δ₁ : ℤ) (δ₂ : ℤ) := by
    have hcop_nat : Nat.Coprime δ₁ δ₂ := by
      have hsqf := q_n_squarefree n
      rw [← hq] at hsqf
      exact Nat.coprime_of_mul_squarefree hsqf
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using hcop_nat)
  have hIδ_sq : Iδ * Iδ = Ideal.span {(δ₂ : R)} := by
    apply le_antisymm
    · rw [Ideal.span_mul_span]
      apply Ideal.span_le.mpr
      intro x hx
      simp only [Set.mem_mul, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with ⟨a, ha, b, hb, rfl⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact Ideal.mem_span_singleton.mpr ⟨(δ₂ : R), rfl⟩
      · exact Ideal.mem_span_singleton.mpr ⟨⟨0, 1⟩, rfl⟩
      · exact Ideal.mem_span_singleton.mpr ⟨⟨0, 1⟩, mul_comm _ _⟩
      · refine Ideal.mem_span_singleton.mpr ⟨-(δ₁ : R), ?_⟩
        ext
        · change 0 * 0 + (-(q_n n : ℤ)) * 1 * 1 = (δ₂ : ℤ) * (-(δ₁ : ℤ)) + (-(q_n n : ℤ)) * 0 * 0
          have : (q_n n : ℤ) = (δ₁ : ℤ) * (δ₂ : ℤ) := by exact_mod_cast hq.symm
          linarith
        · change 0 * 1 + 1 * 0 = (δ₂ : ℤ) * 0 + 0 * (-(δ₁ : ℤ)); ring
    · rw [Ideal.span_singleton_le_iff_mem]
      obtain ⟨c₁, c₂, hc⟩ := hcop_δ
      have hδ2_eq : (δ₂ : R) = (c₂ : R) * ((δ₂ : R) * (δ₂ : R)) - (c₁ : R) * ((⟨0, 1⟩ : R) * ⟨0, 1⟩) := by
        ext
        · change (δ₂ : ℤ) = c₂ * ((δ₂ : ℤ) * (δ₂ : ℤ)) - c₁ * (-(q_n n : ℤ))
          have hqz : (q_n n : ℤ) = (δ₁ : ℤ) * (δ₂ : ℤ) := by exact_mod_cast hq.symm
          rw [hqz]; linear_combination (δ₂ : ℤ) * hc.symm
        · simp
      rw [hδ2_eq]
      have h1_in : (δ₂ : R) ∈ Iδ := Ideal.subset_span (Set.mem_insert _ _)
      have h2_in : (⟨0, 1⟩ : R) ∈ Iδ := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      exact Ideal.sub_mem _
        (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul h1_in h1_in))
        (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul h2_in h2_in))
  refine ⟨hIδ_sq, hδ2_ne, hIδ_sq, ?_⟩
  unfold J_n_pic
  congr 1
  set uδ := invertibleIdealToFracUnit Iδ Iδ (δ₂ : R) hδ2_ne hIδ_sq
  have hm_ne : (m : R) ≠ 0 := by
    intro h0; have := congrArg Zsqrtd.re h0; simp at this; rw [this] at hm; simp at hm
  set uJ := invertibleIdealToFracUnit
    (Ideal.span {(m : R), ⟨1, (s_n n : ℤ)⟩})
    (Ideal.span {(m : R), ⟨1, -(s_n n : ℤ)⟩}) (m : R) hm_ne (J_n_mul_conj_eq hn hm)
  have huδ_sq : ClassGroup.mk uδ ^ 2 = 1 := by
    rw [← map_pow, ClassGroup.mk_eq_one_iff]
    refine ⟨algebraMap R (FractionRing R) (δ₂ : R), ?_⟩
    rw [Units.val_pow_eq_pow_val]
    change FractionalIdeal.spanSingleton _ _ = ((Iδ : FractionalIdeal _ _) ^ 2)
    rw [← FractionalIdeal.coeIdeal_pow, sq, hIδ_sq, FractionalIdeal.coeIdeal_span_singleton]
  set w : R := ⟨(δ₂ : ℤ) * (z₂ : ℤ), (z₁ : ℤ)⟩
  have hw_sq : w ^ 2 = (δ₂ : R) * ⟨1, (s_n n : ℤ)⟩ := (k_eq_1_picard_identity h1 h2 hq hs).symm
  have hw_conj : w * ⟨(δ₂ : ℤ) * (z₂ : ℤ), -(z₁ : ℤ)⟩ = (δ₂ : R) * (m : R) := by
    ext
    · simp only [w, zsqrtd_mul_re', zsqrtd_natCast_re, zsqrtd_natCast_im]
      have hqz : (q_n n : ℤ) = (δ₁ : ℤ) * (δ₂ : ℤ) := by exact_mod_cast hq.symm
      rw [hqz]; nlinarith
    · simp only [w, zsqrtd_mul_im', zsqrtd_natCast_re, zsqrtd_natCast_im]; ring
  have hprod_eq : Iδ * Ideal.span {(m : R), ⟨1, (s_n n : ℤ)⟩} = Ideal.span {w} := by
    apply le_antisymm
    · rw [Ideal.span_mul_span]
      apply Ideal.span_le.mpr
      intro x hx
      simp only [Set.mem_mul, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with ⟨a, ha, b, hb, rfl⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rw [← hw_conj]; exact Ideal.mem_span_singleton.mpr ⟨⟨(δ₂ : ℤ) * (z₂ : ℤ), -(z₁ : ℤ)⟩, rfl⟩
      · rw [← hw_sq, sq]; exact Ideal.mem_span_singleton.mpr ⟨w, rfl⟩
      · refine Ideal.mem_span_singleton.mpr ⟨⟨-(z₁ : ℤ) * (δ₁ : ℤ), (z₂ : ℤ)⟩, ?_⟩
        ext
        · simp only [w, zsqrtd_mul_re', zsqrtd_natCast_re, zsqrtd_natCast_im]
          have hqz : (q_n n : ℤ) = (δ₁ : ℤ) * (δ₂ : ℤ) := by exact_mod_cast hq.symm
          rw [hqz]; ring
        · simp only [w, zsqrtd_mul_im', zsqrtd_natCast_re, zsqrtd_natCast_im]
          nlinarith
      · refine Ideal.mem_span_singleton.mpr ⟨⟨-(δ₁ : ℤ) * (z₁ : ℤ), (z₂ : ℤ)⟩, ?_⟩
        ext
        · simp only [w, zsqrtd_mul_re', zsqrtd_natCast_re, zsqrtd_natCast_im]
          have hqz : (q_n n : ℤ) = (δ₁ : ℤ) * (δ₂ : ℤ) := by exact_mod_cast hq.symm
          have hsz : (s_n n : ℤ) = 2 * (z₁ : ℤ) * (z₂ : ℤ) := by exact_mod_cast hs.symm
          rw [hqz, hsz]; ring
        · simp only [w, zsqrtd_mul_im', zsqrtd_natCast_re, zsqrtd_natCast_im]
          nlinarith
    · rw [Ideal.span_singleton_le_iff_mem]
      have hcop_w : IsCoprime (2 * (δ₂ : ℤ) * (z₂ : ℤ)) (m : ℤ) := by
        refine ⟨(z₂ : ℤ), -1, ?_⟩; linarith
      obtain ⟨c₁, c₂, hc⟩ := hcop_w
      have h1_eq : (1 : R) = (c₁ : R) * (w + ⟨(δ₂ : ℤ) * (z₂ : ℤ), -(z₁ : ℤ)⟩) + (c₂ : R) * (m : R) := by
        have hsum : w + ⟨(δ₂ : ℤ) * (z₂ : ℤ), -(z₁ : ℤ)⟩ = ((2 * (δ₂ : ℤ) * (z₂ : ℤ) : ℤ) : R) := by
          ext <;> simp [w] <;> ring
        rw [hsum]; ext <;> simp [hc] <;> ring
      have hw_eq : w = (c₁ : R) * (w ^ 2 + (δ₂ : R) * (m : R)) + (c₂ : R) * (w * (m : R)) := by
        calc w = w * 1 := (mul_one w).symm
          _ = w * ((c₁ : R) * (w + ⟨(δ₂ : ℤ) * (z₂ : ℤ), -(z₁ : ℤ)⟩) + (c₂ : R) * (m : R)) := by rw [← h1_eq]
          _ = (c₁ : R) * (w ^ 2 + w * ⟨(δ₂ : ℤ) * (z₂ : ℤ), -(z₁ : ℤ)⟩) + (c₂ : R) * (w * (m : R)) := by ring
          _ = (c₁ : R) * (w ^ 2 + (δ₂ : R) * (m : R)) + (c₂ : R) * (w * (m : R)) := by rw [hw_conj]
      rw [hw_eq, hw_sq]
      have hδ_in : (δ₂ : R) ∈ Iδ := Ideal.subset_span (Set.mem_insert _ _)
      have hsq_in : (⟨0, 1⟩ : R) ∈ Iδ := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have hm_in : (m : R) ∈ Ideal.span {(m : R), ⟨1, (s_n n : ℤ)⟩} := Ideal.subset_span (Set.mem_insert _ _)
      have hα_in : (⟨1, (s_n n : ℤ)⟩ : R) ∈ Ideal.span {(m : R), ⟨1, (s_n n : ℤ)⟩} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have hw_in_Iδ : w ∈ Iδ := by
        have : w = (z₂ : R) * (δ₂ : R) + (z₁ : R) * ⟨0, 1⟩ := by ext <;> simp [w] <;> ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hδ_in) (Ideal.mul_mem_left _ _ hsq_in)
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.mul_mem_mul hδ_in hα_in) (Ideal.mul_mem_mul hδ_in hm_in)))
        (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hw_in_Iδ hm_in))
  have hprod_one : ClassGroup.mk uδ * ClassGroup.mk uJ = 1 := by
    rw [← map_mul, ClassGroup.mk_eq_one_iff]
    refine ⟨algebraMap R (FractionRing R) w, ?_⟩
    rw [Units.val_mul]
    change FractionalIdeal.spanSingleton _ _ = (Iδ : FractionalIdeal _ _) * _
    rw [← FractionalIdeal.coeIdeal_mul, hprod_eq, FractionalIdeal.coeIdeal_span_singleton]
  have huδ_eq : ClassGroup.mk uδ = (ClassGroup.mk uδ)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← sq]; exact huδ_sq
  have hJ_eq : ClassGroup.mk uJ = (ClassGroup.mk uδ)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, mul_comm]; exact hprod_one
  change ClassGroup.mk uδ = ClassGroup.mk uJ
  rw [huδ_eq, hJ_eq]

end PicardLift

end GrasGreenbergBrocard
