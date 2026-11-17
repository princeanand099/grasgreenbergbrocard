import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.ExternalAxiomsSec3
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.ChebyshevLucas

/-!
# Lemma 3.1: Fundamental Unit Norm and Growth of `q_n`, `s_n`

Formalizes Section 3.1 (Lemma 3.1(i)–(ii)) of the manuscript:
- `IsFundamentalPell`: fundamental positive solution `(X₁, Y₁)` to `x^2 - D y^2 = 1`
- `q_n_has_prime_mod4`: for `n ≥ 3` with `n ≠ 6`, `q_n` has a prime divisor `p ≡ 3 [MOD 4]`
- `neg_pell_no_int_sol`, `neg_pell_no_rat_sol`: `x^2 - q_n y^2 = -1` has no integer or rational solutions
- `log_q_n_gt_point4`: `log q_n > 0.4 * n` for `n ≥ 116`
- `log_fund_pell_gt_point2`: `log ε_n > 0.2 * n` when `log q_n > 0.4 * n`
- `pell_index_upper_bound`: `1 ≤ k < 2.5 * log n < n / 5` for `n ≥ 116`
- `log_s_n_sqrt_q_n_asymptotic`, `log_s_n_asymptotic`: Lemma 3.1(ii) asymptotics
-/

noncomputable section

open Real Finset BigOperators Asymptotics Filter

namespace GrasGreenbergBrocard

/-- `(X₁, Y₁)` is the fundamental positive solution to `x^2 - D * y^2 = 1`. -/
def IsFundamentalPell (D X₁ Y₁ : ℕ) : Prop :=
  0 < X₁ ∧ 0 < Y₁ ∧ X₁ ^ 2 = D * Y₁ ^ 2 + 1 ∧
    ∀ x y : ℕ, 0 < y → x ^ 2 = D * y ^ 2 + 1 → Y₁ ≤ y

/-- Fundamental Pell value `ε_D = X₁ + Y₁ √D`. -/
def pellUnit (D X₁ Y₁ : ℕ) : ℝ :=
  (X₁ : ℝ) + (Y₁ : ℝ) * Real.sqrt (D : ℝ)

lemma pellUnit_gt_two_sqrt {D X₁ Y₁ : ℕ} (hD : 1 ≤ D) (hfund : IsFundamentalPell D X₁ Y₁) :
    2 * Real.sqrt (D : ℝ) < pellUnit D X₁ Y₁ := by
  rcases hfund with ⟨_, hY1, hEq, _⟩
  have hD_pos : (0 : ℝ) < (D : ℝ) := by positivity
  have hY1_ge : (1 : ℝ) ≤ (Y₁ : ℝ) := by exact_mod_cast hY1
  have hX1_gt : Real.sqrt (D : ℝ) < (X₁ : ℝ) := by
    have hsq : (D : ℝ) < (X₁ : ℝ) ^ 2 := by
      have h1 : D < X₁ ^ 2 := by
        calc D = D * 1 ^ 2 := by ring
          _ ≤ D * Y₁ ^ 2 := Nat.mul_le_mul_left D (Nat.pow_le_pow_left hY1 2)
          _ < D * Y₁ ^ 2 + 1 := Nat.lt_succ_self _
          _ = X₁ ^ 2 := hEq.symm
      exact_mod_cast h1
    calc Real.sqrt (D : ℝ) < Real.sqrt ((X₁ : ℝ) ^ 2) := Real.sqrt_lt_sqrt (by positivity) hsq
      _ = (X₁ : ℝ) := Real.sqrt_sq (by positivity)
  have hY_sqrt : Real.sqrt (D : ℝ) ≤ (Y₁ : ℝ) * Real.sqrt (D : ℝ) :=
    le_mul_of_one_le_left (Real.sqrt_nonneg _) hY1_ge
  unfold pellUnit
  linarith

/-- For `n/2 < p ≤ n` with `p` prime, `v_p(n!) = 1`, hence `p ∈ Podd n` and `p ∣ q_n n`. -/
lemma prime_in_upper_half_dvd_q_n {n p : ℕ} (hp : p.Prime) (hlo : n / 2 < p) (hhi : p ≤ n) :
    p ∈ Podd n ∧ p ∣ q_n n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hv : padicValNat p (Nat.factorial n) = 1 := by
    have h_eq : padicValNat p (Nat.factorial n) = n / p := by
      apply padicValNat_factorial_eq_div_of_lt_sq hp
      have hp2 : 2 ≤ p := hp.two_le
      have hlt : n < 2 * p := by omega
      nlinarith
    rw [h_eq]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  have hmem : p ∈ Podd n := by
    unfold Podd
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hhi⟩, hp, by omega⟩
  refine ⟨hmem, ?_⟩
  unfold q_n
  exact Finset.dvd_prod_of_mem _ hmem

/-- **Lemma 3.1(i), part 1**: For every `n ≥ 3` with `n ≠ 6`, `q_n` has at least one prime
divisor `p ≡ 3 [MOD 4]`. -/
theorem q_n_has_prime_mod4 {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ p ∣ q_n n ∧ p % 4 = 3 := by
  by_cases h14 : 14 ≤ n
  · have hx : (7 : ℝ) ≤ (n : ℝ) / 2 := by
      have : (14 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h14
      linarith
    obtain ⟨p, hp, hlo, hhi, hmod⟩ := breusch_bertrand_mod4 ((n : ℝ) / 2) hx
    have hlo_nat : n / 2 < p := by
      by_contra hle
      push_neg at hle
      have h1 : (p : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hle
      have h2 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        exact_mod_cast Nat.div_mul_le_self n 2
      linarith
    have hhi_nat : p ≤ n := by
      have h1 : (p : ℝ) ≤ (n : ℝ) := by linarith
      exact_mod_cast h1
    exact ⟨p, hp, (prime_in_upper_half_dvd_q_n hp hlo_nat hhi_nat).2, hmod⟩
  · by_cases h7 : 7 ≤ n
    · refine ⟨7, by decide, ?_, by decide⟩
      exact (prime_in_upper_half_dvd_q_n (by decide) (by omega) h7).2
    · refine ⟨3, by decide, ?_, by decide⟩
      exact (@prime_in_upper_half_dvd_q_n n 3 Nat.prime_three (by omega) hn).2

private lemma zmod_sq_ne_neg_one_of_mod4_eq_3 {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 3)
    (z : ZMod p) : z ^ 2 ≠ -1 := by
  intro hz
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by omega
  have hz_ne : z ≠ 0 := by
    intro h0
    rw [h0, sq, zero_mul] at hz
    have h1 : (1 : ZMod p) = 0 := by
      calc (1 : ZMod p) = -(-1 : ZMod p) := by ring
        _ = -(0 : ZMod p) := by rw [← hz]
        _ = 0 := neg_zero
    exact one_ne_zero h1
  have hflt : z ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hz_ne
  obtain ⟨m, hm⟩ : ∃ m : ℕ, p = 4 * m + 3 := ⟨p / 4, by omega⟩
  have hp1 : p - 1 = 2 * (2 * m + 1) := by omega
  rw [hp1, pow_mul, hz] at hflt
  have hodd : (-1 : ZMod p) ^ (2 * m + 1) = -1 := by
    rw [pow_add, pow_mul]
    simp
  rw [hodd] at hflt
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    calc ((2 : ℕ) : ZMod p) = 1 - (-1 : ZMod p) := by norm_num
      _ = 1 - 1 := by rw [hflt]
      _ = 0 := sub_self 1
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- **Lemma 3.1(i), part 2a**: If `D` has a prime divisor `p ≡ 3 [MOD 4]`, then
`x^2 - D * y^2 = -1` has no integer solutions. -/
theorem neg_pell_no_int_sol {D p : ℕ} (hp : p.Prime) (hpD : p ∣ D) (hmod : p % 4 = 3)
    (x y : ℤ) : x ^ 2 - (D : ℤ) * y ^ 2 ≠ -1 := by
  intro h
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod_zmod : ((x ^ 2 - (D : ℤ) * y ^ 2 : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) := by
    rw [h]
  have hpD_zmod : (D : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p D).mpr hpD
  push_cast at hmod_zmod
  rw [hpD_zmod, zero_mul, sub_zero] at hmod_zmod
  exact zmod_sq_ne_neg_one_of_mod4_eq_3 hp hmod (x : ZMod p) hmod_zmod

/-- `q_n n` is square-free for all `n`. -/
theorem q_n_squarefree (n : ℕ) : Squarefree (q_n n) := by
  unfold q_n
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hq_ne : (∏ q ∈ Podd n, q) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun q hq => (Finset.mem_filter.mp hq).2.1.ne_zero)
  haveI : Fact p.Prime := ⟨hp⟩
  have hval : padicValNat p (∏ q ∈ Podd n, q) ≤ 1 := by
    rw [← Nat.factorization_def _ hp,
      Nat.factorization_prod (fun q hq => (Finset.mem_filter.mp hq).2.1.ne_zero)]
    simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
    by_cases hmem : p ∈ Podd n
    · rw [Finset.sum_eq_single p]
      · rw [hp.factorization_self]
      · intro q hq hqp
        have hq_pr : q.Prime := (Finset.mem_filter.mp hq).2.1
        exact Nat.factorization_eq_zero_of_not_dvd (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp h).symm)
      · intro habs; exact absurd hmem habs
    · rw [Finset.sum_eq_zero]
      · exact Nat.zero_le 1
      · intro q hq
        have hqp : q ≠ p := fun h => hmem (h ▸ hq)
        have hq_pr : q.Prime := (Finset.mem_filter.mp hq).2.1
        exact Nat.factorization_eq_zero_of_not_dvd (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hp hq_pr).mp h).symm)
  have h2 : 2 ≤ padicValNat p (∏ q ∈ Podd n, q) := by
    rw [← sq] at hpp
    exact (padicValNat_dvd_iff_le hq_ne).mp hpp
  omega

/-- **Lemma 3.1(i), part 2b**: For `n ≥ 3` with `n ≠ 6`, `x^2 - q_n * y^2 = -1` has no rational
solutions. -/
theorem neg_pell_no_rat_sol {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≠ 6) (x y : ℚ) :
    x ^ 2 - (q_n n : ℚ) * y ^ 2 ≠ -1 := by
  obtain ⟨p, hp, hpq, hmod⟩ := q_n_has_prime_mod4 hn hn6
  have hsqf : ¬ p ^ 2 ∣ q_n n := by
    have := (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp
    simpa [sq] using this
  haveI : Fact p.Prime := ⟨hp⟩
  intro hxy
  -- Clear denominators: `x = a / d`, `y = b / d` with `d ≥ 1`
  let d : ℕ := x.den * y.den
  have hd_pos : 0 < d := Nat.mul_pos x.pos y.pos
  let a : ℤ := x.num * (y.den : ℤ)
  let b : ℤ := y.num * (x.den : ℤ)
  have hxa : x = (a : ℚ) / (d : ℚ) := by
    have h1 : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
    have hyd : (y.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr y.pos.ne'
    calc x = (x.num : ℚ) / (x.den : ℚ) := h1
      _ = ((x.num : ℚ) * (y.den : ℚ)) / ((x.den : ℚ) * (y.den : ℚ)) := by
          field_simp [hyd]
      _ = (a : ℚ) / (d : ℚ) := by push_cast [a, d]; rfl
  have hyb : y = (b : ℚ) / (d : ℚ) := by
    have h1 : y = (y.num : ℚ) / (y.den : ℚ) := (Rat.num_div_den y).symm
    have hxd : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.pos.ne'
    calc y = (y.num : ℚ) / (y.den : ℚ) := h1
      _ = ((y.num : ℚ) * (x.den : ℚ)) / ((x.den : ℚ) * (y.den : ℚ)) := by
          field_simp [hxd]
      _ = (b : ℚ) / (d : ℚ) := by push_cast [b, d]; rfl
  have hint : a ^ 2 + (d : ℤ) ^ 2 = (q_n n : ℤ) * b ^ 2 := by
    rw [hxa, hyb] at hxy
    have hd_q : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
    have hq_rat : (a : ℚ) ^ 2 + (d : ℚ) ^ 2 = (q_n n : ℚ) * (b : ℚ) ^ 2 := by
      field_simp [hd_q] at hxy
      linarith
    exact_mod_cast hq_rat
  -- Strong induction on `d`
  suffices h : ∀ d0 : ℕ, 0 < d0 → ∀ a0 b0 : ℤ, a0 ^ 2 + (d0 : ℤ) ^ 2 ≠ (q_n n : ℤ) * b0 ^ 2 from
    h d hd_pos a b hint
  intro d0
  induction d0 using Nat.strong_induction_on with
  | h d0 ih =>
    intro hd0_pos a0 b0 heq
    have hmod_z : ((a0 ^ 2 + (d0 : ℤ) ^ 2 : ℤ) : ZMod p) = (((q_n n : ℤ) * b0 ^ 2 : ℤ) : ZMod p) := by
      rw [heq]
    have hpq_z : (q_n n : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p (q_n n)).mpr hpq
    push_cast at hmod_z
    rw [hpq_z, zero_mul] at hmod_z
    have hd0_zero : (d0 : ZMod p) = 0 := by
      by_contra hne
      have hsq : ((a0 : ZMod p) * (d0 : ZMod p)⁻¹) ^ 2 = -1 := by
        calc ((a0 : ZMod p) * (d0 : ZMod p)⁻¹) ^ 2
            = (a0 : ZMod p) ^ 2 * ((d0 : ZMod p) ^ 2)⁻¹ := by ring
          _ = (-(d0 : ZMod p) ^ 2) * ((d0 : ZMod p) ^ 2)⁻¹ := by
              have : (a0 : ZMod p) ^ 2 = -(d0 : ZMod p) ^ 2 := eq_neg_of_add_eq_zero_left hmod_z
              rw [this]
          _ = -1 := by
              have hd2 : (d0 : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hne
              field_simp [hd2]
      exact zmod_sq_ne_neg_one_of_mod4_eq_3 hp hmod _ hsq
    have hpd0 : p ∣ d0 := (CharP.cast_eq_zero_iff (ZMod p) p d0).mp hd0_zero
    have ha0_zero : (a0 : ZMod p) = 0 := by
      rw [hd0_zero] at hmod_z
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hmod_z
      exact sq_eq_zero_iff.mp hmod_z
    have hpa0 : (p : ℤ) ∣ a0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a0 p).mp ha0_zero
    obtain ⟨d1, rfl⟩ := hpd0
    obtain ⟨a1, rfl⟩ := hpa0
    have hp2_dvd : (p : ℤ) ^ 2 ∣ (q_n n : ℤ) * b0 ^ 2 := by
      rw [← heq]
      refine ⟨a1 ^ 2 + (d1 : ℤ) ^ 2, ?_⟩
      push_cast; ring
    have hp_dvd_b0 : (p : ℤ) ∣ b0 := by
      have hp2_nat : p ^ 2 ∣ q_n n * b0.natAbs ^ 2 := by
        rw [← Int.natCast_dvd_natCast]
        push_cast
        rw [sq_abs b0]
        exact hp2_dvd
      have hpb_sq : p ∣ b0.natAbs ^ 2 := by
        by_contra hnb
        have hcop : Nat.Coprime (p ^ 2) (b0.natAbs ^ 2) := (hp.coprime_iff_not_dvd.mpr hnb).pow_left 2
        exact hsqf (hcop.dvd_of_dvd_mul_right hp2_nat)
      have hpb : p ∣ b0.natAbs := hp.dvd_of_dvd_pow hpb_sq
      exact Int.natCast_dvd.mpr hpb
    obtain ⟨b1, rfl⟩ := hp_dvd_b0
    have heq1 : a1 ^ 2 + (d1 : ℤ) ^ 2 = (q_n n : ℤ) * b1 ^ 2 := by
      have hp2_ne : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hp.ne_zero)
      apply mul_left_cancel₀ hp2_ne
      calc (p : ℤ) ^ 2 * (a1 ^ 2 + (d1 : ℤ) ^ 2)
          = ((p : ℤ) * a1) ^ 2 + ((p * d1 : ℕ) : ℤ) ^ 2 := by push_cast; ring
        _ = (q_n n : ℤ) * ((p : ℤ) * b1) ^ 2 := heq
        _ = (p : ℤ) ^ 2 * ((q_n n : ℤ) * b1 ^ 2) := by ring
    have hd1_pos : 0 < d1 := by
      by_contra h0
      have : d1 = 0 := by omega
      subst this
      simp at hd0_pos
    have hd1_lt : d1 < p * d1 := lt_mul_of_one_lt_left hd1_pos hp.one_lt
    exact ih d1 hd1_lt hd1_pos a1 b1 heq1

/-- **Lemma 3.1(i), part 3**: `log q_n > 0.4 * n` for all `n ≥ 116`. -/
theorem log_q_n_gt_point4 {n : ℕ} (hn : 116 ≤ n) :
    0.4 * (n : ℝ) < Real.log (q_n n : ℝ) := by
  rw [log_q_n_eq_sum_log n]
  have hsub : (Finset.Ioc (n / 2) n).filter Nat.Prime ⊆ Podd n := by
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    have hIoc := Finset.mem_Ioc.mp hmem.1
    exact (prime_in_upper_half_dvd_q_n hmem.2 hIoc.1 hIoc.2).1
  have hle : ∑ p ∈ (Finset.Ioc (n / 2) n).filter Nat.Prime, Real.log (p : ℝ) ≤
      ∑ p ∈ Podd n, Real.log (p : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have hp_ge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.two_le
    exact Real.log_nonneg (by linarith)
  exact lt_of_lt_of_le (rosser_schoenfeld_theta_diff n hn) hle

/-- **Lemma 3.1(i), part 4**: If `0.4 * n < log q_n`, then `0.2 * n < log ε_n`. -/
theorem log_fund_pell_gt_point2 {n X₁ Y₁ : ℕ}
    (hq_log : 0.4 * (n : ℝ) < Real.log (q_n n : ℝ))
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁) :
    0.2 * (n : ℝ) < Real.log (pellUnit (q_n n) X₁ Y₁) := by
  have hq_pos : 1 ≤ q_n n := by
    by_contra h0
    have hq0 : q_n n = 0 := by omega
    rw [hq0] at hq_log
    simp at hq_log
    linarith
  have h_gt : 2 * Real.sqrt (q_n n : ℝ) < pellUnit (q_n n) X₁ Y₁ :=
    pellUnit_gt_two_sqrt hq_pos hfund
  have hsqrt_pos : 0 < 2 * Real.sqrt (q_n n : ℝ) := by positivity
  have hlog_lt : Real.log (2 * Real.sqrt (q_n n : ℝ)) < Real.log (pellUnit (q_n n) X₁ Y₁) :=
    Real.log_lt_log hsqrt_pos h_gt
  have hlog_eq : Real.log (2 * Real.sqrt (q_n n : ℝ)) =
      Real.log 2 + (1 / 2 : ℝ) * Real.log (q_n n : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.sqrt_eq_rpow,
      Real.log_rpow (by positivity)]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

private lemma nine_mul_factorial_lt_pow (n : ℕ) (hn : 8 ≤ n) : 9 * Nat.factorial n < n ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hn with h8 | hgt
    · have : n = 7 := by omega
      subst this
      norm_num [Nat.factorial]
    · have hih := ih (by omega)
      calc 9 * Nat.factorial (n + 1)
          = (n + 1) * (9 * Nat.factorial n) := by rw [Nat.factorial_succ]; ring
        _ < (n + 1) * n ^ n := Nat.mul_lt_mul_of_pos_left hih (by omega)
        _ ≤ (n + 1) * (n + 1) ^ n := Nat.mul_le_mul_left (n + 1) (Nat.pow_le_pow_left (by omega) n)
        _ = (n + 1) ^ (n + 1) := by rw [pow_succ']

private lemma twelve_point_five_log_lt {n : ℕ} (hn : 116 ≤ n) :
    (12.5 : ℝ) * Real.log (n : ℝ) < (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn_ge : (116 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- `log(n / 20) ≤ n / 20 - 1`, and `log 20 < 3` since `20 < e^3`
  have hlog_div : Real.log ((n : ℝ) / 20) ≤ (n : ℝ) / 20 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlog20 : Real.log 20 < 3 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have he1 : (2.718 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have he3 : (2.718 : ℝ) ^ 3 < Real.exp 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
    norm_num at he3
    linarith
  have hlog_n : Real.log (n : ℝ) = Real.log ((n : ℝ) / 20) + Real.log 20 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    ring_nf
  linarith

/-- **Lemma 3.1(i), part 5**: For `n ≥ 8`, if `n! + 1 = m^2` and `m + s_n √q_n = ε_n^k` with
`0.2 * n < log ε_n`, then `1 ≤ k < 2.5 * log n`, and for `n ≥ 116`, `2.5 * log n < n / 5`. -/
theorem pell_index_upper_bound {n m k X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hm : Nat.factorial n + 1 = m ^ 2)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hlog_eps : 0.2 * (n : ℝ) < Real.log (pellUnit (q_n n) X₁ Y₁))
    (hk_eq : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) =
      (pellUnit (q_n n) X₁ Y₁) ^ k) :
    1 ≤ k ∧ (k : ℝ) < 2.5 * Real.log (n : ℝ) ∧
      (116 ≤ n → (2.5 : ℝ) * Real.log (n : ℝ) < (n : ℝ) / 5) := by
  have hs_pos : 0 < s_n n := by
    unfold s_n
    exact Finset.prod_pos (fun q hq => pow_pos (Finset.mem_filter.mp hq).2.pos _)
  have hq_pos : 0 < q_n n := by
    unfold q_n
    exact Finset.prod_pos (fun q hq => (Finset.mem_filter.mp hq).2.1.pos)
  have hm_pos : 0 < m := by
    by_contra h0
    have : m = 0 := by omega
    subst this
    simp at hm
  have heps_gt1 : 1 < pellUnit (q_n n) X₁ Y₁ := by
    rw [← Real.log_pos_iff (by unfold pellUnit; positivity)]
    have : 0 < (0.2 : ℝ) * (n : ℝ) := by positivity
    linarith
  have hms_gt1 : 1 < (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) := by
    have hm_ge : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
    have hs_ge : (1 : ℝ) ≤ (s_n n : ℝ) := by exact_mod_cast hs_pos
    have hq_ge : (1 : ℝ) ≤ Real.sqrt (q_n n : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hq_pos)
    nlinarith
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    subst hk0
    simp at hk_eq
    linarith
  have hm_lt : (m : ℝ) < 2 * Real.sqrt ((Nat.factorial n : ℕ) : ℝ) := by
    have hsq : (m : ℝ) ^ 2 < (2 * Real.sqrt ((Nat.factorial n : ℕ) : ℝ)) ^ 2 := by
      have hfac_ge1 : (1 : ℝ) ≤ ((Nat.factorial n : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_pos n
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hm_real : (m : ℝ) ^ 2 = ((Nat.factorial n : ℕ) : ℝ) + 1 := by exact_mod_cast hm.symm
      linarith
    have h1 : Real.sqrt ((m : ℝ) ^ 2) < Real.sqrt ((2 * Real.sqrt ((Nat.factorial n : ℕ) : ℝ)) ^ 2) :=
      Real.sqrt_lt_sqrt (by positivity) hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h1
  have hs_sqrt_eq : (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = Real.sqrt ((Nat.factorial n : ℕ) : ℝ) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (s_n n : ℝ)), ← Real.sqrt_mul (by positivity)]
    congr 1
    have hfac := factorial_eq_q_n_mul_s_n_sq n
    have hfac_r : ((Nat.factorial n : ℕ) : ℝ) = (s_n n : ℝ) ^ 2 * (q_n n : ℝ) := by
      have : Nat.factorial n = (s_n n) ^ 2 * q_n n := by rw [hfac]; ring
      exact_mod_cast this
    exact hfac_r.symm
  have hms_lt : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) <
      3 * Real.sqrt ((Nat.factorial n : ℕ) : ℝ) := by
    linarith
  have h3_lt_pow : (3 * Real.sqrt ((Nat.factorial n : ℕ) : ℝ)) ^ 2 < ((n : ℝ) ^ n) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hnat := nine_mul_factorial_lt_pow n hn
    exact_mod_cast hnat
  have hms_sq_lt : ((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2 < (n : ℝ) ^ n := by
    have h1 : ((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2 <
        (3 * Real.sqrt ((Nat.factorial n : ℕ) : ℝ)) ^ 2 :=
      pow_lt_pow_left₀ hms_lt (by positivity) (by norm_num)
    exact lt_trans h1 h3_lt_pow
  have hlog_ms : 2 * Real.log ((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) <
      (n : ℝ) * Real.log (n : ℝ) := by
    have hpos1 : 0 < ((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) ^ 2 := by positivity
    have hlog_lt := Real.log_lt_log hpos1 hms_sq_lt
    rwa [Real.log_pow, Real.log_pow, show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] at hlog_lt
  have hlog_pow : Real.log ((m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) =
      (k : ℝ) * Real.log (pellUnit (q_n n) X₁ Y₁) := by
    rw [hk_eq, Real.log_pow]
  have hk_lt : (k : ℝ) < 2.5 * Real.log (n : ℝ) := by
    have h1 : (k : ℝ) * (0.4 * (n : ℝ)) < (k : ℝ) * (2 * Real.log (pellUnit (q_n n) X₁ Y₁)) := by
      apply mul_lt_mul_of_pos_left (by linarith)
      exact_mod_cast hk1
    have h2 : (k : ℝ) * (0.4 * (n : ℝ)) < (n : ℝ) * Real.log (n : ℝ) := by
      linarith
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    nlinarith
  refine ⟨hk1, hk_lt, fun hn116 => ?_⟩
  have h12 := twelve_point_five_log_lt hn116
  linarith

/-- **Lemma 3.1(ii), part 1**:
`log(s_n √q_n) = (1/2) log(n!) = (1/2) n log n - (1/2) n + (1/4) log(2πn) + O(n⁻¹)`. -/
theorem log_s_n_sqrt_q_n_asymptotic :
    (fun n : ℕ =>
      Real.log ((s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) -
        ((1 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ) - (1 / 2 : ℝ) * (n : ℝ) +
          (1 / 4 : ℝ) * Real.log (2 * Real.pi * (n : ℝ))))
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  have heq : ∀ n : ℕ, Real.log ((s_n n : ℝ) * Real.sqrt (q_n n : ℝ)) =
      (1 / 2 : ℝ) * Real.log ((Nat.factorial n : ℕ) : ℝ) := by
    intro n
    have hfac := factorial_eq_q_n_mul_s_n_sq n
    have hs_pos_nat : 0 < s_n n := by
      unfold s_n
      exact Finset.prod_pos (fun q hq => pow_pos (Finset.mem_filter.mp hq).2.pos _)
    have hq_pos_nat : 0 < q_n n := by
      unfold q_n
      exact Finset.prod_pos (fun q hq => (Finset.mem_filter.mp hq).2.1.pos)
    have hs_pos : (0 : ℝ) < (s_n n : ℝ) := by exact_mod_cast hs_pos_nat
    have hq_pos : (0 : ℝ) < (q_n n : ℝ) := by exact_mod_cast hq_pos_nat
    have hprod : (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = Real.sqrt ((Nat.factorial n : ℕ) : ℝ) := by
      rw [← Real.sqrt_sq hs_pos.le, ← Real.sqrt_mul (by positivity)]
      congr 1
      have : Nat.factorial n = (s_n n) ^ 2 * q_n n := by rw [hfac]; ring
      exact_mod_cast this.symm
    rw [hprod, Real.sqrt_eq_rpow, Real.log_rpow (by positivity)]
  have hst := stirling_log_factorial_remainder.const_mul_left (1 / 2 : ℝ)
  refine hst.congr' (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => rfl)
  dsimp only
  rw [heq n]
  ring

/-- **Lemma 3.1(ii), part 2**:
`log s_n = (1/2) n log n - ((1 + log 2)/2) n + O(n exp(-c₀ √(log n)))`. -/
theorem log_s_n_asymptotic :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      (fun n : ℕ =>
        Real.log (s_n n : ℝ) -
          ((1 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ) - ((1 + Real.log 2) / 2 : ℝ) * (n : ℝ)))
        =O[atTop] (fun n : ℕ => (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ)))) := by
  obtain ⟨c₀, hc₀, hq_asym⟩ := log_q_n_asymptotic
  refine ⟨c₀, hc₀, ?_⟩
  have hlog_n_le : (fun n : ℕ => (n : ℝ)⁻¹) =O[atTop]
      (fun n : ℕ => (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ)))) := by
    -- `n⁻¹ = n * n⁻²`, and `n⁻² ≤ exp(-c₀ √(log n))` eventually since `c₀ √(log n) ≤ 2 log n`
    have hsqrt_le : ∀ᶠ n : ℕ in atTop,
        c₀ * Real.sqrt (Real.log (n : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
      have ht : Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (nhds 0) := by
        have h1 : (fun t : ℝ => Real.sqrt t / t) =ᶠ[atTop] (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) := by
          filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
          have ht_pos : 0 < t := by linarith
          calc Real.sqrt t / t = t ^ (1 / 2 : ℝ) * t ^ (-1 : ℝ) := by
                rw [Real.sqrt_eq_rpow, div_eq_mul_inv, Real.rpow_neg_one]
            _ = t ^ ((1 / 2 : ℝ) + (-1 : ℝ)) := (Real.rpow_add ht_pos _ _).symm
            _ = t ^ (-(1 / 2 : ℝ)) := by norm_num
        have h2 : Tendsto (fun t : ℝ => Real.sqrt t / t) atTop (nhds 0) :=
          (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr' h1.symm
        exact h2.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      filter_upwards [ht.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < 2 / c₀)),
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 0)] with n hn hlog_pos
      dsimp only [Function.comp_def] at hlog_pos
      rw [div_le_iff₀ hlog_pos] at hn
      have := mul_le_mul_of_nonneg_left hn hc₀.le
      have hc0_ne : c₀ ≠ 0 := hc₀.ne'
      calc c₀ * Real.sqrt (Real.log (n : ℝ)) ≤ c₀ * (2 / c₀ * Real.log (n : ℝ)) := this
        _ = 2 * Real.log (n : ℝ) := by field_simp [hc0_ne]
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hsqrt_le, eventually_ge_atTop 1] with n hn_sqrt hn1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
    have hexp_ge : (n : ℝ) ^ (-2 : ℝ) ≤ Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by
      calc (n : ℝ) ^ (-2 : ℝ) = Real.exp ((-2 : ℝ) * Real.log (n : ℝ)) := by
            rw [Real.rpow_def_of_pos hn_pos]; ring_nf
        _ ≤ Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) :=
            Real.exp_le_exp.mpr (by linarith)
    calc (n : ℝ)⁻¹ = (n : ℝ) * (n : ℝ) ^ (-2 : ℝ) := by
          rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
          field_simp [hn_pos.ne']
      _ ≤ (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp_ge hn_pos.le
  have hlog2pi_le : (fun n : ℕ => (1 / 4 : ℝ) * Real.log (2 * Real.pi * (n : ℝ))) =O[atTop]
      (fun n : ℕ => (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ)))) := by
    have hsqrt_half : ∀ᶠ n : ℕ in atTop,
        c₀ * Real.sqrt (Real.log (n : ℝ)) ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) := by
      have ht : Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (nhds 0) := by
        have h1 : (fun t : ℝ => Real.sqrt t / t) =ᶠ[atTop] (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) := by
          filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
          have ht_pos : 0 < t := by linarith
          calc Real.sqrt t / t = t ^ (1 / 2 : ℝ) * t ^ (-1 : ℝ) := by
                rw [Real.sqrt_eq_rpow, div_eq_mul_inv, Real.rpow_neg_one]
            _ = t ^ ((1 / 2 : ℝ) + (-1 : ℝ)) := (Real.rpow_add ht_pos _ _).symm
            _ = t ^ (-(1 / 2 : ℝ)) := by norm_num
        have h2 : Tendsto (fun t : ℝ => Real.sqrt t / t) atTop (nhds 0) :=
          (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr' h1.symm
        exact h2.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      filter_upwards [ht.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < (1 / 2) / c₀)),
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 0)] with n hn hlog_pos
      dsimp only [Function.comp_def] at hlog_pos
      rw [div_le_iff₀ hlog_pos] at hn
      have := mul_le_mul_of_nonneg_left hn hc₀.le
      have hc0_ne : c₀ ≠ 0 := hc₀.ne'
      calc c₀ * Real.sqrt (Real.log (n : ℝ)) ≤ c₀ * (((1 / 2 : ℝ) / c₀) * Real.log (n : ℝ)) := this
        _ = (1 / 2 : ℝ) * Real.log (n : ℝ) := by field_simp [hc0_ne]
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hsqrt_half, eventually_ge_atTop 100] with n hn_sqrt hn100
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog2pi_nn : 0 ≤ (1 / 4 : ℝ) * Real.log (2 * Real.pi * (n : ℝ)) := by
      apply mul_nonneg (by norm_num)
      apply Real.log_nonneg
      have h1 : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn100
      have hpi : 3 < Real.pi := Real.pi_gt_three
      nlinarith
    rw [Real.norm_of_nonneg hlog2pi_nn, Real.norm_of_nonneg (by positivity), one_mul]
    have hexp_ge : Real.sqrt (n : ℝ) ≤ (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by
      have h1 : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) := by
        calc (n : ℝ) ^ (-(1 / 2 : ℝ)) = Real.exp (-(1 / 2 : ℝ) * Real.log (n : ℝ)) := by
              rw [Real.rpow_def_of_pos hn_pos]; ring_nf
          _ ≤ Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) :=
              Real.exp_le_exp.mpr (by linarith)
      calc Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
        _ = (n : ℝ) ^ (1 + (-(1 / 2 : ℝ))) := by norm_num
        _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_add hn_pos 1 (-(1 / 2))
        _ = (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
        _ ≤ (n : ℝ) * Real.exp (-c₀ * Real.sqrt (Real.log (n : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 hn_pos.le
    have hlog_le_sqrt : (1 / 4 : ℝ) * Real.log (2 * Real.pi * (n : ℝ)) ≤ Real.sqrt (n : ℝ) := by
      have h1 : Real.log (Real.sqrt (n : ℝ)) ≤ Real.sqrt (n : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log (n : ℝ) = 2 * Real.log (Real.sqrt (n : ℝ)) := by
        rw [Real.sqrt_eq_rpow, Real.log_rpow hn_pos]; ring
      have h3 : Real.log (2 * Real.pi) ≤ 3 := by
        rw [Real.log_le_iff_le_exp (by positivity)]
        have hpi : Real.pi < 4 := Real.pi_lt_four
        have he1 : (2.718 : ℝ) < Real.exp 1 := by
          have := Real.exp_one_gt_d9
          linarith
        have he3 : (2.718 : ℝ) ^ 3 < Real.exp 3 := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
          exact pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
        norm_num at he3
        linarith
      have h4 : Real.log (2 * Real.pi * (n : ℝ)) = Real.log (2 * Real.pi) + Real.log (n : ℝ) :=
        Real.log_mul (by positivity) hn_pos.ne'
      have hsqrt10 : (10 : ℝ) ≤ Real.sqrt (n : ℝ) := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10)]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn100)
      linarith
    exact le_trans hlog_le_sqrt hexp_ge
  have h1 := log_s_n_sqrt_q_n_asymptotic.trans hlog_n_le
  have h2 := h1.add hlog2pi_le
  have h3 := h2.sub (hq_asym.const_mul_left (1 / 2 : ℝ))
  refine h3.congr' (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => rfl)
  have hs_pos_nat : 0 < s_n n := by
    unfold s_n
    exact Finset.prod_pos (fun q hq => pow_pos (Finset.mem_filter.mp hq).2.pos _)
  have hq_pos_nat : 0 < q_n n := by
    unfold q_n
    exact Finset.prod_pos (fun q hq => (Finset.mem_filter.mp hq).2.1.pos)
  have hs_pos : (0 : ℝ) < (s_n n : ℝ) := by exact_mod_cast hs_pos_nat
  have hq_pos : (0 : ℝ) < (q_n n : ℝ) := by exact_mod_cast hq_pos_nat
  dsimp only
  rw [Real.log_mul hs_pos.ne' (by positivity), Real.sqrt_eq_rpow, Real.log_rpow hq_pos]
  ring

end GrasGreenbergBrocard
