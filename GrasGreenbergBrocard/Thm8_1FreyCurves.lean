import GrasGreenbergBrocard.ExternalAxiomsSec8
import GrasGreenbergBrocard.Prop4_1SmoothBiquad
import GrasGreenbergBrocard.Thm4_2QuarticCores
import GrasGreenbergBrocard.ValuationParityThm

/-!
# Section 8.1: Frey–Hellegouarch Elliptic Curves, Base-Change Unit Factorization, and Level-2 CM Reduction

This file formalizes **Theorem 8.1(i)–(ii)** of the manuscript:
- Exact Weierstrass invariants $b_2, b_4, b_6, b_8, c_4, \Delta$ of $\mathcal{E}_n : Y^2 = X^3 + 2mX^2 + X$,
  minimality and multiplicative reduction at all odd primes $p \le n$ with $v_p(\Delta(\mathcal{E}_n)) = v_p(n!)$,
  2-isogenous curve $\widehat{\mathcal{E}}_n$ discriminant $2^{12}(n!)^2$, and quadratic base-change
  unit factorization $X(X + \varepsilon_n^k)(X + \varepsilon_n^{-k}) = X^3 + 2mX^2 + X$ in $\mathbb{Z}[\sqrt{q_n}]$ (eq. 8.1).
- Level-2 Frey curve $F_n^{(2)} : Y^2 = X(X - 2(X_1 - 1))(X + 4)$ in the $k = 2$ regime:
  shifted model $Y^2 = (V^2 - 4)(V - 2X_1)$ (eq. 8.2), $\Delta(F_n^{(2)}) = 2^{12} q_n^2 Y_1^4$,
  $c_4(F_n^{(2)}) = 64(X_1^2 + 3)$, good CM reduction modulo odd $p \mid X_1$ to $Y^2 \equiv V^3 - 4V \pmod p$,
  exact identity $j(F_n^{(2)}) - 1728 = \frac{64 X_1^2 (X_1^2 - 9)^2}{(X_1^2 - 1)^2}$ (eq. 8.3),
  $v_p(j(F_n^{(2)})) = -2$ for $p \in (n/2, n]$, unconditional $abc$-quality lower bound
  $q(A_n, B_n, C_n) \ge (1/4 - o(1))\log n \to \infty$, and Hall-type cubic-square bound
  $0 < y_n^2 - x_n^3 = v_n^2 \le x_n^{(12 + o(1))/\log n}$.
-/

open scoped BigOperators
open Real Finset Filter

namespace GrasGreenbergBrocard

set_option maxHeartbeats 800000

/-- Radical of a positive natural number: $\operatorname{rad}(N) = \prod_{p \mid N} p$. -/
def radNat (N : ℕ) : ℕ := ∏ p ∈ N.primeFactors, p

lemma radNat_pos (N : ℕ) : 0 < radNat N :=
  Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)

lemma radNat_dvd_of_dvd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ∣ b) :
    radNat a ∣ radNat b := by
  unfold radNat
  apply Finset.prod_dvd_prod_of_subset
  exact Nat.primeFactors_mono hab hb

/-- Weierstrass invariants of $\mathcal{E}_n : Y^2 = X^3 + 2m X^2 + X$. -/
def freyE_b2 (m : ℕ) : ℤ := 8 * (m : ℤ)
def freyE_b4 : ℤ := 2
def freyE_b6 : ℤ := 0
def freyE_b8 : ℤ := -1
def freyE_c4 (m : ℕ) : ℤ := (freyE_b2 m) ^ 2 - 24 * freyE_b4
def freyE_Delta (m : ℕ) : ℤ := -(freyE_b2 m) ^ 2 * freyE_b8 - 8 * freyE_b4 ^ 3

/-- Weierstrass invariants of $F_n^{(2)} : Y^2 = (V^2 - 4)(V - 2X_1) = V^3 - 2X_1 V^2 - 4V + 8X_1$. -/
def freyF2_c4 (X₁ : ℕ) : ℤ := 64 * ((X₁ : ℤ) ^ 2 + 3)
def freyF2_Delta (X₁ : ℕ) : ℤ := 2 ^ 12 * ((X₁ : ℤ) ^ 2 - 1) ^ 2

/-- **Theorem 8.1(i)**: Weierstrass invariants, minimality and first-power factorial multiplicative
reduction of $\mathcal{E}_n : Y^2 = X^3 + 2mX^2 + X$ at all odd primes $p \le n$, 2-isogenous
discriminant $2^{12}(n!)^2$, modularity/conductor/Frobenius trace, and quadratic base-change
unit factorization (eq. 8.1) in $\mathbb{Z}[\sqrt{q_n}]$. -/
theorem thm_8_1_part1_frey_E {n m X₁ Y₁ : ℕ} (hn : 8 ≤ n) (hm : Nat.factorial n + 1 = m ^ 2) :
    freyE_c4 m = 16 * (4 * (Nat.factorial n : ℤ) + 1) ∧
    freyE_Delta m = 64 * (Nat.factorial n : ℤ) ∧
    (∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ n →
      ¬ ((p : ℤ) ∣ freyE_c4 m) ∧
      padicValNat p (64 * Nat.factorial n) = padicValNat p (Nat.factorial n)) ∧
    -- 2-isogenous curve \widehat{\mathcal{E}}_n : y^2 = x(x - 2(m-1))(x - 2(m+1)) discriminant
    (16 : ℤ) * (2 * ((m : ℤ) - 1)) ^ 2 * (2 * ((m : ℤ) + 1)) ^ 2 * 4 ^ 2 =
      2 ^ 12 * (Nat.factorial n : ℤ) ^ 2 ∧
    -- Quadratic base-change unit factorization in Zsqrtd (q_n n) (eq. 8.1):
    (∀ X : Zsqrtd (q_n n : ℤ),
      let εk : Zsqrtd (q_n n : ℤ) := ⟨(m : ℤ), (s_n n : ℤ)⟩
      let εk_inv : Zsqrtd (q_n n : ℤ) := ⟨(m : ℤ), -(s_n n : ℤ)⟩
      εk * εk_inv = 1 ∧
      X * (X + εk) * (X + εk_inv) = X ^ 3 + (2 * (m : ℤ) : Zsqrtd (q_n n : ℤ)) * X ^ 2 + X) ∧
    -- Modularity, conductor, and Frobenius traces
    (∃ D : FreyCurveArithmeticData n m X₁ Y₁,
      D.isModular_E ∧ D.conductor_E = 2 ^ D.alpha_E * ∏ p ∈ (Finset.Icc 3 n).filter Nat.Prime, p ∧
      D.alpha_E ≤ 3 ∧ ∀ (p : ℕ) (hp : p.Prime), 3 ≤ p → p ≤ n → D.ap_E p = @legendreSym p ⟨hp⟩ (-(m : ℤ))) := by
  have hm_z : (Nat.factorial n : ℤ) + 1 = (m : ℤ) ^ 2 := by exact_mod_cast hm
  have hc4 : freyE_c4 m = 16 * (4 * (Nat.factorial n : ℤ) + 1) := by
    unfold freyE_c4 freyE_b2 freyE_b4; linarith
  have hDelta : freyE_Delta m = 64 * (Nat.factorial n : ℤ) := by
    unfold freyE_Delta freyE_b2 freyE_b4 freyE_b8; linarith
  refine ⟨hc4, hDelta, ?_, ?_, ?_, ?_⟩
  · intro p hp hp3 hpn
    have hp_fac : p ∣ Nat.factorial n := Nat.dvd_factorial hp.pos hpn
    have hp_fac_z : (p : ℤ) ∣ (Nat.factorial n : ℤ) := Int.natCast_dvd_natCast.mpr hp_fac
    constructor
    · rw [hc4]; intro hdvd
      have hcop16 : IsCoprime (p : ℤ) 16 := by
        have hp2 : p ≠ 2 := by omega
        have h1 : Nat.Coprime p 16 := (hp.coprime_iff_not_dvd.mpr (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 4 from h)))))
        exact_mod_cast h1.isCoprime
      have hdvd2 : (p : ℤ) ∣ 4 * (Nat.factorial n : ℤ) + 1 := hcop16.dvd_of_dvd_mul_left hdvd
      have h1 : (p : ℤ) ∣ 1 := by
        have := dvd_sub hdvd2 (dvd_mul_of_dvd_right hp_fac_z 4)
        simpa using this
      exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp h1)
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [padicValNat.mul (by norm_num) (Nat.factorial_pos n).ne']
      have h64 : padicValNat p 64 = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        intro h
        have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 6 from h))
        omega
      rw [h64, zero_add]
  · have h1 : ((m : ℤ) - 1) * ((m : ℤ) + 1) = (Nat.factorial n : ℤ) := by linarith
    calc (16 : ℤ) * (2 * ((m : ℤ) - 1)) ^ 2 * (2 * ((m : ℤ) + 1)) ^ 2 * 4 ^ 2
        = 2 ^ 12 * (((m : ℤ) - 1) * ((m : ℤ) + 1)) ^ 2 := by ring
      _ = 2 ^ 12 * (Nat.factorial n : ℤ) ^ 2 := by rw [h1]
  · intro X
    dsimp only
    have hfac_z : (Nat.factorial n : ℤ) = (q_n n : ℤ) * (s_n n : ℤ) ^ 2 := by
      exact_mod_cast factorial_eq_q_n_mul_s_n_sq n
    have hnorm : (m : ℤ) ^ 2 - (q_n n : ℤ) * (s_n n : ℤ) ^ 2 = 1 := by linarith
    have hmul1 : (⟨(m : ℤ), (s_n n : ℤ)⟩ : Zsqrtd (q_n n : ℤ)) * ⟨(m : ℤ), -(s_n n : ℤ)⟩ = 1 := by
      apply Zsqrtd.ext
      · change (m : ℤ) * (m : ℤ) + (q_n n : ℤ) * (s_n n : ℤ) * (-(s_n n : ℤ)) = 1
        linarith
      · change (m : ℤ) * (-(s_n n : ℤ)) + (s_n n : ℤ) * (m : ℤ) = 0
        ring
    refine ⟨hmul1, ?_⟩
    have hadd : (⟨(m : ℤ), (s_n n : ℤ)⟩ : Zsqrtd (q_n n : ℤ)) + ⟨(m : ℤ), -(s_n n : ℤ)⟩ =
        (2 * (m : ℤ) : Zsqrtd (q_n n : ℤ)) := by
      ext <;> (simp; try ring)
    calc X * (X + ⟨(m : ℤ), (s_n n : ℤ)⟩) * (X + ⟨(m : ℤ), -(s_n n : ℤ)⟩)
        = X ^ 3 + (⟨(m : ℤ), (s_n n : ℤ)⟩ + ⟨(m : ℤ), -(s_n n : ℤ)⟩) * X ^ 2 +
          (⟨(m : ℤ), (s_n n : ℤ)⟩ * ⟨(m : ℤ), -(s_n n : ℤ)⟩) * X := by ring
      _ = X ^ 3 + (2 * (m : ℤ) : Zsqrtd (q_n n : ℤ)) * X ^ 2 + X := by rw [hadd, hmul1, one_mul]
  · obtain ⟨D, hmodE⟩ := frey_E_modularity (X₁ := X₁) (Y₁ := Y₁) hn hm
    exact ⟨D, hmodE, D.conductor_E_eq, D.alpha_E_le, D.ap_E_eq⟩

/-- **Theorem 8.1(ii) (Algebraic, CM-Reduction, and Valuation Structure of $F_n^{(2)}$)**:
In the $k = 2$ regime ($m = 2X_1^2 - 1$, $s_n = 2 X_1 Y_1$, $X_1^2 - q_n Y_1^2 = 1$), the Level-2
Frey curve $F_n^{(2)} : Y^2 = X(X - 2(X_1 - 1))(X + 4)$ satisfies eqs. (8.2)–(8.3), has good CM
reduction to $Y^2 \equiv V^3 - 4V \pmod p$ at every odd prime $p \mid X_1$, has $v_p(j(F_n^{(2)})) = -2$
at every prime $p \in (n/2, n]$, and has surjective mod-$\ell$ Galois representation for all $\ell \ge 5$. -/
theorem thm_8_1_part2_level2_cm_reduction {n m X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hm : Nat.factorial n + 1 = m ^ 2)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk2 : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2) :
    -- Shifted model (eq. 8.2)
    (∀ V : ℤ, (V - 2) * ((V - 2) - 2 * ((X₁ : ℤ) - 1)) * ((V - 2) + 4) =
      (V ^ 2 - 4) * (V - 2 * (X₁ : ℤ)) ∧
      (V ^ 2 - 4) * (V - 2 * (X₁ : ℤ)) = V ^ 3 - 2 * (X₁ : ℤ) * V ^ 2 - 4 * V + 8 * (X₁ : ℤ)) ∧
    -- Discriminant Δ(F_n^{(2)}) = 2^{12} q_n^2 Y_1^4
    freyF2_Delta X₁ = 2 ^ 12 * (q_n n : ℤ) ^ 2 * (Y₁ : ℤ) ^ 4 ∧
    -- Good CM reduction at odd primes p | X_1
    (∀ p : ℕ, p.Prime → 3 ≤ p → p ∣ X₁ →
      ¬ ((p : ℤ) ∣ freyF2_Delta X₁) ∧
      ∀ V : ℤ, (p : ℤ) ∣ (V ^ 3 - 2 * (X₁ : ℤ) * V ^ 2 - 4 * V + 8 * (X₁ : ℤ)) - (V ^ 3 - 4 * V)) ∧
    -- Exact j-invariant identity (eq. 8.3): j(F_n^{(2)}) - 1728 = 64 X_1^2 (X_1^2 - 9)^2 / (X_1^2 - 1)^2
    ((freyF2_c4 X₁ : ℚ) ^ 3 / (freyF2_Delta X₁ : ℚ) - 1728 =
      64 * (X₁ : ℚ) ^ 2 * ((X₁ : ℚ) ^ 2 - 9) ^ 2 / ((X₁ : ℚ) ^ 2 - 1) ^ 2) ∧
    -- v_p(j(F_n^{(2)})) = -2 for all primes p ∈ (n/2, n] (i.e. p^2 ∥ Δ and p ∤ c_4)
    (∀ p : ℕ, p.Prime → n / 2 < p → p ≤ n →
      padicValNat p (2 ^ 12 * (q_n n) ^ 2 * Y₁ ^ 4) = 2 ∧ ¬ ((p : ℤ) ∣ freyF2_c4 X₁)) ∧
    -- Modularity, slashed conductor formula, and surjectivity of mod-ℓ Galois representation for ℓ ≥ 5
    (∃ D : FreyCurveArithmeticData n m X₁ Y₁,
      D.isModular_F2 ∧
      D.conductor_F2 = 2 ^ D.alpha_F2 * ((∏ p ∈ (Finset.Icc 3 n).filter Nat.Prime, p) /
        (∏ p ∈ (Finset.Icc 3 n).filter (fun p => p.Prime ∧ p ∣ X₁), p)) ∧
      D.alpha_F2 ≤ 3 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ), D.surj_mod_ell_F2 ℓ hℓ hℓ5) := by
  have hX1_pos : 0 < X₁ := by have := hfund.1; omega
  have hY1_pos : 0 < Y₁ := hfund.2.1
  have hpell_z : (X₁ : ℤ) ^ 2 - 1 = (q_n n : ℤ) * (Y₁ : ℤ) ^ 2 := by linarith [hfund.2.2.1]
  have hpell_eq : X₁ ^ 2 = q_n n * Y₁ ^ 2 + 1 := by zify; linarith [hfund.2.2.1]
  obtain ⟨_, _, _, hs_eq, _, _, hfac_eq⟩ := k_eq_2_identities (by omega) (by omega) hm hfund hk2
  have hDelta_eq : freyF2_Delta X₁ = 2 ^ 12 * (q_n n : ℤ) ^ 2 * (Y₁ : ℤ) ^ 4 := by
    unfold freyF2_Delta; rw [hpell_z]; ring
  have hX1_gt1 : 1 < X₁ := by
    have hq_pos : 0 < q_n n := by unfold q_n; exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.1.pos)
    nlinarith [hpell_eq, hq_pos, hY1_pos]
  refine ⟨fun V => ⟨by ring, by ring⟩, hDelta_eq, ?_, ?_, ?_, ?_⟩
  · intro p hp hp3 hpX
    have hpX_z : (p : ℤ) ∣ (X₁ : ℤ) := Int.natCast_dvd_natCast.mpr hpX
    constructor
    · unfold freyF2_Delta; intro hdvd
      have hp2 : p ≠ 2 := by omega
      have hcop : IsCoprime (p : ℤ) (2 ^ 12) := by
        have h1 : Nat.Coprime p (2 ^ 12) := hp.coprime_iff_not_dvd.mpr (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)))
        exact_mod_cast h1.isCoprime
      have hdvd2 : (p : ℤ) ∣ ((X₁ : ℤ) ^ 2 - 1) ^ 2 := hcop.dvd_of_dvd_mul_left hdvd
      have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hdvd3 : (p : ℤ) ∣ (X₁ : ℤ) ^ 2 - 1 := hp_int.dvd_of_dvd_pow hdvd2
      have h1 : (p : ℤ) ∣ 1 := by
        have hsq : (p : ℤ) ∣ (X₁ : ℤ) ^ 2 := dvd_pow hpX_z (by norm_num)
        have := dvd_sub hsq hdvd3
        simpa using this
      exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp h1)
    · intro V
      have : (V ^ 3 - 2 * (X₁ : ℤ) * V ^ 2 - 4 * V + 8 * (X₁ : ℤ)) - (V ^ 3 - 4 * V) =
          (X₁ : ℤ) * (-2 * V ^ 2 + 8) := by ring
      rw [this]; exact dvd_mul_of_dvd_left hpX_z _
  · have hne : ((X₁ : ℚ) ^ 2 - 1) ≠ 0 := by
      have : (1 : ℚ) < (X₁ : ℚ) := by exact_mod_cast hX1_gt1
      nlinarith
    unfold freyF2_c4 freyF2_Delta
    push_cast
    field_simp [hne]
    ring
  · intro p hp hp_lo hp_hi
    haveI : Fact p.Prime := ⟨hp⟩
    have hp_ge5 : 5 ≤ p := by omega
    have hv1 : padicValNat p (Nat.factorial n) = 1 := by
      have h2p : n < 2 * p := by omega
      have hlt_sq : n < p ^ 2 := by nlinarith
      have hlog : Nat.log p n < 2 := Nat.log_lt_of_lt_pow (by omega) hlt_sq
      rw [padicValNat_factorial (b := 2) hlog, Finset.sum_Ico_succ_top (by norm_num), Finset.Ico_self, Finset.sum_empty, zero_add, pow_one]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    have hq_pos : 0 < q_n n := by unfold q_n; exact Finset.prod_pos (fun r hr => (Finset.mem_filter.mp hr).2.1.pos)
    have hp_q : p ∣ q_n n := by
      unfold q_n
      refine Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hp_hi⟩, hp, ?_⟩)
      rw [hv1]; omega
    have hvp_q : padicValNat p (q_n n) = 1 := by
      have hsqf := q_n_squarefree n
      have hge1 : 1 ≤ padicValNat p (q_n n) := one_le_padicValNat_of_dvd hq_pos.ne' hp_q
      have hle1 : padicValNat p (q_n n) ≤ 1 := by
        by_contra hgt; push Not at hgt
        have hsq_dvd : p ^ 2 ∣ q_n n := (padicValNat_dvd_iff_le hq_pos.ne').mpr hgt
        exact hp.prime.not_unit (hsqf p (by simpa [sq] using hsq_dvd))
      omega
    have hvp_Y1 : padicValNat p Y₁ = 0 := by
      have hfac_eq' : Nat.factorial n = 4 * X₁ ^ 2 * q_n n * (Y₁ * Y₁) := by
        have := factorial_eq_q_n_mul_s_n_sq n
        rw [hs_eq] at this; linarith
      have hv_sum := congrArg (padicValNat p) hfac_eq'
      rw [padicValNat.mul (by positivity) (mul_ne_zero hY1_pos.ne' hY1_pos.ne'),
        padicValNat.mul (by positivity) hq_pos.ne',
        padicValNat.mul hY1_pos.ne' hY1_pos.ne', hv1, hvp_q] at hv_sum
      omega
    constructor
    · have hrew : 2 ^ 12 * (q_n n) ^ 2 * Y₁ ^ 4 = 2 ^ 12 * (q_n n * q_n n) * ((Y₁ * Y₁) * (Y₁ * Y₁)) := by ring
      rw [hrew,
        padicValNat.mul (by positivity) (by positivity),
        padicValNat.mul (by norm_num) (mul_ne_zero hq_pos.ne' hq_pos.ne'),
        padicValNat.mul hq_pos.ne' hq_pos.ne',
        padicValNat.mul (mul_ne_zero hY1_pos.ne' hY1_pos.ne') (mul_ne_zero hY1_pos.ne' hY1_pos.ne'),
        padicValNat.mul hY1_pos.ne' hY1_pos.ne', hvp_q, hvp_Y1]
      have h212 : padicValNat p (2 ^ 12) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd; intro h
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
        omega
      omega
    · unfold freyF2_c4
      intro hdvd
      have hcop64 : IsCoprime (p : ℤ) 64 := by
        have h1 : Nat.Coprime p 64 := hp.coprime_iff_not_dvd.mpr (fun h => by
          have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 6 from h))
          omega)
        exact_mod_cast h1.isCoprime
      have hdvd2 : (p : ℤ) ∣ (X₁ : ℤ) ^ 2 + 3 := hcop64.dvd_of_dvd_mul_left hdvd
      have hp_pell : (p : ℤ) ∣ (X₁ : ℤ) ^ 2 - 1 := by
        rw [hpell_z]; exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hp_q) _
      have h4 : (p : ℤ) ∣ 4 := by
        have := dvd_sub hdvd2 hp_pell
        simpa using this
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from Int.natCast_dvd_natCast.mp h4))
      omega
  · obtain ⟨D, hmodF2, hsurj⟩ := frey_F2_modularity_and_galois hn hm hfund hk2
    exact ⟨D, hmodF2, D.conductor_F2_eq, D.alpha_F2_le, hsurj⟩

/-- **Theorem 8.1(ii) ($abc$-Quality Lower Bound & Hall-Type Cubic-Square Bound)**:
1. In the $k = 2$ regime, the coprime triple $(A_n, B_n, C_n) = ((X_1 - 1)/c_0, 2/c_0, (X_1 + 1)/c_0)$
   satisfies $A_n + B_n = C_n$ and $q(A_n, B_n, C_n) := \frac{\log C_n}{\log\operatorname{rad}(A_n B_n C_n)} \ge (1/4 - \varepsilon)\log n$
   for all sufficiently large $n$.
2. For any Brocard solution $n! + 1 = m^2$ ($n \ge 8$), writing $n! = u_n^3 v_n$ with $v_n$ cube-free
   and setting $x_n = u_n v_n$, $y_n = m v_n$ gives $0 < y_n^2 - x_n^3 = v_n^2$ and
   $\frac{\log(v_n^2)}{\log x_n} \le \frac{12 + \varepsilon}{\log n}$ for all sufficiently large $n$. -/
theorem thm_8_1_part2_abc_and_hall_bounds (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 8) :
    ∃ N₀ : ℕ, 8 ≤ N₀ ∧
      (∀ n m X₁ Y₁ : ℕ, N₀ ≤ n → Nat.factorial n + 1 = m ^ 2 →
        IsFundamentalPell (q_n n) X₁ Y₁ →
        (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2 →
        let c₀ := Nat.gcd (X₁ - 1) 2
        let A_n := (X₁ - 1) / c₀
        let B_n := 2 / c₀
        let C_n := (X₁ + 1) / c₀
        A_n + B_n = C_n ∧ Nat.Coprime A_n B_n ∧ Nat.Coprime A_n C_n ∧ Nat.Coprime B_n C_n ∧
        (1 / 4 - ε) * Real.log (n : ℝ) ≤ Real.log (C_n : ℝ) / Real.log (radNat (A_n * B_n * C_n) : ℝ)) ∧
      (∀ n m : ℕ, N₀ ≤ n → Nat.factorial n + 1 = m ^ 2 →
        ∃ u_n v_n : ℕ, 0 < u_n ∧ 0 < v_n ∧ Nat.factorial n = u_n ^ 3 * v_n ∧
          (∀ p : ℕ, p.Prime → padicValNat p v_n ≤ 2) ∧
          let x_n := u_n * v_n
          let y_n := m * v_n
          y_n ^ 2 - x_n ^ 3 = v_n ^ 2 ∧ 0 < v_n ^ 2 ∧
          Real.log ((v_n ^ 2 : ℕ) : ℝ) / Real.log (x_n : ℝ) ≤ (12 + ε) / Real.log (n : ℝ)) := by
  -- Use de_la_vallee_poussin_theta: |thetaPrime n - n| ≤ (ε/2) * n for large n
  obtain ⟨c₁, hc₁, hdlvp⟩ := de_la_vallee_poussin_theta
  have hθ_o : (fun n : ℕ => thetaPrime (n : ℝ) - (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    rw [Asymptotics.isLittleO_iff]
    intro δ hδ
    obtain ⟨C₁, hC₁⟩ := hdlvp.bound
    obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp hC₁
    have hC1_nn : 0 ≤ C₁ := by
      have h16 := hX₁ (max X₁ 16) (le_max_left _ _)
      have hpos_rhs : 0 < (max X₁ 16) * Real.exp (-c₁ * Real.sqrt (Real.log (max X₁ 16))) := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos_rhs] at h16
      exact nonneg_of_mul_nonneg_left (le_trans (abs_nonneg _) h16) hpos_rhs
    have htend : Filter.Tendsto (fun n : ℕ => C₁ * Real.exp (-c₁ * Real.sqrt (Real.log (n : ℝ)))) atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      have h2 : Filter.Tendsto (fun n : ℕ => -c₁ * Real.sqrt (Real.log (n : ℝ))) atTop atBot :=
        Filter.Tendsto.const_mul_atTop_of_neg (r := -c₁) (by linarith) h1
      simpa using (Real.tendsto_exp_atBot.comp h2).const_mul C₁
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (htend.eventually (Metric.ball_mem_nhds 0 hδ))
    refine Filter.eventually_atTop.mpr ⟨max (max (Nat.ceil X₁) N₁) 16, fun n hn => ?_⟩
    have h1 := hX₁ (n : ℝ) (le_trans (Nat.le_ceil X₁) (by exact_mod_cast le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)))
    have h2 := hN₁ n (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hC1_nn (Real.exp_pos _).le)] at h2
    have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (Real.exp_pos _).le)] at h1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
    calc |thetaPrime (n : ℝ) - (n : ℝ)|
        ≤ C₁ * ((n : ℝ) * Real.exp (-c₁ * Real.sqrt (Real.log (n : ℝ)))) := h1
      _ = (C₁ * Real.exp (-c₁ * Real.sqrt (Real.log (n : ℝ)))) * (n : ℝ) := by ring
      _ ≤ δ * (n : ℝ) := mul_le_mul_of_nonneg_right h2.le hnn
  obtain ⟨N_th, hN_th⟩ := Filter.eventually_atTop.mp (Asymptotics.IsLittleO.bound hθ_o (show (0 : ℝ) < ε / 100 by positivity))
  have h_inv_log : Filter.Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N_lg, hN_lg⟩ := Filter.eventually_atTop.mp (h_inv_log.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < ε / 100 by positivity)))
  let N₀ := max (max N_th N_lg) 100
  refine ⟨N₀, by omega, ?_, ?_⟩
  · intro n m X₁ Y₁ hn hm hfund hk2
    have hX1_pos : 0 < X₁ := by have := hfund.1; omega
    have hY1_pos : 0 < Y₁ := hfund.2.1
    have hpell_eq : X₁ ^ 2 = q_n n * Y₁ ^ 2 + 1 := by zify; linarith [hfund.2.2.1]
    obtain ⟨_, _, _, hs_eq, _, _, hfac_eq⟩ := k_eq_2_identities (by omega) (by omega) hm hfund hk2
    have hX1_gt1 : 1 < X₁ := by
      have hq_pos : 0 < q_n n := by unfold q_n; exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.1.pos)
      nlinarith [hpell_eq, hq_pos, hY1_pos]
    set c₀ := Nat.gcd (X₁ - 1) 2
    set A_n := (X₁ - 1) / c₀
    set B_n := 2 / c₀
    set C_n := (X₁ + 1) / c₀
    have hc0_pos : 0 < c₀ := Nat.gcd_pos_of_pos_right _ (by norm_num)
    have hc0_dvd1 : c₀ ∣ X₁ - 1 := Nat.gcd_dvd_left _ _
    have hc0_dvd2 : c₀ ∣ 2 := Nat.gcd_dvd_right _ _
    have hc0_dvd3 : c₀ ∣ X₁ + 1 := by
      have : X₁ + 1 = (X₁ - 1) + 2 := by omega
      rw [this]; exact dvd_add hc0_dvd1 hc0_dvd2
    have hsum : A_n + B_n = C_n := by
      have h1 : A_n * c₀ = X₁ - 1 := Nat.div_mul_cancel hc0_dvd1
      have h2 : B_n * c₀ = 2 := Nat.div_mul_cancel hc0_dvd2
      have h3 : C_n * c₀ = X₁ + 1 := Nat.div_mul_cancel hc0_dvd3
      have hmul : (A_n + B_n) * c₀ = C_n * c₀ := by rw [add_mul, h1, h2, h3]; omega
      exact mul_right_cancel₀ hc0_pos.ne' hmul
    have hcopAB : Nat.Coprime A_n B_n := Nat.coprime_div_gcd_div_gcd hc0_pos
    have hcopAC : Nat.Coprime A_n C_n := by rw [← hsum]; exact Nat.coprime_self_add_right.mpr hcopAB
    have hcopBC : Nat.Coprime B_n C_n := by rw [← hsum, add_comm]; exact Nat.coprime_self_add_right.mpr hcopAB.symm
    refine ⟨hsum, hcopAB, hcopAC, hcopBC, ?_⟩
    -- Bound log(rad(A_n B_n C_n)) ≤ thetaPrime n ≤ (1 + ε/100) * n
    have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hrad_dvd_fac : radNat (A_n * B_n * C_n) ∣ ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p := by
      unfold radNat
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      have hp_pr := Nat.prime_of_mem_primeFactors hp
      have hp_dvd : p ∣ A_n * B_n * C_n := Nat.dvd_of_mem_primeFactors hp
      have hABC_dvd : A_n * B_n * C_n ∣ Nat.factorial n := by
        have h1 : A_n * C_n * c₀ ^ 2 = (X₁ - 1) * (X₁ + 1) := by
          have hA : A_n * c₀ = X₁ - 1 := Nat.div_mul_cancel hc0_dvd1
          have hC : C_n * c₀ = X₁ + 1 := Nat.div_mul_cancel hc0_dvd3
          calc A_n * C_n * c₀ ^ 2 = (A_n * c₀) * (C_n * c₀) := by ring
            _ = (X₁ - 1) * (X₁ + 1) := by rw [hA, hC]
        have h2 : A_n * C_n ∣ X₁ ^ 2 - 1 := by
          refine ⟨c₀ ^ 2, ?_⟩
          have hsq : (X₁ - 1) * (X₁ + 1) = X₁ ^ 2 - 1 := by
            zify [hX1_pos, show 1 ≤ X₁ ^ 2 by nlinarith]; ring
          linarith
        have h3 : B_n ∣ 2 := Nat.div_dvd_of_dvd hc0_dvd2
        have h4 : 2 * (X₁ ^ 2 - 1) ∣ Nat.factorial n := by
          refine ⟨2 * X₁ ^ 2, ?_⟩
          have : 4 * X₁ ^ 2 * (X₁ ^ 2 - 1) = Nat.factorial n := by
            have := factorial_eq_q_n_mul_s_n_sq n
            rw [hs_eq] at this
            have hxp : X₁ ^ 2 - 1 = q_n n * Y₁ ^ 2 := by omega
            rw [hxp]; linarith
          linarith
        exact dvd_trans (show A_n * B_n * C_n ∣ 2 * (X₁ ^ 2 - 1) by
          have := mul_dvd_mul h3 h2
          simpa [mul_comm, mul_left_comm, mul_assoc] using this) h4
      have hp_fac : p ∣ Nat.factorial n := dvd_trans hp_dvd hABC_dvd
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_pr.two_le, hp_pr.dvd_factorial.mp hp_fac⟩, hp_pr⟩
    have hrad_ge2 : 2 ≤ radNat (A_n * B_n * C_n) := by
      have hA_pos : 0 < A_n := Nat.div_pos (Nat.le_of_dvd (by omega) hc0_dvd1) hc0_pos
      have hB_pos : 0 < B_n := Nat.div_pos (Nat.le_of_dvd (by norm_num) hc0_dvd2) hc0_pos
      have hC_pos : 0 < C_n := Nat.div_pos (Nat.le_of_dvd (by omega) hc0_dvd3) hc0_pos
      have hC_gt1 : 1 < C_n := by
        have h1 : 4 ≤ X₁ := by
          have h8 : Nat.factorial 8 ≤ Nat.factorial n := Nat.factorial_le (by omega)
          have h8v : Nat.factorial 8 = 40320 := by decide
          have h4x : Nat.factorial n ≤ 4 * X₁ ^ 4 := by
            have : Nat.factorial n = 4 * X₁ ^ 2 * (X₁ ^ 2 - 1) := by
              have := factorial_eq_q_n_mul_s_n_sq n; rw [hs_eq] at this
              have hxp : X₁ ^ 2 - 1 = q_n n * Y₁ ^ 2 := by omega
              rw [hxp]; linarith
            nlinarith [Nat.sub_le (X₁ ^ 2) 1]
          by_contra hlt4; push Not at hlt4
          have : X₁ ^ 4 ≤ 3 ^ 4 := Nat.pow_le_pow_left (by omega) 4
          omega
        have hc2 : c₀ ≤ 2 := Nat.le_of_dvd (by norm_num) hc0_dvd2
        have hCm : C_n * c₀ = X₁ + 1 := Nat.div_mul_cancel hc0_dvd3
        nlinarith only [h1, hc2, hCm]
      have hAB_pos : 1 ≤ A_n * B_n := Nat.mul_pos hA_pos hB_pos
      have hABC_gt1 : 1 < A_n * B_n * C_n := by nlinarith only [hAB_pos, hC_gt1]
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : A_n * B_n * C_n ≠ 1)
      have hmem : p ∈ (A_n * B_n * C_n).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, by positivity⟩
      have hdvd_rad : p ∣ radNat (A_n * B_n * C_n) := Finset.dvd_prod_of_mem _ hmem
      exact le_trans hp.two_le (Nat.le_of_dvd (radNat_pos _) hdvd_rad)
    have hlog_rad_pos : 0 < Real.log (radNat (A_n * B_n * C_n) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < radNat (A_n * B_n * C_n)))
    have hlog_rad_le_theta : Real.log (radNat (A_n * B_n * C_n) : ℝ) ≤ thetaPrime (n : ℝ) := by
      have hprod_pos : 0 < ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p :=
        Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
      have hle_r : (radNat (A_n * B_n * C_n) : ℝ) ≤ ((∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p : ℕ) : ℝ) :=
        by exact_mod_cast Nat.le_of_dvd hprod_pos hrad_dvd_fac
      have hlog := Real.log_le_log (by exact_mod_cast radNat_pos _) hle_r
      rw [Nat.cast_prod, Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr (Finset.mem_filter.mp hp).2.ne_zero)] at hlog
      have hth_eq : thetaPrime (n : ℝ) = ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, Real.log (p : ℝ) := by
        unfold thetaPrime; rw [Nat.floor_natCast]
      rw [hth_eq]; exact hlog
    have htheta_ub : thetaPrime (n : ℝ) ≤ (1 + ε / 100) * (n : ℝ) := by
      have h := hN_th n (by omega)
      have habs_n : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, habs_n] at h
      linarith [(abs_le.mp h).2]
    -- Lower bound log C_n ≥ (1/4) (n log n - n) - log 4
    have hlog_Cn_lb : (1 / 4 : ℝ) * ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ)) - Real.log 4 ≤ Real.log (C_n : ℝ) := by
      have hC_ge : ((X₁ : ℝ) + 1) / 2 ≤ (C_n : ℝ) := by
        have hc0_le2 : (c₀ : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_dvd (by norm_num) hc0_dvd2
        have hmul : (C_n : ℝ) * (c₀ : ℝ) = (X₁ : ℝ) + 1 := by exact_mod_cast Nat.div_mul_cancel hc0_dvd3
        have hc0_rpos : (0 : ℝ) < (c₀ : ℝ) := by exact_mod_cast hc0_pos
        rw [div_le_iff₀ (by norm_num)]; nlinarith only [hc0_le2, hmul, hc0_rpos]
      have hfac_le_X1 : (Nat.factorial n : ℝ) ≤ 4 * (X₁ : ℝ) ^ 4 := by
        have : Nat.factorial n ≤ 4 * X₁ ^ 4 := by
          have h4x : Nat.factorial n = 4 * X₁ ^ 2 * (X₁ ^ 2 - 1) := by
            have := factorial_eq_q_n_mul_s_n_sq n; rw [hs_eq] at this
            have hxp : X₁ ^ 2 - 1 = q_n n * Y₁ ^ 2 := by omega
            rw [hxp]; linarith
          nlinarith [Nat.sub_le (X₁ ^ 2) 1]
        exact_mod_cast this
      have hlog_fac : (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) ≤ Real.log (Nat.factorial n : ℝ) :=
        (n_log_n_sub_n_le_log_factorial n (by omega)).1
      have hlog_X1 : Real.log (Nat.factorial n : ℝ) ≤ Real.log 4 + 4 * Real.log (X₁ : ℝ) := by
        have h1 := Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) hfac_le_X1
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
        simpa using h1
      have hlog_C : Real.log (X₁ : ℝ) - Real.log 2 ≤ Real.log (C_n : ℝ) := by
        have h1 := Real.log_le_log (by positivity : (0 : ℝ) < ((X₁ : ℝ) + 1) / 2) hC_ge
        rw [Real.log_div (by positivity) (by norm_num)] at h1
        have h2 : Real.log (X₁ : ℝ) ≤ Real.log ((X₁ : ℝ) + 1) := Real.log_le_log (by exact_mod_cast hX1_pos) (by linarith)
        linarith only [h1, h2]
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith only [hlog_fac, hlog_X1, hlog_C, hlog4, hlog2_nn]
    have hil := hN_lg n (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg zero_le_one hlogn_pos.le)] at hil
    have hlog4_lt : Real.log 4 < 2 := by
      have h1 : (4 : ℝ) < Real.exp 2 := by
        have := Real.exp_one_gt_d9
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
      exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr h1
    rw [le_div_iff₀ hlog_rad_pos]
    have hrad_ub : Real.log (radNat (A_n * B_n * C_n) : ℝ) ≤ (1 + ε / 100) * (n : ℝ) :=
      le_trans hlog_rad_le_theta htheta_ub
    have hn_ge100 : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 100 ≤ n)
    have h1_lt : 1 < (ε / 100) * Real.log (n : ℝ) := (div_lt_iff₀ hlogn_pos).mp hil
    calc (1 / 4 - ε) * Real.log (n : ℝ) * Real.log (radNat (A_n * B_n * C_n) : ℝ)
        ≤ (1 / 4 - ε) * Real.log (n : ℝ) * ((1 + ε / 100) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hrad_ub (mul_nonneg (by linarith only [hε1]) hlogn_pos.le)
      _ ≤ (1 / 4 : ℝ) * ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ)) - Real.log 4 := by
          have hcoef : (1 / 4 - ε) * (1 + ε / 100) ≤ 1 / 4 - (3 / 4) * ε := by nlinarith only [hε0, hε1]
          have hstep1 : (1 / 4 - ε) * Real.log (n : ℝ) * ((1 + ε / 100) * (n : ℝ)) ≤
              (1 / 4 - (3 / 4) * ε) * ((n : ℝ) * Real.log (n : ℝ)) := by
            have : (1 / 4 - ε) * Real.log (n : ℝ) * ((1 + ε / 100) * (n : ℝ)) =
                ((1 / 4 - ε) * (1 + ε / 100)) * ((n : ℝ) * Real.log (n : ℝ)) := by ring
            rw [this]; exact mul_le_mul_of_nonneg_right hcoef (by positivity)
          nlinarith only [hstep1, h1_lt, hn_ge100, hlog4_lt, hlogn_pos, hε0, hε1]
      _ ≤ Real.log (C_n : ℝ) := hlog_Cn_lb
  · -- Hall-type cubic-square bound: n! = u_n^3 v_n, x_n = u_n v_n, y_n = m v_n
    intro n m hn hm
    let u_n : ℕ := ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p ^ (padicValNat p (Nat.factorial n) / 3)
    let v_n : ℕ := ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p ^ (padicValNat p (Nat.factorial n) % 3)
    have hu_pos : 0 < u_n := Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp hp).2.pos _)
    have hv_pos : 0 < v_n := Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp hp).2.pos _)
    have hfac_uv : Nat.factorial n = u_n ^ 3 * v_n := by
      have hprod_eq : u_n ^ 3 * v_n =
          ∏ p ∈ (Finset.Icc 2 n).filter Nat.Prime, p ^ padicValNat p (Nat.factorial n) := by
        dsimp [u_n, v_n]
        rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl; intro p _
        rw [← pow_mul, ← pow_add, mul_comm, Nat.div_add_mod]
      rw [hprod_eq]
      apply Nat.eq_of_factorization_eq (Nat.factorial_pos n).ne'
        (Finset.prod_pos (fun p hp => pow_pos (Finset.mem_filter.mp hp).2.pos _)).ne'
      intro p
      by_cases hp : p.Prime
      · haveI : Fact p.Prime := ⟨hp⟩
        rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
        by_cases hmem : p ∈ (Finset.Icc 2 n).filter Nat.Prime
        · rw [← Finset.mul_prod_erase _ _ hmem,
            padicValNat.mul (pow_ne_zero _ hp.ne_zero)
              (Finset.prod_pos (fun q hq => pow_pos (Finset.mem_filter.mp (Finset.mem_of_mem_erase hq)).2.pos _)).ne',
            padicValNat.prime_pow]
          have hcop : ¬ p ∣ ∏ q ∈ ((Finset.Icc 2 n).filter Nat.Prime).erase p,
              q ^ padicValNat q (Nat.factorial n) := by
            intro h
            rw [hp.prime.dvd_finset_prod_iff] at h
            obtain ⟨q, hq, hqd⟩ := h
            have hq_pr := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hq)).2
            have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_pr).mp (hp.dvd_of_dvd_pow hqd)
            exact Finset.ne_of_mem_erase hq hpq.symm
          rw [padicValNat.eq_zero_of_not_dvd hcop, add_zero]
        · have hndvd1 : ¬ p ∣ Nat.factorial n := by
            intro h; apply hmem
            exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hp.dvd_factorial.mp h⟩, hp⟩
          have hndvd2 : ¬ p ∣ ∏ q ∈ (Finset.Icc 2 n).filter Nat.Prime, q ^ padicValNat q (Nat.factorial n) := by
            intro h
            rw [hp.prime.dvd_finset_prod_iff] at h
            obtain ⟨q, hq, hqd⟩ := h
            have hq_pr := (Finset.mem_filter.mp hq).2
            have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_pr).mp (hp.dvd_of_dvd_pow hqd)
            exact hmem (hpq ▸ hq)
          rw [padicValNat.eq_zero_of_not_dvd hndvd1, padicValNat.eq_zero_of_not_dvd hndvd2]
      · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]
    have hv_cubefree : ∀ p : ℕ, p.Prime → padicValNat p v_n ≤ 2 := by
      intro p hp
      haveI : Fact p.Prime := ⟨hp⟩
      by_cases hmem : p ∈ (Finset.Icc 2 n).filter Nat.Prime
      · have hprod_val : padicValNat p v_n = padicValNat p (Nat.factorial n) % 3 := by
          dsimp [v_n]
          rw [← Finset.mul_prod_erase _ _ hmem,
            padicValNat.mul (pow_ne_zero _ hp.ne_zero)
              (Finset.prod_pos (fun q hq => pow_pos (Finset.mem_filter.mp (Finset.mem_of_mem_erase hq)).2.pos _)).ne',
            padicValNat.prime_pow]
          have hcop : ¬ p ∣ ∏ q ∈ ((Finset.Icc 2 n).filter Nat.Prime).erase p,
              q ^ (padicValNat q (Nat.factorial n) % 3) := by
            intro h
            rw [hp.prime.dvd_finset_prod_iff] at h
            obtain ⟨q, hq, hqd⟩ := h
            have hq_pr := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hq)).2
            have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_pr).mp (hp.dvd_of_dvd_pow hqd)
            exact Finset.ne_of_mem_erase hq hpq.symm
          rw [padicValNat.eq_zero_of_not_dvd hcop, add_zero]
        rw [hprod_val]; omega
      · have hndvd : ¬ p ∣ v_n := by
          dsimp [v_n]; intro h
          rw [hp.prime.dvd_finset_prod_iff] at h
          obtain ⟨q, hq, hqd⟩ := h
          have hq_pr := (Finset.mem_filter.mp hq).2
          have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_pr).mp (hp.dvd_of_dvd_pow hqd)
          exact hmem (hpq ▸ hq)
        rw [padicValNat.eq_zero_of_not_dvd hndvd]; omega
    refine ⟨u_n, v_n, hu_pos, hv_pos, hfac_uv, hv_cubefree, ?_, by positivity, ?_⟩
    · have h1 : (m * v_n) ^ 2 = (u_n * v_n) ^ 3 + v_n ^ 2 := by
        calc (m * v_n) ^ 2 = m ^ 2 * v_n ^ 2 := by ring
          _ = (Nat.factorial n + 1) * v_n ^ 2 := by rw [← hm]
          _ = (u_n ^ 3 * v_n + 1) * v_n ^ 2 := by rw [hfac_uv]
          _ = (u_n * v_n) ^ 3 + v_n ^ 2 := by ring
      omega
    · have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hlog_v_le : Real.log (v_n : ℝ) ≤ 2 * thetaPrime (n : ℝ) := by
        have hth_eq : thetaPrime (n : ℝ) = ∑ p ∈ (Finset.Icc 2 n).filter Nat.Prime, Real.log (p : ℝ) := by
          unfold thetaPrime; rw [Nat.floor_natCast]
        rw [hth_eq, Finset.mul_sum]
        dsimp [v_n]
        rw [Nat.cast_prod, Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr (pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero))]
        apply Finset.sum_le_sum; intro p hp
        rw [Nat.cast_pow, Real.log_pow]
        have hle2 : ((padicValNat p (Nat.factorial n) % 3 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by omega : padicValNat p (Nat.factorial n) % 3 ≤ 2)
        have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos)
        exact mul_le_mul_of_nonneg_right hle2 hlogp_nn
      have htheta_ub : thetaPrime (n : ℝ) ≤ (1 + ε / 100) * (n : ℝ) := by
        have h := hN_th n (by omega)
        have habs_n : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, habs_n] at h
        linarith [(abs_le.mp h).2]
      have hlog_x_lb : (1 / 3 : ℝ) * ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ)) ≤ Real.log ((u_n * v_n : ℕ) : ℝ) := by
        have hfac_le_x3 : Nat.factorial n ≤ (u_n * v_n) ^ 3 := by
          rw [hfac_uv, mul_pow]
          exact Nat.mul_le_mul_left (u_n ^ 3) (Nat.le_self_pow (by norm_num) v_n)
        have hfac_pos_r : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
        have hfac_le_r : (Nat.factorial n : ℝ) ≤ (((u_n * v_n) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hfac_le_x3
        have h1 := Real.log_le_log hfac_pos_r hfac_le_r
        rw [Nat.cast_pow, Real.log_pow] at h1
        have h2 := (n_log_n_sub_n_le_log_factorial n (by omega : 1 ≤ n)).1
        linarith
      have hil := hN_lg n (by omega)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg zero_le_one hlogn_pos.le)] at hil
      have h1_lt : 1 < (ε / 100) * Real.log (n : ℝ) := (div_lt_iff₀ hlogn_pos).mp hil
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hlog_x_pos : 0 < Real.log ((u_n * v_n : ℕ) : ℝ) := by
        have hlog_gt1 : 1 < Real.log (n : ℝ) := by nlinarith only [h1_lt, hε0, hε1]
        nlinarith only [hlog_x_lb, hn_pos, hlog_gt1]
      rw [div_le_div_iff₀ hlog_x_pos hlogn_pos, Nat.cast_pow, Real.log_pow]
      calc (2 : ℝ) * Real.log (v_n : ℝ) * Real.log (n : ℝ)
          ≤ 2 * (2 * ((1 + ε / 100) * (n : ℝ))) * Real.log (n : ℝ) := by nlinarith only [hlog_v_le, htheta_ub, hlogn_pos]
        _ ≤ (12 + ε) * ((1 / 3 : ℝ) * ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ))) := by
            nlinarith only [h1_lt, hn_pos, hlogn_pos, hε0, hε1]
        _ ≤ (12 + ε) * Real.log ((u_n * v_n : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hlog_x_lb (by linarith only [hε0])

end GrasGreenbergBrocard
