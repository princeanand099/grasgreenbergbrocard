import GrasGreenbergBrocard.Prop6_1FourGCD
import GrasGreenbergBrocard.Prop4_1SmoothBiquad

/-!
# Section 6.2: Consecutive-Index Rigidity and Unconditional Square-Shift Exclusions

This file formalizes **Proposition 6.2(i)–(iii)** of the manuscript:
1. Uniqueness of the `n = 4` boundary collapse `m_{n+1} = n!/2 - 1` (yielding `(4, 5)` and `(5, 11)`).
2. Quarter-factorial equipartition `X, Y, Z, W > 1`, `log T = (1/4) log(n!) + O(log n)` for
   consecutive solutions `(n, n+1)` (`n ≥ 6`), and unconditional exclusion of `(k_n, k_{n+1}) = (2, 2)`
   for all sufficiently large `n`.
3. Unconditional square-shift exclusions: no two solutions `n₁ < n₂` with `P < 4(n₁! + 1)` can
   have `P = t^2`; in particular `(t^2 - 1)! + 1` and `(t^2)! + 1` are never both squares for
   `t ≥ 2`; and quarter-factorial equipartition `log T = (1/4) log((j^2)!) + O(j log j)` holds
   for consecutive squares `n₁ = j^2, n₂ = (j + 1)^2`.
-/

open scoped BigOperators

namespace GrasGreenbergBrocard

set_option maxHeartbeats 800000

private lemma factorial_gt_four_mul_add_two (n : ℕ) (hn : 5 ≤ n) :
    4 * (n + 2) < Nat.factorial n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ k hk ih =>
    rw [Nat.factorial_succ]
    have h1 : 4 * (k + 1 + 2) ≤ (k + 1) * (4 * (k + 2)) := by nlinarith
    have h2 : (k + 1) * (4 * (k + 2)) < (k + 1) * Nat.factorial k :=
      Nat.mul_lt_mul_of_pos_left ih (by omega)
    omega

/-- **Proposition 6.2(i) (Uniqueness of the `n = 4` Boundary Collapse)**:
For `n ≥ 4` and `(n + 1)! + 1 = m₂^2`, we have `m₂ = n! / 2 - 1` if and only if
`n! = 4 * (n + 2)`, whose unique solution in `n ≥ 4` is `n = 4` (with `m₁ = 5, m₂ = 11`). -/
theorem prop_6_2_part1_n4_boundary {n m₂ : ℕ} (hn : 4 ≤ n)
    (hm₂ : Nat.factorial (n + 1) + 1 = m₂ ^ 2) :
    (m₂ = Nat.factorial n / 2 - 1 ↔ Nat.factorial n = 4 * (n + 2)) ∧
    (Nat.factorial n = 4 * (n + 2) ↔ n = 4) := by
  have h2_dvd : 2 ∣ Nat.factorial n := Nat.dvd_factorial (by norm_num) (by omega)
  have hM : 2 * (Nat.factorial n / 2) = Nat.factorial n := Nat.mul_div_cancel' h2_dvd
  have hM_ge : 12 ≤ Nat.factorial n / 2 := by
    have : 24 ≤ Nat.factorial n := by
      calc 24 = Nat.factorial 4 := by norm_num [Nat.factorial]
        _ ≤ Nat.factorial n := Nat.factorial_le hn
    omega
  have hiff1 : m₂ = Nat.factorial n / 2 - 1 ↔ Nat.factorial n = 4 * (n + 2) := by
    constructor
    · intro hm_eq
      rw [hm_eq] at hm₂
      have hm2z : (Nat.factorial (n + 1) : ℤ) + 1 = ((Nat.factorial n / 2 : ℤ) - 1) ^ 2 := by
        zify [show 1 ≤ Nat.factorial n / 2 by omega] at hm₂ ⊢; exact hm₂
      rw [Nat.factorial_succ] at hm2z; push_cast at hm2z
      have hMz : 2 * (Nat.factorial n / 2 : ℤ) = (Nat.factorial n : ℤ) := by exact_mod_cast hM
      have hfac_pos : (0 : ℤ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
      nlinarith
    · intro hfac_eq
      have hm2_sq : m₂ ^ 2 = (Nat.factorial n / 2 - 1) ^ 2 := by
        zify [show 1 ≤ Nat.factorial n / 2 by omega]
        have hm2z : (Nat.factorial (n + 1) : ℤ) + 1 = (m₂ : ℤ) ^ 2 := by exact_mod_cast hm₂
        rw [Nat.factorial_succ] at hm2z; push_cast at hm2z
        have hMz : 2 * (Nat.factorial n / 2 : ℤ) = (Nat.factorial n : ℤ) := by exact_mod_cast hM
        have hfz : (Nat.factorial n : ℤ) = 4 * ((n : ℤ) + 2) := by exact_mod_cast hfac_eq
        nlinarith
      nlinarith
  have hiff2 : Nat.factorial n = 4 * (n + 2) ↔ n = 4 := by
    constructor
    · intro heq
      by_contra hne
      exact absurd heq (ne_of_gt (factorial_gt_four_mul_add_two n (by omega)))
    · intro hn4; subst hn4; norm_num [Nat.factorial]
  exact ⟨hiff1, hiff2⟩

private lemma log_consecutive_equipartition_aux {n m₁ m₂ : ℕ}
    (hn : 6 ≤ n) (hm₁ : Nat.factorial n + 1 = m₁ ^ 2)
    (hm₂ : Nat.factorial (n + 1) + 1 = m₂ ^ 2) :
    let X := X_gcd m₁ m₂; let Y := Y_gcd m₁ m₂
    let Z := Z_gcd m₁ m₂; let W := W_gcd m₁ m₂
    1 < X ∧ 1 < Y ∧ 1 < Z ∧ 1 < W ∧
    ∀ T ∈ ({X, Y, Z, W} : Finset ℕ),
      |Real.log (T : ℝ) - (1 / 4 : ℝ) * Real.log (Nat.factorial n : ℝ)| ≤
        4 * Real.log ((n : ℝ) + 1) := by
  have hlt : n < n + 1 := Nat.lt_succ_self n
  obtain ⟨⟨a, b, c, d⟩, ⟨ha, hb, hc, hd, hab, hcd, _, _, _, _, _, h4sq⟩, _⟩ :=
    prop_6_1_part1_sl2_and_four_squares (by omega) hlt hm₁ hm₂
  rcases h4sq with ⟨hXsq, hYsq, hZsq, hWsq⟩
  set P := P_ratio n (n + 1)
  have hP_eq : P = n + 1 := by
    dsimp [P, P_ratio]
    rw [Nat.factorial_succ, Nat.mul_div_cancel _ (Nat.factorial_pos n)]
  rw [hP_eq] at hab hcd hXsq hYsq hZsq hWsq
  have hab' : a * b = n := by omega
  have ha_le : a ≤ n := le_trans (Nat.le_mul_of_pos_right a hb) hab'.le
  have hb_le : b ≤ n := le_trans (Nat.le_mul_of_pos_left b ha) hab'.le
  have hc_le : c ≤ n + 1 := by nlinarith only [hcd, hc, hd]
  have hd_le : d ≤ n + 1 := by nlinarith only [hcd, hc, hd]
  have hm₁_ge : 27 ≤ m₁ := by
    have h720 : 720 ≤ Nat.factorial n := by
      calc 720 = Nat.factorial 6 := by norm_num [Nat.factorial]
        _ ≤ Nat.factorial n := Nat.factorial_le hn
    nlinarith
  have hm₁_gt_fac : (Nat.factorial n : ℝ) < (m₁ : ℝ) ^ 2 := by
    have : (Nat.factorial n : ℝ) + 1 = (m₁ : ℝ) ^ 2 := by exact_mod_cast hm₁
    linarith
  have hm₂_lt : (m₂ : ℝ) < (n + 1 : ℝ) * (m₁ : ℝ) / 2 := by
    have hm2_sq : (m₂ : ℝ) ^ 2 = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) + 1 := by
      have : Nat.factorial (n + 1) + 1 = m₂ ^ 2 := hm₂
      rw [Nat.factorial_succ] at this
      exact_mod_cast this.symm
    have hm1_sq : (m₁ : ℝ) ^ 2 = (Nat.factorial n : ℝ) + 1 := by exact_mod_cast hm₁.symm
    have hn6r : (6 : ℝ) ≤ n := by exact_mod_cast hn
    have hfac_nn : (0 : ℝ) ≤ Nat.factorial n := Nat.cast_nonneg _
    have hm2_lt_sq : (m₂ : ℝ) ^ 2 < (((n : ℝ) + 1) * (m₁ : ℝ) / 2) ^ 2 := by
      rw [hm2_sq, div_pow, mul_pow, hm1_sq, lt_div_iff₀ (by norm_num)]
      nlinarith only [hn6r, hfac_nn]
    have h2m2 : 2 * (m₂ : ℝ) < ((n : ℝ) + 1) * (m₁ : ℝ) := by
      have hsq2 : (2 * (m₂ : ℝ)) ^ 2 < (((n : ℝ) + 1) * (m₁ : ℝ)) ^ 2 := by linarith
      nlinarith only [hsq2, (Nat.cast_nonneg m₂ : (0 : ℝ) ≤ m₂), (Nat.cast_nonneg m₁ : (0 : ℝ) ≤ m₁), hn6r]
    linarith
  have hX_lb_int : 2 * n * (n + 1) < (n + 1) * m₁ - m₂ - n := by
    have h1 : (2 * n * (n + 1) + n : ℝ) < ((n : ℝ) + 1) * m₁ - m₂ := by
      have hn6r : (6 : ℝ) ≤ n := by exact_mod_cast hn
      have hm1r : (27 : ℝ) ≤ m₁ := by exact_mod_cast hm₁_ge
      have hm₁_big : 4 * (n + 1 : ℝ) + 2 < (m₁ : ℝ) := by
        by_cases hn6 : n = 6
        · subst hn6; norm_num at hm₁_ge ⊢
          have h721 : 721 = m₁ ^ 2 := by simpa [Nat.factorial] using hm₁
          rcases lt_or_ge m₁ 27 with h26 | h27 <;> nlinarith only [h721, h26, h27]
        · have hn7 : 7 ≤ n := by omega
          have hfac_sq_all : ∀ k : ℕ, 7 ≤ k → (4 * k + 6) ^ 2 < Nat.factorial k := by
            intro k hk
            induction k, hk using Nat.le_induction with
            | base => norm_num [Nat.factorial]
            | succ k hk ih =>
              rw [Nat.factorial_succ]
              have h1' : (4 * (k + 1) + 6) ^ 2 ≤ (k + 1) * (4 * k + 6) ^ 2 := by nlinarith only [hk]
              have h2' : (k + 1) * (4 * k + 6) ^ 2 < (k + 1) * Nat.factorial k :=
                Nat.mul_lt_mul_of_pos_left ih (by omega)
              omega
          have hfac_sq : (4 * n + 6) ^ 2 < Nat.factorial n := hfac_sq_all n hn7
          have h42 : (4 * (n + 1 : ℝ) + 2) ^ 2 < (m₁ : ℝ) ^ 2 := by
            have hm1sq : (m₁ : ℝ) ^ 2 = (Nat.factorial n : ℝ) + 1 := by exact_mod_cast hm₁.symm
            have hfac_sqr : ((4 * (n : ℝ) + 6) ^ 2) < (Nat.factorial n : ℝ) := by exact_mod_cast hfac_sq
            linarith only [hm1sq, hfac_sqr]
          nlinarith only [h42, hn6r, hm1r]
      nlinarith only [hm₁_big, hm₂_lt, hn6r]
    have h2 : ((2 * n * (n + 1) + n : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) * m₁ - m₂ := by
      push_cast; exact h1
    have h3 : (2 * n * (n + 1) + n : ℤ) < (n + 1 : ℤ) * m₁ - m₂ := by
      exact_mod_cast h2
    have h4 : m₂ + n + 2 * n * (n + 1) < (n + 1) * m₁ := by
      exact_mod_cast (by linarith only [h3] : (m₂ + n + 2 * n * (n + 1) : ℤ) < (n + 1 : ℤ) * m₁)
    omega
  set X := X_gcd m₁ m₂; set Y := Y_gcd m₁ m₂
  set Z := Z_gcd m₁ m₂; set W := W_gcd m₁ m₂
  have hm2_nn : (0 : ℤ) ≤ m₂ := Nat.cast_nonneg _
  have hX_lb_z : (2 * (n : ℤ) * ((n : ℤ) + 1)) < ((n : ℤ) + 1) * (m₁ : ℤ) - (m₂ : ℤ) - (n : ℤ) := by
    zify [show m₂ + n ≤ (n + 1) * m₁ by omega] at hX_lb_int; exact hX_lb_int
  have hX1 : 1 < X := by
    have h2ac : (a : ℤ) * c ≤ n * (n + 1) := mul_le_mul (by exact_mod_cast ha_le) (by exact_mod_cast hc_le) (by positivity) (by positivity)
    have hX2 : (2 * (a : ℤ) * c) * (X : ℤ) ^ 2 > 2 * (a : ℤ) * c := by linarith only [hXsq, hX_lb_z, h2ac]
    by_contra hle; rw [not_lt] at hle
    have hsq : (X : ℤ) ^ 2 ≤ 1 := by nlinarith only [show (X : ℤ) ≤ 1 by exact_mod_cast hle, show (0 : ℤ) ≤ X by positivity]
    nlinarith only [hX2, hsq, show (0 : ℤ) < 2 * a * c by positivity]
  have hY1 : 1 < Y := by
    have h2ad : (a : ℤ) * d ≤ n * (n + 1) := mul_le_mul (by exact_mod_cast ha_le) (by exact_mod_cast hd_le) (by positivity) (by positivity)
    have hY2 : (2 * (a : ℤ) * d) * (Y : ℤ) ^ 2 > 2 * (a : ℤ) * d := by linarith only [hYsq, hX_lb_z, h2ad]
    by_contra hle; rw [not_lt] at hle
    have hsq : (Y : ℤ) ^ 2 ≤ 1 := by nlinarith only [show (Y : ℤ) ≤ 1 by exact_mod_cast hle, show (0 : ℤ) ≤ Y by positivity]
    nlinarith only [hY2, hsq, show (0 : ℤ) < 2 * a * d by positivity]
  have hZ1 : 1 < Z := by
    have h2bd : (b : ℤ) * d ≤ n * (n + 1) := mul_le_mul (by exact_mod_cast hb_le) (by exact_mod_cast hd_le) (by positivity) (by positivity)
    have hZ2 : (2 * (b : ℤ) * d) * (Z : ℤ) ^ 2 > 2 * (b : ℤ) * d := by linarith only [hZsq, hX_lb_z, h2bd, hm2_nn]
    by_contra hle; rw [not_lt] at hle
    have hsq : (Z : ℤ) ^ 2 ≤ 1 := by nlinarith only [show (Z : ℤ) ≤ 1 by exact_mod_cast hle, show (0 : ℤ) ≤ Z by positivity]
    nlinarith only [hZ2, hsq, show (0 : ℤ) < 2 * b * d by positivity]
  have hW1 : 1 < W := by
    have h2bc : (b : ℤ) * c ≤ n * (n + 1) := mul_le_mul (by exact_mod_cast hb_le) (by exact_mod_cast hc_le) (by positivity) (by positivity)
    have hW2 : (2 * (b : ℤ) * c) * (W : ℤ) ^ 2 > 2 * (b : ℤ) * c := by linarith only [hWsq, hX_lb_z, h2bc, hm2_nn]
    by_contra hle; rw [not_lt] at hle
    have hsq : (W : ℤ) ^ 2 ≤ 1 := by nlinarith only [show (W : ℤ) ≤ 1 by exact_mod_cast hle, show (0 : ℤ) ≤ W by positivity]
    nlinarith only [hW2, hsq, show (0 : ℤ) < 2 * b * c by positivity]
  refine ⟨hX1, hY1, hZ1, hW1, ?_⟩
  have hS_lb : (1 / 2 : ℝ) * ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ) ≤
      ((n : ℝ) + 1) * m₁ - m₂ - n := by
    have hm1_gt_sqrt : Real.sqrt (Nat.factorial n : ℝ) < m₁ := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg m₁)]
      exact Real.sqrt_lt_sqrt (by positivity) hm₁_gt_fac
    have hm2_le2 : (m₂ : ℝ) ≤ (2 / 5 : ℝ) * ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ) := by
      have hn6r : (6 : ℝ) ≤ n := by exact_mod_cast hn
      have hfac_ge : (720 : ℝ) ≤ Nat.factorial n := by
        exact_mod_cast (show 720 ≤ Nat.factorial n by
          calc 720 = Nat.factorial 6 := by norm_num [Nat.factorial]
            _ ≤ Nat.factorial n := Nat.factorial_le hn)
      have hsq : (m₂ : ℝ) ^ 2 ≤ ((2 / 5 : ℝ) * ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ)) ^ 2 := by
        have hm2sq : (m₂ : ℝ) ^ 2 = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) + 1 := by
          have : Nat.factorial (n + 1) + 1 = m₂ ^ 2 := hm₂
          rw [Nat.factorial_succ] at this
          exact_mod_cast this.symm
        rw [hm2sq, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        have h425 : (n : ℝ) + 1 + 1 / 720 ≤ (2 / 5 : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2 := by nlinarith only [hn6r]
        have hmul : ((n : ℝ) + 1 + 1 / 720) * (Nat.factorial n : ℝ) ≤
            (2 / 5 : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2 * (Nat.factorial n : ℝ) :=
          mul_le_mul_of_nonneg_right h425 (Nat.cast_nonneg _)
        linarith only [hmul, hfac_ge]
      rw [← Real.sqrt_sq (Nat.cast_nonneg m₂),
        ← Real.sqrt_sq (by positivity : 0 ≤ (2 / 5 : ℝ) * ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ))]
      exact Real.sqrt_le_sqrt hsq
    have hn_le_tenth : (n : ℝ) ≤ (1 / 10 : ℝ) * ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ) := by
      have hfac_ge : (720 : ℝ) ≤ Nat.factorial n := by
        exact_mod_cast (show 720 ≤ Nat.factorial n by
          calc 720 = Nat.factorial 6 := by norm_num [Nat.factorial]
            _ ≤ Nat.factorial n := Nat.factorial_le hn)
      have h26 : (26 : ℝ) ≤ Real.sqrt (Nat.factorial n : ℝ) := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 26)]
        exact Real.sqrt_le_sqrt (by linarith)
      nlinarith only [h26, (by exact_mod_cast hn : (6 : ℝ) ≤ n)]
    have hm1_gt_sqrt_le : Real.sqrt (Nat.factorial n : ℝ) ≤ m₁ := hm1_gt_sqrt.le
    nlinarith only [hm1_gt_sqrt_le, hm2_le2, hn_le_tenth, (by exact_mod_cast hn : (6 : ℝ) ≤ n)]
  have hS_ub : ((n : ℝ) + 1) * m₁ + m₂ + n ≤ 4 * ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ) := by
    have hm1_le2 : (m₁ : ℝ) ≤ 2 * Real.sqrt (Nat.factorial n : ℝ) := by
      have hfac_ge : (720 : ℝ) ≤ Nat.factorial n := by
        exact_mod_cast (show 720 ≤ Nat.factorial n by
          calc 720 = Nat.factorial 6 := by norm_num [Nat.factorial]
            _ ≤ Nat.factorial n := Nat.factorial_le hn)
      have hsq1 : (m₁ : ℝ) ^ 2 ≤ (2 * Real.sqrt (Nat.factorial n : ℝ)) ^ 2 := by
        have hm1sq : (m₁ : ℝ) ^ 2 = (Nat.factorial n : ℝ) + 1 := by exact_mod_cast hm₁.symm
        rw [mul_pow, Real.sq_sqrt (by positivity), hm1sq]; linarith
      nlinarith only [hsq1, Real.sqrt_nonneg (Nat.factorial n : ℝ), (Nat.cast_nonneg m₁ : (0 : ℝ) ≤ m₁)]
    have hm2_le : (m₂ : ℝ) ≤ ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ) := by
      have hm2sq : (m₂ : ℝ) ^ 2 = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) + 1 := by
        have : Nat.factorial (n + 1) + 1 = m₂ ^ 2 := hm₂
        rw [Nat.factorial_succ] at this
        exact_mod_cast this.symm
      have hn6r : (6 : ℝ) ≤ n := by exact_mod_cast hn
      have hfac_ge : (720 : ℝ) ≤ Nat.factorial n := by
        exact_mod_cast (show 720 ≤ Nat.factorial n by
          calc 720 = Nat.factorial 6 := by norm_num [Nat.factorial]
            _ ≤ Nat.factorial n := Nat.factorial_le hn)
      have hsq : (m₂ : ℝ) ^ 2 ≤ (((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ)) ^ 2 := by
        rw [hm2sq, mul_pow, Real.sq_sqrt (by positivity)]
        have hn1 : (n : ℝ) + 2 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith only [hn6r]
        have hmul : ((n : ℝ) + 2) * (Nat.factorial n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 * (Nat.factorial n : ℝ) :=
          mul_le_mul_of_nonneg_right hn1 (Nat.cast_nonneg _)
        linarith only [hmul, hfac_ge]
      rw [← Real.sqrt_sq (Nat.cast_nonneg m₂),
        ← Real.sqrt_sq (by positivity : 0 ≤ ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ))]
      exact Real.sqrt_le_sqrt hsq
    have hn_le : (n : ℝ) ≤ ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ) := by
      have h1sq : (1 : ℝ) ≤ Real.sqrt (Nat.factorial n : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.factorial_pos n)
      nlinarith only [h1sq, (by exact_mod_cast hn : (6 : ℝ) ≤ n)]
    nlinarith only [hm1_le2, hm2_le, hn_le, (by exact_mod_cast hn : (6 : ℝ) ≤ n)]
  have hbound_generic : ∀ (T k : ℕ), 1 ≤ k → k ≤ 2 * n * (n + 1) → 1 < T →
      (1 / 2 : ℝ) * ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ) ≤ (k : ℝ) * (T : ℝ) ^ 2 →
      (k : ℝ) * (T : ℝ) ^ 2 ≤ 4 * ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ) →
      |Real.log (T : ℝ) - (1 / 4 : ℝ) * Real.log (Nat.factorial n : ℝ)| ≤ 4 * Real.log ((n : ℝ) + 1) := by
    intro T k hk1 hk_ub hT1 hlb hub
    have hn6r : (6 : ℝ) ≤ n := by exact_mod_cast hn
    have hfac_pos : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
    have hT_pos : (0 : ℝ) < T := by positivity
    have hk_pos : (0 : ℝ) < k := by positivity
    have hsqrt_pos : 0 < Real.sqrt (Nat.factorial n : ℝ) := Real.sqrt_pos.mpr hfac_pos
    have hT2_lb : Real.sqrt (Nat.factorial n : ℝ) / (4 * ((n : ℝ) + 1) ^ 2) ≤ (T : ℝ) ^ 2 := by
      have hk_le : (k : ℝ) ≤ 2 * ((n : ℝ) + 1) ^ 2 := by
        have : (k : ℝ) ≤ 2 * n * (n + 1) := by exact_mod_cast hk_ub
        nlinarith
      calc Real.sqrt (Nat.factorial n : ℝ) / (4 * ((n : ℝ) + 1) ^ 2)
          = ((1 / 2 : ℝ) * ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ)) /
              (2 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1)) := by field_simp; ring
        _ ≤ ((1 / 2 : ℝ) * ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ)) / (k : ℝ) := by
            gcongr; nlinarith
        _ ≤ (T : ℝ) ^ 2 := (div_le_iff₀ hk_pos).mpr (by linarith)
    have hT2_ub : (T : ℝ) ^ 2 ≤ 4 * ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ) := by
      have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      calc (T : ℝ) ^ 2 ≤ (k : ℝ) * (T : ℝ) ^ 2 := le_mul_of_one_le_left (by positivity) hk1r
        _ ≤ 4 * ((n : ℝ) + 1) * Real.sqrt (Nat.factorial n : ℝ) := hub
    have hlog_sqrt : Real.log (Real.sqrt (Nat.factorial n : ℝ)) =
        (1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.log_rpow hfac_pos]; try ring
    have hlog_T2_ub : 2 * Real.log (T : ℝ) - (1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ) ≤
        Real.log (4 * ((n : ℝ) + 1)) := by
      have h1 := Real.log_le_log (by positivity) hT2_ub
      rw [Real.log_pow, Nat.cast_ofNat, Real.log_mul (by positivity) hsqrt_pos.ne', hlog_sqrt] at h1
      linarith
    have hlog_T2_lb : -Real.log (4 * ((n : ℝ) + 1) ^ 2) ≤
        2 * Real.log (T : ℝ) - (1 / 2 : ℝ) * Real.log (Nat.factorial n : ℝ) := by
      have h1 := Real.log_le_log (by positivity) hT2_lb
      rw [Real.log_pow, Nat.cast_ofNat, Real.log_div hsqrt_pos.ne' (by positivity), hlog_sqrt] at h1
      linarith
    have h4_le : Real.log (4 * ((n : ℝ) + 1) ^ 2) ≤ 8 * Real.log ((n : ℝ) + 1) := by
      have h4le : (4 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have hlog_n1 : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Nat.cast_ofNat]
      have : Real.log 4 ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by norm_num) h4le
      linarith
    have h4_le1 : Real.log (4 * ((n : ℝ) + 1)) ≤ 8 * Real.log ((n : ℝ) + 1) := by
      have : 4 * ((n : ℝ) + 1) ≤ 4 * ((n : ℝ) + 1) ^ 2 := by nlinarith
      exact le_trans (Real.log_le_log (by positivity) this) h4_le
    rw [abs_le]
    constructor <;> linarith
  intro T hT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  have hm2r_nn : (0 : ℝ) ≤ m₂ := Nat.cast_nonneg m₂
  have hnr_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases hT with rfl | rfl | rfl | rfl
  · refine hbound_generic X (2 * a * c) (by nlinarith only [ha, hc]) (by nlinarith only [ha_le, hc_le]) hX1 ?_ ?_
    · have : ((2 * a * c : ℕ) : ℝ) * (X : ℝ) ^ 2 = ((n : ℝ) + 1) * m₁ - m₂ - n := by exact_mod_cast hXsq
      linarith only [this, hS_lb]
    · have : ((2 * a * c : ℕ) : ℝ) * (X : ℝ) ^ 2 = ((n : ℝ) + 1) * m₁ - m₂ - n := by exact_mod_cast hXsq
      linarith only [this, hS_ub, hm2r_nn, hnr_nn]
  · refine hbound_generic Y (2 * a * d) (by nlinarith only [ha, hd]) (by nlinarith only [ha_le, hd_le]) hY1 ?_ ?_
    · have : ((2 * a * d : ℕ) : ℝ) * (Y : ℝ) ^ 2 = ((n : ℝ) + 1) * m₁ - m₂ + n := by exact_mod_cast hYsq
      linarith only [this, hS_lb, hnr_nn]
    · have : ((2 * a * d : ℕ) : ℝ) * (Y : ℝ) ^ 2 = ((n : ℝ) + 1) * m₁ - m₂ + n := by exact_mod_cast hYsq
      linarith only [this, hS_ub, hm2r_nn]
  · refine hbound_generic Z (2 * b * d) (by nlinarith only [hb, hd]) (by nlinarith only [hb_le, hd_le]) hZ1 ?_ ?_
    · have : ((2 * b * d : ℕ) : ℝ) * (Z : ℝ) ^ 2 = ((n : ℝ) + 1) * m₁ + m₂ - n := by exact_mod_cast hZsq
      linarith only [this, hS_lb, hm2r_nn]
    · have : ((2 * b * d : ℕ) : ℝ) * (Z : ℝ) ^ 2 = ((n : ℝ) + 1) * m₁ + m₂ - n := by exact_mod_cast hZsq
      linarith only [this, hS_ub, hnr_nn]
  · refine hbound_generic W (2 * b * c) (by nlinarith only [hb, hc]) (by nlinarith only [hb_le, hc_le]) hW1 ?_ ?_
    · have : ((2 * b * c : ℕ) : ℝ) * (W : ℝ) ^ 2 = ((n : ℝ) + 1) * m₁ + m₂ + n := by exact_mod_cast hWsq
      linarith only [this, hS_lb, hm2r_nn, hnr_nn]
    · have : ((2 * b * c : ℕ) : ℝ) * (W : ℝ) ^ 2 = ((n : ℝ) + 1) * m₁ + m₂ + n := by exact_mod_cast hWsq
      linarith only [this, hS_ub]

private lemma k_eq_2_AB {n m X₁ Y₁ : ℕ} (hn : 4 ≤ n) (hn6 : n ≠ 6)
    (hm : Nat.factorial n + 1 = m ^ 2) (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hk2 : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2) :
    A_sol m = q_n n * Y₁ ^ 2 ∧ B_sol m = X₁ ^ 2 := by
  have h1 : (m : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) =
      ((X₁ : ℝ) ^ 2 + (q_n n : ℝ) * (Y₁ : ℝ) ^ 2) +
      (2 * (X₁ : ℝ) * (Y₁ : ℝ)) * Real.sqrt (q_n n : ℝ) := by
    rw [hk2]; unfold pellUnit; push_cast; ring_nf; rw [Real.sq_sqrt (by positivity)]
  have hq_nsq : ¬ IsSquare (q_n n) := by
    intro ⟨r, hr⟩
    have hq2 : 2 ≤ q_n n := q_n_ge_two (by omega)
    have hr2 : 2 ≤ r := by nlinarith
    obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd (by omega : r ≠ 1)
    exact (Nat.squarefree_iff_prime_squarefree.mp (q_n_squarefree n)) p hp (by rw [hr]; exact mul_dvd_mul hpr hpr)
  have hirr : Irrational (Real.sqrt (q_n n : ℝ)) := irrational_sqrt_natCast_iff.mpr hq_nsq
  have hm_nat : m = X₁ ^ 2 + q_n n * Y₁ ^ 2 := by
    have hdiff : ((m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2) : ℤ) =
        ((2 * (X₁ : ℤ) * (Y₁ : ℤ) - (s_n n : ℤ)) : ℤ) * Real.sqrt (q_n n : ℝ) := by
      push_cast; linarith
    by_contra hne
    have hne_z : ((m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2)) ≠ 0 := by
      intro h0; apply hne; exact_mod_cast sub_eq_zero.mp h0
    have hco_nz : (2 * (X₁ : ℝ) * (Y₁ : ℝ) - (s_n n : ℝ)) ≠ 0 := by
      intro h0
      have hdiff' : ((m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2) : ℤ) =
          (2 * (X₁ : ℝ) * (Y₁ : ℝ) - (s_n n : ℝ)) * Real.sqrt (q_n n : ℝ) := by
        push_cast at hdiff ⊢; exact hdiff
      rw [h0, zero_mul] at hdiff'
      exact hne_z (by exact_mod_cast hdiff')
    let a_z : ℤ := (m : ℤ) - ((X₁ : ℤ) ^ 2 + (q_n n : ℤ) * (Y₁ : ℤ) ^ 2)
    let b_z : ℤ := 2 * (X₁ : ℤ) * (Y₁ : ℤ) - (s_n n : ℤ)
    have hrat : Real.sqrt (q_n n : ℝ) = (a_z : ℝ) / (b_z : ℝ) := by
      have hco_z : (b_z : ℝ) ≠ 0 := by push_cast [b_z]; exact hco_nz
      rw [eq_div_iff hco_z]
      push_cast [a_z, b_z] at hdiff ⊢
      linarith [hdiff]
    exact hirr ⟨(a_z : ℚ) / (b_z : ℚ), by push_cast; exact hrat.symm⟩
  have hpell := hfund.2.2.1
  have hm1_ge : 1 ≤ m := by nlinarith [hfund.1]
  have hm_sub : m - 1 = 2 * q_n n * Y₁ ^ 2 := by zify [hm1_ge] at hpell ⊢; linarith
  have hm_add : m + 1 = 2 * X₁ ^ 2 := by zify [show 1 ≤ X₁ ^ 2 by nlinarith [hfund.1]] at hpell ⊢; linarith
  constructor
  · change (m - 1) / 2 = q_n n * Y₁ ^ 2; omega
  · change (m + 1) / 2 = X₁ ^ 2; omega

/-- **Proposition 6.2(ii) (Quarter-Factorial Equipartition and Exclusion of `(k_n, k_{n+1}) = (2, 2)`)**:
For consecutive solutions `(n, m₁)` and `(n + 1, m₂)` with `n ≥ 6`:
1. `X, Y, Z, W > 1` and `|log T - (1/4) log(n!)| ≤ 4 log(n + 1)` for `T ∈ {X, Y, Z, W}`.
2. For all sufficiently large `n`, `(k_n, k_{n+1}) ≠ (2, 2)`. -/
theorem prop_6_2_part2_consecutive_equipartition :
    (∀ n m₁ m₂ : ℕ, 6 ≤ n → Nat.factorial n + 1 = m₁ ^ 2 →
      Nat.factorial (n + 1) + 1 = m₂ ^ 2 →
      let X := X_gcd m₁ m₂; let Y := Y_gcd m₁ m₂
      let Z := Z_gcd m₁ m₂; let W := W_gcd m₁ m₂
      1 < X ∧ 1 < Y ∧ 1 < Z ∧ 1 < W ∧
      ∀ T ∈ ({X, Y, Z, W} : Finset ℕ),
        |Real.log (T : ℝ) - (1 / 4 : ℝ) * Real.log (Nat.factorial n : ℝ)| ≤
          4 * Real.log ((n : ℝ) + 1)) ∧
    (∃ N₀ : ℕ, 8 ≤ N₀ ∧ ∀ n m₁ m₂ X₁ Y₁ X₂ Y₂ : ℕ, N₀ ≤ n →
      Nat.factorial n + 1 = m₁ ^ 2 → Nat.factorial (n + 1) + 1 = m₂ ^ 2 →
      IsFundamentalPell (q_n n) X₁ Y₁ →
      IsFundamentalPell (q_n (n + 1)) X₂ Y₂ →
      ¬ ((m₁ : ℝ) + (s_n n : ℝ) * Real.sqrt (q_n n : ℝ) = (pellUnit (q_n n) X₁ Y₁) ^ 2 ∧
         (m₂ : ℝ) + (s_n (n + 1) : ℝ) * Real.sqrt (q_n (n + 1) : ℝ) =
           (pellUnit (q_n (n + 1)) X₂ Y₂) ^ 2)) := by
  refine ⟨fun n m₁ m₂ hn hm₁ hm₂ => log_consecutive_equipartition_aux hn hm₁ hm₂, ?_⟩
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (Asymptotics.IsLittleO.bound S_odd_asymptotic (show (0 : ℝ) < 1 / 20 by norm_num))
  obtain ⟨C_mert, hC_mert_pos, hMert⟩ := Mertens_div_p_band_le
  have hloglog : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 (by norm_num)
    exact (h1.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    (hloglog.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < 1 / 200 by norm_num)))
  have hlog_div : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / ((n : ℝ) * Real.log (n : ℝ)))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (2 * Real.log (n : ℝ)) / ((n : ℝ) * Real.log (n : ℝ)))
        Filter.atTop (nhds 0) := by
      have : ∀ᶠ n : ℕ in Filter.atTop, (2 * Real.log (n : ℝ)) / ((n : ℝ) * Real.log (n : ℝ)) = 2 / (n : ℝ) := by
        filter_upwards [Filter.eventually_ge_atTop 3] with n hn
        have hlog0 : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
        field_simp [hlog0]
      exact (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).congr'
        (Filter.Eventually.mono this (fun _ h => h.symm))
    refine squeeze_zero' ?_ ?_ h1
    · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n + 1))) (by positivity)
    · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
      gcongr
      have : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by
        have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      calc Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by positivity) this
        _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp
    (hlog_div.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < 1 / 400 by norm_num)))
  have hinvlog : Filter.Tendsto (fun n : ℕ => (2 * Real.log ((n : ℝ) + 1)) / (Real.log (n : ℝ)) ^ 2)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => 4 / Real.log (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    refine squeeze_zero' ?_ ?_ h1
    · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
      exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n + 1)))) (sq_nonneg _)
    · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
      have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hle : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
        have : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by
          have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith
        calc Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by positivity) this
          _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
      calc 2 * Real.log ((n : ℝ) + 1) / (Real.log (n : ℝ)) ^ 2
          ≤ 2 * (2 * Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 2 := by gcongr
        _ = 4 / Real.log (n : ℝ) := by field_simp [hlog_pos.ne']; ring
  obtain ⟨N₄, hN₄⟩ := Filter.eventually_atTop.mp
    (hinvlog.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < 1 / 40 by norm_num)))
  have hconst_div : Filter.Tendsto (fun n : ℕ => (2 * (C_mert + 1)) / Real.log (n : ℝ))
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₅, hN₅⟩ := Filter.eventually_atTop.mp
    (hconst_div.eventually (Metric.ball_mem_nhds 0 (show (0 : ℝ) < 1 / 200 by norm_num)))
  let N₀ := max (max (max N₁ N₂) (max N₃ N₄)) (max N₅ 1000)
  refine ⟨N₀, by omega, ?_⟩
  intro n m₁ m₂ X₁ Y₁ X₂ Y₂ hn hm₁ hm₂ hfund₁ hfund₂ ⟨hk₁, hk₂⟩
  have hn6 : 6 ≤ n := by omega
  have hlt : n < n + 1 := Nat.lt_succ_self n
  have hEquip := log_consecutive_equipartition_aux hn6 hm₁ hm₂
  have hX_ub : Real.log (X_gcd m₁ m₂ : ℝ) ≤
      (1 / 4 : ℝ) * Real.log (Nat.factorial n : ℝ) + 4 * Real.log ((n : ℝ) + 1) := by
    have := hEquip.2.2.2.2 (X_gcd m₁ m₂) (by simp)
    linarith [(abs_le.mp this).2]
  have hfac_ub : Real.log (Nat.factorial n : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    have hle : Nat.factorial n ≤ n ^ n := Nat.factorial_le_pow n
    have h1 : Real.log (Nat.factorial n : ℝ) ≤ Real.log ((n : ℝ) ^ n) :=
      Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) (by exact_mod_cast hle)
    rwa [Real.log_pow] at h1
  have hSodd_lb : (0.45 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤ S_odd n := by
    have h1 := hN₁ n (by omega)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h1
    have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hnn : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by positivity
    rw [abs_of_nonneg hnn] at h1
    linarith [(abs_le.mp h1).1]
  have ⟨hX_pos, _, _, _, _, _, _, _, _, _, hA₁_eq, _, _⟩ :=
    prop_6_1_coprime_and_factorization (by omega) hlt hm₁ hm₂
  have ⟨hA₁_val, _⟩ := k_eq_2_AB (by omega) (by omega) hm₁ hfund₁ hk₁
  have ⟨hA₂_val, _⟩ := k_eq_2_AB (by omega) (by omega) hm₂ hfund₂ hk₂
  obtain ⟨⟨a, b, c, d⟩, hprop, _⟩ :=
    prop_6_1_part1_sl2_and_four_squares (by omega) hlt hm₁ hm₂
  rcases hprop with ⟨_, _, _, _, _, _, _, hB₂_eq, _, _, _, _⟩
  have h4mul1 : 4 * A_sol m₁ * B_sol m₁ = Nat.factorial n :=
    (brocard_u1_u2_rel (by omega) hm₁).2.2.2.2.1
  have hcop1 : Nat.Coprime (A_sol m₁) (B_sol m₁) :=
    (brocard_u1_u2_rel (by omega) hm₁).2.2.2.1
  have hcop2 : Nat.Coprime (A_sol m₂) (B_sol m₂) :=
    (brocard_u1_u2_rel (by omega) hm₂).2.2.2.1
  let S_good := (Podd n).filter (fun p => 3 ≤ p ∧ ¬ p ∣ n + 1)
  let S_bad := (Podd n).filter (fun p => 3 ≤ p ∧ p ∣ n + 1)
  have hdvd_each : ∀ p ∈ S_good, p ^ padicValNat p (Nat.factorial n) ∣ X_gcd m₁ m₂ := by
    intro p hp
    simp only [S_good, Finset.mem_filter] at hp
    have hp_prime : p.Prime := by have h := hp.1; simp [Podd] at h; exact h.2.1
    have hp2 : p ≠ 2 := by omega
    have hndvd_n1 : ¬ p ∣ n + 1 := hp.2.2
    have hp_odd1 : ¬ 2 ∣ padicValNat p (Nat.factorial n) := by have h := hp.1; simp [Podd] at h; omega
    have hp_odd2 : ¬ 2 ∣ padicValNat p (Nat.factorial (n + 1)) := by
      haveI : Fact p.Prime := ⟨hp_prime⟩
      rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_pos n).ne']
      have hv0 : padicValNat p (n + 1) = 0 := padicValNat.eq_zero_of_not_dvd hndvd_n1
      rw [hv0, zero_add]; exact hp_odd1
    have hp_q1 : p ∣ q_n n := Finset.dvd_prod_of_mem _ hp.1
    have hp_mem2 : p ∈ Podd (n + 1) := by
      have h := hp.1; simp only [Podd, Finset.mem_filter, Finset.mem_Icc] at h ⊢
      exact ⟨⟨h.1.1, by omega⟩, hp_prime, hp_odd2⟩
    have hp_q2 : p ∣ q_n (n + 1) := Finset.dvd_prod_of_mem _ hp_mem2
    have hp_A1 : p ∣ A_sol m₁ := hA₁_val ▸ dvd_mul_of_dvd_left hp_q1 _
    have hp_A2 : p ∣ A_sol m₂ := hA₂_val ▸ dvd_mul_of_dvd_left hp_q2 _
    have hp_nB2 : ¬ p ∣ B_sol m₂ := fun h => hp_prime.not_dvd_one (hcop2 ▸ Nat.dvd_gcd hp_A2 h)
    have hp_nZ : ¬ p ∣ Z_gcd m₁ m₂ := by
      intro hZ; apply hp_nB2; rw [hB₂_eq]; exact dvd_mul_of_dvd_right hZ _
    have hp_pow_fac : p ^ padicValNat p (Nat.factorial n) ∣ Nat.factorial n := pow_padicValNat_dvd
    have hp_pow_A1B1 : p ^ padicValNat p (Nat.factorial n) ∣ A_sol m₁ * B_sol m₁ := by
      have hcop4 : Nat.Coprime (p ^ padicValNat p (Nat.factorial n)) 4 := by
        apply Nat.Coprime.pow_left
        exact hp_prime.coprime_iff_not_dvd.mpr (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp (hp_prime.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h))))
      have hp_pow_4AB : p ^ padicValNat p (Nat.factorial n) ∣ 4 * (A_sol m₁ * B_sol m₁) := by
        rw [← mul_assoc, h4mul1]; exact hp_pow_fac
      exact hcop4.dvd_of_dvd_mul_left hp_pow_4AB
    have hp_nB1 : ¬ p ∣ B_sol m₁ := fun h => hp_prime.not_dvd_one (hcop1 ▸ Nat.dvd_gcd hp_A1 h)
    have hp_pow_A1 : p ^ padicValNat p (Nat.factorial n) ∣ A_sol m₁ :=
      (Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hp_nB1)).dvd_of_dvd_mul_right hp_pow_A1B1
    rw [hA₁_eq] at hp_pow_A1
    exact (Nat.Coprime.pow_left _ (hp_prime.coprime_iff_not_dvd.mpr hp_nZ)).dvd_of_dvd_mul_right hp_pow_A1
  have hdvd_X : ∏ p ∈ S_good, p ^ padicValNat p (Nat.factorial n) ∣ X_gcd m₁ m₂ := by
    have hcop_each : ∀ p ∈ S_good, ∀ q ∈ S_good, p ≠ q →
        Nat.Coprime (p ^ padicValNat p (Nat.factorial n)) (q ^ padicValNat q (Nat.factorial n)) := by
      intro p hp q hq hpq
      simp only [S_good, Finset.mem_filter] at hp hq
      have hp_pr : p.Prime := by have h := hp.1; simp [Podd] at h; exact h.2.1
      have hq_pr : q.Prime := by have h := hq.1; simp [Podd] at h; exact h.2.1
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp_pr hq_pr).mpr hpq)
    have hprod_dvd : ∀ s : Finset ℕ, (∀ p ∈ s, p ^ padicValNat p (Nat.factorial n) ∣ X_gcd m₁ m₂) →
        (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Nat.Coprime (p ^ padicValNat p (Nat.factorial n)) (q ^ padicValNat q (Nat.factorial n))) →
        ∏ p ∈ s, p ^ padicValNat p (Nat.factorial n) ∣ X_gcd m₁ m₂ := by
      intro s hs hcs
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha]
        have hcop_a : Nat.Coprime (a ^ padicValNat a (Nat.factorial n)) (∏ p ∈ s, p ^ padicValNat p (Nat.factorial n)) :=
          Nat.Coprime.prod_right fun q hq => hcs a (Finset.mem_insert_self a s) q (Finset.mem_insert_of_mem hq) (fun h => ha (h ▸ hq))
        exact hcop_a.mul_dvd_of_dvd_of_dvd (hs a (Finset.mem_insert_self a s))
          (ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
              (fun p hp q hq hpq => hcs p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq) hpq))
    exact hprod_dvd S_good hdvd_each hcop_each
  have hlog_prod : ∑ p ∈ S_good, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
      Real.log (X_gcd m₁ m₂ : ℝ) := by
    have hpos_prod : 0 < ∏ p ∈ S_good, p ^ padicValNat p (Nat.factorial n) := by
      apply Finset.prod_pos; intro p hp
      simp only [S_good, Finset.mem_filter] at hp; exact pow_pos (by omega : 0 < p) _
    have hle := Real.log_le_log
      (show (0 : ℝ) < ↑(∏ p ∈ S_good, p ^ padicValNat p (Nat.factorial n)) by exact_mod_cast hpos_prod)
      (show (↑(∏ p ∈ S_good, p ^ padicValNat p (Nat.factorial n)) : ℝ) ≤ ↑(X_gcd m₁ m₂) by exact_mod_cast Nat.le_of_dvd hX_pos hdvd_X)
    rw [Nat.cast_prod, Real.log_prod] at hle
    · refine le_trans ?_ hle
      apply le_of_eq; apply Finset.sum_congr rfl; intro p _; rw [Nat.cast_pow, Real.log_pow]
    · intro p hp; simp only [S_good, Finset.mem_filter] at hp; exact_mod_cast pow_ne_zero (padicValNat p (Nat.factorial n)) (by omega : p ≠ 0)
  have hS_split : S_odd n =
      (∑ p ∈ S_good, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) +
      (∑ p ∈ S_bad, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)) := by
    unfold S_odd
    have hdisj : Disjoint S_good S_bad := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      simp only [S_good, S_bad, Finset.mem_filter] at hp1 hp2
      exact hp1.2.2 hp2.2.2
    have hunion : (Podd n).filter (fun p => 3 ≤ p) = S_good ∪ S_bad := by
      ext p; simp only [Finset.mem_filter, Finset.mem_union, S_good, S_bad]; tauto
    rw [hunion, Finset.sum_union hdisj]
  have hS_bad_ub : ∑ p ∈ S_bad, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
      0.05 * (n : ℝ) * Real.log (n : ℝ) := by
    let S_bad_le := S_bad.filter (fun (p : ℕ) => (p : ℝ) ≤ Real.log (n : ℝ))
    let S_bad_gt := S_bad.filter (fun (p : ℕ) => Real.log (n : ℝ) < (p : ℝ))
    have hsplit_bad : S_bad = S_bad_le ∪ S_bad_gt := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter, S_bad_le, S_bad_gt]; constructor
      · intro h; by_cases hle : (p : ℝ) ≤ Real.log (n : ℝ); exact Or.inl ⟨h, hle⟩; exact Or.inr ⟨h, lt_of_not_ge hle⟩
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hdisj_bad : Disjoint S_bad_le S_bad_gt := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      simp only [Finset.mem_filter, S_bad_le, S_bad_gt] at hp1 hp2; linarith
    rw [hsplit_bad, Finset.sum_union hdisj_bad]
    have hlog_n_ge : 3 ≤ Real.log (n : ℝ) := by
      have h1000 : (1000 : ℝ) ≤ n := by exact_mod_cast (by omega : 1000 ≤ n)
      have he3 : Real.exp 3 < 1000 := by
        have := Real.exp_one_lt_d9
        calc Real.exp 3 = Real.exp (1 + 1 + 1) := by norm_num
          _ = Real.exp 1 * Real.exp 1 * Real.exp 1 := by rw [Real.exp_add, Real.exp_add]
          _ < 2.72 * 2.72 * 2.72 := by gcongr <;> linarith
          _ < 1000 := by norm_num
      exact (Real.le_log_iff_exp_le (by positivity)).mpr (le_trans he3.le h1000)
    have hle_sum : ∑ p ∈ S_bad_le, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
        (n : ℝ) * ((2 : ℝ) * (Real.log (Real.log (n : ℝ)) + C_mert + 1)) := by
      have hterm : ∀ p ∈ S_bad_le, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
          (n : ℝ) * (2 * (Real.log (p : ℝ) / (p : ℝ))) := by
        intro p hp
        simp only [S_bad_le, S_bad, Finset.mem_filter] at hp
        have hp_prime : p.Prime := by have h := hp.1.1; simp [Podd] at h; exact h.2.1
        have hp3 : 3 ≤ p := hp.1.2.1
        haveI : Fact p.Prime := ⟨hp_prime⟩
        have hleg : (p - 1) * padicValNat p (Nat.factorial n) ≤ n := by
          have := sub_one_mul_padicValNat_factorial (p := p) n
          exact le_trans this.le (Nat.sub_le n _)
        have h1r : (padicValNat p (Nat.factorial n) : ℝ) * ((p : ℝ) - 1) ≤ (n : ℝ) := by
          have h1n : (padicValNat p (Nat.factorial n) : ℝ) * ((p - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast (by linarith : padicValNat p (Nat.factorial n) * (p - 1) ≤ n)
          rwa [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at h1n
        have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        have hv : (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) :=
          (le_div_iff₀ (by linarith)).mpr h1r
        have hp_half : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
        have hv2 : (padicValNat p (Nat.factorial n) : ℝ) ≤ 2 * (n : ℝ) / (p : ℝ) := by
          calc (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := hv
            _ ≤ (n : ℝ) / ((p : ℝ) / 2) := by gcongr
            _ = 2 * (n : ℝ) / (p : ℝ) := by ring
        have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
        calc (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ)
            ≤ (2 * (n : ℝ) / (p : ℝ)) * Real.log (p : ℝ) := by gcongr
          _ = (n : ℝ) * (2 * (Real.log (p : ℝ) / (p : ℝ))) := by ring
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      gcongr
      have hsub : S_bad_le ⊆ {3} ∪ ((Finset.Icc 3 (Nat.floor (Real.log (n : ℝ)))).filter Nat.Prime).filter
          (fun p : ℕ => (3 : ℝ) < (p : ℝ)) := by
        intro p hp
        simp only [S_bad_le, S_bad, Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc] at hp ⊢
        by_cases hp3 : p = 3
        · exact Or.inl hp3
        · have hp_pr : p.Prime := by have h := hp.1.1; simp [Podd] at h; exact h.2.1
          exact Or.inr ⟨⟨⟨hp.1.2.1, Nat.le_floor hp.2⟩, hp_pr⟩, by exact_mod_cast (by omega : 3 < p)⟩
      have hsum_mert : ∑ p ∈ S_bad_le, Real.log (p : ℝ) / (p : ℝ) ≤
          ∑ p ∈ ({3} ∪ ((Finset.Icc 3 (Nat.floor (Real.log (n : ℝ)))).filter Nat.Prime).filter
            (fun p : ℕ => (3 : ℝ) < (p : ℝ))), Real.log (p : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
      have hmert := hMert 3 (Real.log (n : ℝ)) (le_refl 3) hlog_n_ge
      have h3_val : Real.log (3 : ℝ) / (3 : ℝ) ≤ 1 := by
        have : Real.log (3 : ℝ) ≤ 3 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
        linarith
      calc ∑ p ∈ S_bad_le, Real.log (p : ℝ) / (p : ℝ)
          ≤ ∑ p ∈ ({3} ∪ ((Finset.Icc 3 (Nat.floor (Real.log (n : ℝ)))).filter Nat.Prime).filter
              (fun p : ℕ => (3 : ℝ) < (p : ℝ))), Real.log (p : ℝ) / (p : ℝ) := hsum_mert
        _ ≤ (Real.log (3 : ℝ) / (3 : ℝ)) + (Real.log (Real.log (n : ℝ) / 3) + C_mert) := by
            rw [Finset.sum_union]
            · simp only [Finset.sum_singleton]; linarith
            · rw [Finset.disjoint_singleton_left]; simp
        _ ≤ 1 + (Real.log (Real.log (n : ℝ)) + C_mert) := by
            have : Real.log (Real.log (n : ℝ) / 3) ≤ Real.log (Real.log (n : ℝ)) := by
              apply Real.log_le_log (by linarith); linarith
            linarith
        _ = Real.log (Real.log (n : ℝ)) + C_mert + 1 := by ring
    have hgt_sum : ∑ p ∈ S_bad_gt, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
        (2 * (n : ℝ) / Real.log (n : ℝ)) * Real.log ((n : ℝ) + 1) := by
      have hterm : ∀ p ∈ S_bad_gt, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
          (2 * (n : ℝ) / Real.log (n : ℝ)) * Real.log (p : ℝ) := by
        intro p hp
        simp only [S_bad_gt, S_bad, Finset.mem_filter] at hp
        have hp_prime : p.Prime := by have h := hp.1.1; simp [Podd] at h; exact h.2.1
        have hp3 : 3 ≤ p := hp.1.2.1
        haveI : Fact p.Prime := ⟨hp_prime⟩
        have h1 : padicValNat p (Nat.factorial n) * (p - 1) ≤ n := by
          rw [mul_comm]
          exact le_trans (sub_one_mul_padicValNat_factorial (p := p) n).le (Nat.sub_le n _)
        have h1r : (padicValNat p (Nat.factorial n) : ℝ) * ((p : ℝ) - 1) ≤ (n : ℝ) := by
          have h1n : (padicValNat p (Nat.factorial n) : ℝ) * ((p - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
          rwa [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at h1n
        have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        have h2 : (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) :=
          (le_div_iff₀ (by linarith)).mpr h1r
        have hp_half : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
        have hv : (padicValNat p (Nat.factorial n) : ℝ) ≤ 2 * (n : ℝ) / (p : ℝ) := by
          calc (padicValNat p (Nat.factorial n) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := h2
            _ ≤ (n : ℝ) / ((p : ℝ) / 2) := by gcongr
            _ = 2 * (n : ℝ) / (p : ℝ) := by ring
        have hv_log : (padicValNat p (Nat.factorial n) : ℝ) ≤ 2 * (n : ℝ) / Real.log (n : ℝ) :=
          le_trans hv (div_le_div_of_nonneg_left (by positivity) (by linarith) hp.2.le)
        have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
        exact mul_le_mul_of_nonneg_right hv_log hlogp_nn
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.mul_sum]
      gcongr
      have hdvd_prod : ∏ p ∈ S_bad_gt, p ∣ n + 1 := by
        apply Finset.prod_primes_dvd
        · intro p hp
          simp only [S_bad_gt, S_bad, Finset.mem_filter] at hp
          have hp_pr : p.Prime := by have h := hp.1.1; simp [Podd] at h; exact h.2.1
          exact hp_pr.prime
        · intro p hp; simp only [S_bad_gt, S_bad, Finset.mem_filter] at hp; exact hp.1.2.2
      have hpos_prod : 0 < ∏ p ∈ S_bad_gt, p := by
        apply Finset.prod_pos; intro p hp
        simp only [S_bad_gt, S_bad, Finset.mem_filter] at hp; have := hp.1.2.1; omega
      have hle_n1 : ((∏ p ∈ S_bad_gt, p : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast Nat.le_of_dvd (by omega) hdvd_prod
      have hlog_le := Real.log_le_log (show (0 : ℝ) < ↑(∏ p ∈ S_bad_gt, p) by exact_mod_cast hpos_prod) hle_n1
      rw [Nat.cast_prod, Real.log_prod] at hlog_le
      · exact hlog_le
      · intro p hp; simp only [S_bad_gt, S_bad, Finset.mem_filter] at hp; exact_mod_cast (by have := hp.1.2.1; omega : p ≠ 0)
    have hlog_n_pos : 0 < Real.log (n : ℝ) := by linarith
    have h1_ball : Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) < 1 / 200 := by
      have := hN₂ n (by omega)
      have hll_nn : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg (by linarith)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hll_nn hlog_n_pos.le)] at this; exact this
    have h2_ball : 2 * Real.log ((n : ℝ) + 1) / (Real.log (n : ℝ)) ^ 2 < 1 / 40 := by
      have := hN₄ n (by omega)
      have hln1_nn : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hln1_nn) (sq_nonneg _))] at this; exact this
    have h5_ball : 2 * (C_mert + 1) / Real.log (n : ℝ) < 1 / 200 := by
      have := hN₅ n (by omega)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (by linarith [hC_mert_pos]) hlog_n_pos.le)] at this; exact this
    have hA : (n : ℝ) * (2 * (Real.log (Real.log (n : ℝ)) + C_mert + 1)) ≤ 0.025 * (n : ℝ) * Real.log (n : ℝ) := by
      have h1 : 2 * Real.log (Real.log (n : ℝ)) ≤ 0.01 * Real.log (n : ℝ) := by
        have := (div_lt_iff₀ hlog_n_pos).mp h1_ball; linarith
      have h2 : 2 * (C_mert + 1) ≤ 0.005 * Real.log (n : ℝ) := by
        have := (div_lt_iff₀ hlog_n_pos).mp h5_ball; linarith
      have : 2 * (Real.log (Real.log (n : ℝ)) + C_mert + 1) ≤ 0.025 * Real.log (n : ℝ) := by linarith
      nlinarith [show (0 : ℝ) ≤ n by positivity]
    have hB : (2 * (n : ℝ) / Real.log (n : ℝ)) * Real.log ((n : ℝ) + 1) ≤ 0.025 * (n : ℝ) * Real.log (n : ℝ) := by
      have h1 : 2 * Real.log ((n : ℝ) + 1) ≤ (1 / 40 : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
        have := (div_lt_iff₀ (sq_pos_of_pos hlog_n_pos)).mp h2_ball; linarith
      calc (2 * (n : ℝ) / Real.log (n : ℝ)) * Real.log ((n : ℝ) + 1)
          = ((n : ℝ) / Real.log (n : ℝ)) * (2 * Real.log ((n : ℝ) + 1)) := by ring
        _ ≤ ((n : ℝ) / Real.log (n : ℝ)) * ((1 / 40 : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
            gcongr
        _ = 0.025 * (n : ℝ) * Real.log (n : ℝ) := by field_simp [hlog_n_pos.ne']; ring
    linarith
  have hn_log_pos : (0 : ℝ) < (n : ℝ) * Real.log (n : ℝ) := by
    have : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    positivity
  have hlog_div_small : 4 * Real.log ((n : ℝ) + 1) ≤ 0.01 * (n : ℝ) * Real.log (n : ℝ) := by
    have := hN₃ n (by omega)
    have hlog_n1_nn : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hlog_n1_nn hn_log_pos.le)] at this
    have h1 := (div_lt_iff₀ hn_log_pos).mp this
    linarith
  have hS_good_le : ∑ p ∈ S_good, (padicValNat p (Nat.factorial n) : ℝ) * Real.log (p : ℝ) ≤
      0.25 * (n : ℝ) * Real.log (n : ℝ) + 0.01 * (n : ℝ) * Real.log (n : ℝ) := by
    linarith
  linarith

/-- **Proposition 6.2(iii) (Unconditional Square-Shift Exclusions)**:
1. No two solutions `4 ≤ n₁ < n₂` with `P = n₂!/n₁! < 4(n₁! + 1)` can have `P = t^2`.
2. In particular, for every `t ≥ 2`, `(t^2 - 1)! + 1` and `(t^2)! + 1` can never both be squares.
3. For consecutive squares `n₁ = j^2` and `n₂ = (j + 1)^2` (`j ≥ 3`), every `T ∈ {X, Y, Z, W}`
   satisfies `|log T - (1/4) log((j^2)!)| ≤ 12 * j * log(j + 1)`. -/
theorem prop_6_2_part3_square_shift_exclusions :
    (∀ n₁ n₂ m₁ m₂ t : ℕ, 4 ≤ n₁ → n₁ < n₂ →
      Nat.factorial n₁ + 1 = m₁ ^ 2 → Nat.factorial n₂ + 1 = m₂ ^ 2 →
      P_ratio n₁ n₂ < 4 * (Nat.factorial n₁ + 1) →
      P_ratio n₁ n₂ ≠ t ^ 2) ∧
    (∀ t : ℕ, 2 ≤ t → ¬ ∃ m₁ m₂ : ℕ,
      Nat.factorial (t ^ 2 - 1) + 1 = m₁ ^ 2 ∧ Nat.factorial (t ^ 2) + 1 = m₂ ^ 2) ∧
    (∀ j m₁ m₂ : ℕ, 3 ≤ j →
      Nat.factorial (j ^ 2) + 1 = m₁ ^ 2 →
      Nat.factorial ((j + 1) ^ 2) + 1 = m₂ ^ 2 →
      ∀ T ∈ ({X_gcd m₁ m₂, Y_gcd m₁ m₂, Z_gcd m₁ m₂, W_gcd m₁ m₂} : Finset ℕ),
        |Real.log (T : ℝ) - (1 / 4 : ℝ) * Real.log (Nat.factorial (j ^ 2) : ℝ)| ≤
          12 * (j : ℝ) * Real.log ((j : ℝ) + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n₁ n₂ m₁ m₂ t hn₁ hlt hm₁ hm₂ hP_lt hP_sq
    have hP_ge : 2 ≤ P_ratio n₁ n₂ := P_ratio_ge_two hn₁ hlt
    have ht2 : 2 ≤ t := by nlinarith
    have hlt_2m : t < 2 * m₁ := by
      have : t ^ 2 < (2 * m₁) ^ 2 := by rw [← hP_sq]; linarith
      nlinarith
    have hm2_rel : (t * m₁) ^ 2 = m₂ ^ 2 + (t ^ 2 - 1) := by
      have h1 : m₂ ^ 2 - 1 = P_ratio n₁ n₂ * (m₁ ^ 2 - 1) := by
        have hfac : P_ratio n₁ n₂ * Nat.factorial n₁ = Nat.factorial n₂ := P_ratio_mul_factorial hlt
        zify [show 1 ≤ m₁ ^ 2 by nlinarith, show 1 ≤ m₂ ^ 2 by nlinarith]
        have hm1z : (Nat.factorial n₁ : ℤ) + 1 = (m₁ : ℤ) ^ 2 := by exact_mod_cast hm₁
        have hm2z : (Nat.factorial n₂ : ℤ) + 1 = (m₂ : ℤ) ^ 2 := by exact_mod_cast hm₂
        have hfz : (P_ratio n₁ n₂ : ℤ) * Nat.factorial n₁ = Nat.factorial n₂ := by exact_mod_cast hfac
        nlinarith
      have h2 : 1 ≤ m₁ ^ 2 := by nlinarith
      have h3 : 1 ≤ m₂ ^ 2 := by nlinarith
      have h4 : 1 ≤ t ^ 2 := by nlinarith
      zify [h2, h3, h4] at h1 ⊢
      rw [hP_sq] at h1
      push_cast at h1 ⊢
      linarith
    have htsq_gt1 : 1 ≤ t ^ 2 - 1 := by
      have : 4 ≤ t ^ 2 := by nlinarith
      omega
    have hm_gt : m₂ < t * m₁ := by
      have hsq_lt : m₂ ^ 2 < (t * m₁) ^ 2 := by omega
      by_contra hle; push Not at hle
      exact absurd (Nat.mul_le_mul hle hle) (by simpa [sq] using hsq_lt.not_ge)
    have hdiff_mul : (t * m₁ - m₂) * (t * m₁ + m₂) = t ^ 2 - 1 := by
      have hm2z : ((t * m₁ : ℕ) : ℤ) ^ 2 = (m₂ : ℤ) ^ 2 + ((t ^ 2 : ℤ) - 1) := by
        zify [show 1 ≤ t ^ 2 by nlinarith] at hm2_rel; exact hm2_rel
      zify [le_of_lt hm_gt, show 1 ≤ t ^ 2 by nlinarith]
      rw [show (↑t * ↑m₁ - ↑m₂) * (↑t * ↑m₁ + ↑m₂) = ((t * m₁ : ℕ) : ℤ) ^ 2 - (m₂ : ℤ) ^ 2 by push_cast; ring]
      linarith [hm2z]
    set u := t * m₁ - m₂
    have hu1 : 1 ≤ u := by omega
    rcases eq_or_lt_of_le hu1 with hu_eq | hu_ge2
    · rw [← hu_eq, one_mul] at hdiff_mul
      have : 2 * (t * m₁) = t ^ 2 := by omega
      have : 2 * m₁ = t := by nlinarith
      omega
    · have h2tm : 2 * (t * m₁ + m₂) ≤ t ^ 2 - 1 := by
        calc 2 * (t * m₁ + m₂) ≤ u * (t * m₁ + m₂) := Nat.mul_le_mul_right _ hu_ge2
          _ = t ^ 2 - 1 := hdiff_mul
      have htm_lt : 2 * (t * m₁) < t * t := by
        have htsq_lt : t ^ 2 - 1 < t * t := by rw [← sq]; omega
        omega
      have : 2 * m₁ < t := by nlinarith [htm_lt]
      omega
  · intro t ht ⟨m₁, m₂, hm₁, hm₂⟩
    by_cases ht2 : t = 2
    · subst ht2; norm_num [Nat.factorial] at hm₁
      have : m₁ ≤ 2 := by nlinarith
      interval_cases m₁ <;> norm_num at hm₁
    · have ht3 : 3 ≤ t := by omega
      have htsq9 : 9 ≤ t ^ 2 := by nlinarith
      have hn1_ge : 8 ≤ t ^ 2 - 1 := by omega
      have hlt : t ^ 2 - 1 < t ^ 2 := by omega
      have hP_eq : P_ratio (t ^ 2 - 1) (t ^ 2) = t ^ 2 := by
        unfold P_ratio
        have hsucc : t ^ 2 = (t ^ 2 - 1) + 1 := by omega
        have hfac_succ : Nat.factorial (t ^ 2) = t ^ 2 * Nat.factorial (t ^ 2 - 1) := by
          conv_lhs => rw [hsucc, Nat.factorial_succ, ← hsucc]
        rw [hfac_succ, Nat.mul_div_cancel _ (Nat.factorial_pos _)]
      have hP_lt : P_ratio (t ^ 2 - 1) (t ^ 2) < 4 * (Nat.factorial (t ^ 2 - 1) + 1) := by
        rw [hP_eq]
        have hfac : t ^ 2 < 4 * Nat.factorial (t ^ 2 - 1) := by
          have h8 : 8 ≤ t ^ 2 - 1 := hn1_ge
          have hgt := factorial_gt_four_mul_add_two (t ^ 2 - 1) (by omega)
          omega
        omega
      have hlt_2m : t < 2 * m₁ := by
        have : t ^ 2 < (2 * m₁) ^ 2 := by rw [← hP_eq]; linarith
        nlinarith
      have hm2_rel : (t * m₁) ^ 2 = m₂ ^ 2 + (t ^ 2 - 1) := by
        have h1 : m₂ ^ 2 - 1 = P_ratio (t ^ 2 - 1) (t ^ 2) * (m₁ ^ 2 - 1) := by
          have hfac : P_ratio (t ^ 2 - 1) (t ^ 2) * Nat.factorial (t ^ 2 - 1) = Nat.factorial (t ^ 2) :=
            P_ratio_mul_factorial hlt
          zify [show 1 ≤ m₁ ^ 2 by nlinarith, show 1 ≤ m₂ ^ 2 by nlinarith]
          have hm1z : (Nat.factorial (t ^ 2 - 1) : ℤ) + 1 = (m₁ : ℤ) ^ 2 := by exact_mod_cast hm₁
          have hm2z : (Nat.factorial (t ^ 2) : ℤ) + 1 = (m₂ : ℤ) ^ 2 := by exact_mod_cast hm₂
          have hfz : (P_ratio (t ^ 2 - 1) (t ^ 2) : ℤ) * Nat.factorial (t ^ 2 - 1) =
              Nat.factorial (t ^ 2) := by exact_mod_cast hfac
          nlinarith
        zify [show 1 ≤ m₁ ^ 2 by nlinarith, show 1 ≤ m₂ ^ 2 by nlinarith, show 1 ≤ t ^ 2 by nlinarith] at h1 ⊢
        rw [hP_eq] at h1; push_cast at h1 ⊢; linarith
      have htsq_gt1 : 1 ≤ t ^ 2 - 1 := by omega
      have hm_gt : m₂ < t * m₁ := by
        have hsq_lt : m₂ ^ 2 < (t * m₁) ^ 2 := by omega
        by_contra hle; push Not at hle
        exact absurd (Nat.mul_le_mul hle hle) (by simpa [sq] using hsq_lt.not_ge)
      have hdiff_mul : (t * m₁ - m₂) * (t * m₁ + m₂) = t ^ 2 - 1 := by
        have hm2z : ((t * m₁ : ℕ) : ℤ) ^ 2 = (m₂ : ℤ) ^ 2 + ((t ^ 2 : ℤ) - 1) := by
          zify [show 1 ≤ t ^ 2 by nlinarith] at hm2_rel; exact hm2_rel
        zify [le_of_lt hm_gt, show 1 ≤ t ^ 2 by nlinarith]
        rw [show (↑t * ↑m₁ - ↑m₂) * (↑t * ↑m₁ + ↑m₂) = ((t * m₁ : ℕ) : ℤ) ^ 2 - (m₂ : ℤ) ^ 2 by push_cast; ring]
        linarith [hm2z]
      set u := t * m₁ - m₂
      have hu1 : 1 ≤ u := by omega
      rcases eq_or_lt_of_le hu1 with hu_eq | hu_ge2
      · rw [← hu_eq, one_mul] at hdiff_mul
        have : 2 * (t * m₁) = t ^ 2 := by omega
        have : 2 * m₁ = t := by nlinarith
        omega
      · have h2tm : 2 * (t * m₁ + m₂) ≤ t ^ 2 - 1 := by
          calc 2 * (t * m₁ + m₂) ≤ u * (t * m₁ + m₂) := Nat.mul_le_mul_right _ hu_ge2
            _ = t ^ 2 - 1 := hdiff_mul
        have htm_lt : 2 * (t * m₁) < t * t := by
          have htsq_lt : t ^ 2 - 1 < t * t := by rw [← sq]; omega
          omega
        have : 2 * m₁ < t := by nlinarith [htm_lt]
        omega
  · intro j m₁ m₂ hj hm₁ hm₂ T hT
    set n₁ := j ^ 2
    set n₂ := (j + 1) ^ 2
    have hn₁ : 9 ≤ n₁ := by dsimp [n₁]; nlinarith
    have hlt : n₁ < n₂ := by dsimp [n₁, n₂]; nlinarith
    obtain ⟨⟨a, b, c, d⟩, hprop, _⟩ :=
      prop_6_1_part1_sl2_and_four_squares (by omega) hlt hm₁ hm₂
    rcases hprop with ⟨ha, hb, hc, hd, hab, hcd, _, _, _, _, _, h4sq⟩
    rcases h4sq with ⟨hXsq, hYsq, hZsq, hWsq⟩
    set P := P_ratio n₁ n₂
    have hP_ge : 2 ≤ P := P_ratio_ge_two (by omega) hlt
    -- Bound P ≤ n₂^(2j+1) = (j+1)^(4j+2)
    have hP_ub : P ≤ (j + 1) ^ (4 * j + 2) := by
      have hfac_eq : P * Nat.factorial n₁ = Nat.factorial n₂ := P_ratio_mul_factorial hlt
      have hprod_aux : ∀ a b : ℕ, a ≤ b → Nat.factorial b = Nat.factorial a * ∏ i ∈ Finset.Ioc a b, i := by
        intro a b hab_le
        induction b, hab_le using Nat.le_induction with
        | base => simp
        | succ k hk ih =>
          rw [Nat.factorial_succ, Finset.prod_Ioc_succ_top hk, ih]; ring
      have hprod : Nat.factorial n₂ = Nat.factorial n₁ * ∏ i ∈ Finset.Ioc n₁ n₂, i :=
        hprod_aux n₁ n₂ (le_of_lt hlt)
      have hP_eq_prod : P = ∏ i ∈ Finset.Ioc n₁ n₂, i := by
        have : P * Nat.factorial n₁ = (∏ i ∈ Finset.Ioc n₁ n₂, i) * Nat.factorial n₁ := by
          rw [hfac_eq, hprod]; ring
        exact mul_right_cancel₀ (Nat.factorial_pos n₁).ne' this
      rw [hP_eq_prod]
      have hle_each : ∀ i ∈ Finset.Ioc n₁ n₂, i ≤ (j + 1) ^ 2 := by
        intro i hi; exact (Finset.mem_Ioc.mp hi).2
      calc ∏ i ∈ Finset.Ioc n₁ n₂, i
          ≤ ∏ _i ∈ Finset.Ioc n₁ n₂, (j + 1) ^ 2 := Finset.prod_le_prod' hle_each
        _ = ((j + 1) ^ 2) ^ (Finset.Ioc n₁ n₂).card := Finset.prod_const _
        _ = ((j + 1) ^ 2) ^ (2 * j + 1) := by
            rw [Nat.card_Ioc]; congr 1; dsimp [n₁, n₂]; ring_nf; omega
        _ = (j + 1) ^ (4 * j + 2) := by rw [← pow_mul]; ring_nf
    -- From eq. (6.4), bound (P m₁ - m₂ - (P-1)) ≥ (1/2) P √(n₁!) and ≤ 4 P √(n₁!)
    have ha_le : a ≤ P := le_trans (Nat.le_mul_of_pos_right a hb) (hab ▸ Nat.sub_le P 1)
    have hb_le : b ≤ P := le_trans (Nat.le_mul_of_pos_left b ha) (hab ▸ Nat.sub_le P 1)
    have hc_le : c ≤ P := le_trans (Nat.le_mul_of_pos_right c hd) hcd.le
    have hd_le : d ≤ P := le_trans (Nat.le_mul_of_pos_left d hc) hcd.le
    have hfac_ge : 362880 ≤ Nat.factorial n₁ := by
      calc 362880 = Nat.factorial 9 := by norm_num [Nat.factorial]
        _ ≤ Nat.factorial n₁ := Nat.factorial_le hn₁
    have hm₂_le : (m₂ : ℝ) ≤ Real.sqrt (P : ℝ) * (m₁ : ℝ) := by
      have hm2_sq : (m₂ : ℝ) ^ 2 ≤ (Real.sqrt (P : ℝ) * (m₁ : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have h1 : (m₂ : ℝ) ^ 2 = (P : ℝ) * (m₁ : ℝ) ^ 2 - ((P : ℝ) - 1) := by
          have : (P : ℤ) * (Nat.factorial n₁ : ℤ) = Nat.factorial n₂ := by
            exact_mod_cast P_ratio_mul_factorial hlt
          have hm1r : (Nat.factorial n₁ : ℝ) + 1 = (m₁ : ℝ) ^ 2 := by exact_mod_cast hm₁
          have hm2r : (Nat.factorial n₂ : ℝ) + 1 = (m₂ : ℝ) ^ 2 := by exact_mod_cast hm₂
          have hPr : (P : ℝ) * (Nat.factorial n₁ : ℝ) = Nat.factorial n₂ := by exact_mod_cast this
          nlinarith
        have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
        linarith
      nlinarith only [hm2_sq, mul_nonneg (Real.sqrt_nonneg (P : ℝ)) (Nat.cast_nonneg m₁ : (0 : ℝ) ≤ m₁), (Nat.cast_nonneg m₂ : (0 : ℝ) ≤ m₂)]
    have hPm1_lb : (1 / 8 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) ≤
        (P : ℝ) * m₁ - m₂ - (P - 1) := by
      have hP2r : (2 : ℝ) ≤ P := by exact_mod_cast hP_ge
      have hsqrtP : Real.sqrt (P : ℝ) ≤ (P : ℝ) * (3 / 4 : ℝ) := by
        have hsq : Real.sqrt (P : ℝ) ^ 2 ≤ ((P : ℝ) * (3 / 4 : ℝ)) ^ 2 := by
          rw [Real.sq_sqrt (by positivity)]; nlinarith only [hP2r]
        nlinarith only [hsq, Real.sqrt_nonneg (P : ℝ), hP2r]
      have hm1_gt : Real.sqrt (Nat.factorial n₁ : ℝ) < m₁ := by
        rw [← Real.sqrt_sq (Nat.cast_nonneg m₁)]
        exact Real.sqrt_lt_sqrt (by positivity) (by
          have : (Nat.factorial n₁ : ℝ) + 1 = (m₁ : ℝ) ^ 2 := by exact_mod_cast hm₁
          linarith)
      have hPm1_big : (P : ℝ) ≤ (1 / 16 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
        have h600 : (600 : ℝ) ≤ Real.sqrt (Nat.factorial n₁ : ℝ) := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 600)]
          exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 360000 ≤ Nat.factorial n₁))
        nlinarith only [h600, hP2r]
      have hm2_le_P34 : (m₂ : ℝ) ≤ (3 / 4 : ℝ) * (P : ℝ) * (m₁ : ℝ) := by
        have h1 : Real.sqrt (P : ℝ) * (m₁ : ℝ) ≤ ((P : ℝ) * (3 / 4 : ℝ)) * (m₁ : ℝ) :=
          mul_le_mul_of_nonneg_right hsqrtP (Nat.cast_nonneg m₁)
        linarith only [hm₂_le, h1]
      have hP_m1 : (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) ≤ (P : ℝ) * (m₁ : ℝ) :=
        mul_le_mul_of_nonneg_left hm1_gt.le (by positivity)
      nlinarith only [hm2_le_P34, hP_m1, hPm1_big, hP2r]
    have hPm1_ub : (P : ℝ) * m₁ + m₂ + (P - 1) ≤ 4 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
      have hm1_le : (m₁ : ℝ) ≤ 2 * Real.sqrt (Nat.factorial n₁ : ℝ) := by
        have hsq : (m₁ : ℝ) ^ 2 ≤ (2 * Real.sqrt (Nat.factorial n₁ : ℝ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
          have : (m₁ : ℝ) ^ 2 = (Nat.factorial n₁ : ℝ) + 1 := by exact_mod_cast hm₁.symm
          have : (362880 : ℝ) ≤ Nat.factorial n₁ := by exact_mod_cast hfac_ge
          linarith
        nlinarith only [hsq, Real.sqrt_nonneg (Nat.factorial n₁ : ℝ), (Nat.cast_nonneg m₁ : (0 : ℝ) ≤ m₁)]
      have hP2r : (2 : ℝ) ≤ P := by exact_mod_cast hP_ge
      have hm2_le' : (m₂ : ℝ) ≤ (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
        have hm2_sq : (m₂ : ℝ) ^ 2 ≤ ((P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
          have h1 : (m₂ : ℝ) ^ 2 = (P : ℝ) * (Nat.factorial n₁ : ℝ) + 1 := by
            have : P * Nat.factorial n₁ + 1 = m₂ ^ 2 := by
              rw [P_ratio_mul_factorial hlt]; exact hm₂
            exact_mod_cast this.symm
          have hfacr : (362880 : ℝ) ≤ Nat.factorial n₁ := by exact_mod_cast hfac_ge
          nlinarith only [h1, hP2r, hfacr]
        nlinarith only [hm2_sq, mul_nonneg (by linarith [hP2r] : (0 : ℝ) ≤ P) (Real.sqrt_nonneg (Nat.factorial n₁ : ℝ)), (Nat.cast_nonneg m₂ : (0 : ℝ) ≤ m₂)]
      have hP_le : (P : ℝ) - 1 ≤ (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
        have h1sq : (1 : ℝ) ≤ Real.sqrt (Nat.factorial n₁ : ℝ) := by
          rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.factorial_pos n₁)
        nlinarith only [h1sq, hP2r]
      have hP_m1_ub : (P : ℝ) * (m₁ : ℝ) ≤ 2 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
        nlinarith only [hm1_le, hP2r]
      linarith only [hP_m1_ub, hm2_le', hP_le]
    have hlogP_ub : Real.log (P : ℝ) ≤ (4 * (j : ℝ) + 2) * Real.log ((j : ℝ) + 1) := by
      have h1 : Real.log (P : ℝ) ≤ Real.log (((j + 1 : ℕ) : ℝ) ^ (4 * j + 2)) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hP_ub)
      rw [Real.log_pow] at h1
      push_cast at h1; exact h1
    have hbound_sq : ∀ (U k : ℕ), 1 ≤ k → k ≤ 2 * P ^ 2 → 0 < U →
        (1 / 8 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) ≤ (k : ℝ) * (U : ℝ) ^ 2 →
        (k : ℝ) * (U : ℝ) ^ 2 ≤ 4 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) →
        |Real.log (U : ℝ) - (1 / 4 : ℝ) * Real.log (Nat.factorial n₁ : ℝ)| ≤
          12 * (j : ℝ) * Real.log ((j : ℝ) + 1) := by
      intro U k hk1 hk_ub hU_pos hlb hub
      have hfac_pos : (0 : ℝ) < Nat.factorial n₁ := by exact_mod_cast Nat.factorial_pos n₁
      have hsqrt_pos : 0 < Real.sqrt (Nat.factorial n₁ : ℝ) := Real.sqrt_pos.mpr hfac_pos
      have hk_pos : (0 : ℝ) < k := by positivity
      have hP_pos : (0 : ℝ) < P := by positivity
      have hU2_lb : Real.sqrt (Nat.factorial n₁ : ℝ) / (16 * (P : ℝ)) ≤ (U : ℝ) ^ 2 := by
        calc Real.sqrt (Nat.factorial n₁ : ℝ) / (16 * (P : ℝ))
            = ((1 / 8 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ)) / (2 * (P : ℝ) ^ 2) := by
              field_simp; ring
          _ ≤ ((1 / 8 : ℝ) * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ)) / (k : ℝ) := by
              gcongr; exact_mod_cast hk_ub
          _ ≤ (U : ℝ) ^ 2 := (div_le_iff₀ hk_pos).mpr (by linarith)
      have hU2_ub : (U : ℝ) ^ 2 ≤ 4 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := by
        have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
        calc (U : ℝ) ^ 2 ≤ (k : ℝ) * (U : ℝ) ^ 2 := le_mul_of_one_le_left (by positivity) hk1r
          _ ≤ 4 * (P : ℝ) * Real.sqrt (Nat.factorial n₁ : ℝ) := hub
      have hlog_sqrt : Real.log (Real.sqrt (Nat.factorial n₁ : ℝ)) =
          (1 / 2 : ℝ) * Real.log (Nat.factorial n₁ : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.log_rpow hfac_pos]; try ring
      have hlog_U2_ub : 2 * Real.log (U : ℝ) - (1 / 2 : ℝ) * Real.log (Nat.factorial n₁ : ℝ) ≤
          Real.log (4 * (P : ℝ)) := by
        have h1 := Real.log_le_log (by positivity) hU2_ub
        rw [Real.log_pow, Nat.cast_ofNat, Real.log_mul (by positivity) hsqrt_pos.ne', hlog_sqrt] at h1
        linarith
      have hlog_U2_lb : -Real.log (16 * (P : ℝ)) ≤
          2 * Real.log (U : ℝ) - (1 / 2 : ℝ) * Real.log (Nat.factorial n₁ : ℝ) := by
        have h1 := Real.log_le_log (by positivity) hU2_lb
        rw [Real.log_pow, Nat.cast_ofNat, Real.log_div hsqrt_pos.ne' (by positivity), hlog_sqrt] at h1
        linarith
      have h16P : Real.log (16 * (P : ℝ)) ≤ 24 * (j : ℝ) * Real.log ((j : ℝ) + 1) := by
        rw [Real.log_mul (by norm_num) hP_pos.ne']
        have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast hj
        have hlog16 : Real.log 16 ≤ 4 * Real.log ((j : ℝ) + 1) := by
          have : (16 : ℝ) ≤ ((j : ℝ) + 1) ^ 4 := le_trans (by norm_num : (16 : ℝ) ≤ (2 : ℝ) ^ 4) (pow_le_pow_left₀ (by norm_num) (by linarith) 4)
          have h1 := Real.log_le_log (by norm_num) this
          rwa [Real.log_pow, Nat.cast_ofNat] at h1
        have h4j : (4 * (j : ℝ) + 2) ≤ 20 * (j : ℝ) / 3 := by linarith
        have hlogj1 : 0 ≤ Real.log ((j : ℝ) + 1) := Real.log_nonneg (by linarith)
        nlinarith only [hlogP_ub, hlog16, h4j, hlogj1, hj3]
      have h4P : Real.log (4 * (P : ℝ)) ≤ 24 * (j : ℝ) * Real.log ((j : ℝ) + 1) := by
        have : 4 * (P : ℝ) ≤ 16 * (P : ℝ) := by linarith
        exact le_trans (Real.log_le_log (by positivity) this) h16P
      rw [abs_le]; constructor <;> linarith
    have ⟨hX_pos, hY_pos, hZ_pos, hW_pos, _⟩ :=
      prop_6_1_coprime_and_factorization (by omega) hlt hm₁ hm₂
    have hm2_nn : (0 : ℝ) ≤ m₂ := Nat.cast_nonneg m₂
    have hP1_nn : (1 : ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl
    · refine hbound_sq _ (2 * a * c) (by nlinarith only [ha, hc]) (by nlinarith only [ha_le, hc_le]) hX_pos ?_ ?_
      · have : ((2 * a * c : ℕ) : ℝ) * (X_gcd m₁ m₂ : ℝ) ^ 2 = (P : ℝ) * m₁ - m₂ - ((P : ℝ) - 1) := by
          exact_mod_cast hXsq
        linarith [hPm1_lb]
      · have : ((2 * a * c : ℕ) : ℝ) * (X_gcd m₁ m₂ : ℝ) ^ 2 = (P : ℝ) * m₁ - m₂ - ((P : ℝ) - 1) := by
          exact_mod_cast hXsq
        linarith [hPm1_ub, hm2_nn, hP1_nn]
    · refine hbound_sq _ (2 * a * d) (by nlinarith only [ha, hd]) (by nlinarith only [ha_le, hd_le]) hY_pos ?_ ?_
      · have : ((2 * a * d : ℕ) : ℝ) * (Y_gcd m₁ m₂ : ℝ) ^ 2 = (P : ℝ) * m₁ - m₂ + ((P : ℝ) - 1) := by
          exact_mod_cast hYsq
        linarith [hPm1_lb, hP1_nn]
      · have : ((2 * a * d : ℕ) : ℝ) * (Y_gcd m₁ m₂ : ℝ) ^ 2 = (P : ℝ) * m₁ - m₂ + ((P : ℝ) - 1) := by
          exact_mod_cast hYsq
        linarith [hPm1_ub, hm2_nn]
    · refine hbound_sq _ (2 * b * d) (by nlinarith only [hb, hd]) (by nlinarith only [hb_le, hd_le]) hZ_pos ?_ ?_
      · have : ((2 * b * d : ℕ) : ℝ) * (Z_gcd m₁ m₂ : ℝ) ^ 2 = (P : ℝ) * m₁ + m₂ - ((P : ℝ) - 1) := by
          exact_mod_cast hZsq
        linarith [hPm1_lb, hm2_nn]
      · have : ((2 * b * d : ℕ) : ℝ) * (Z_gcd m₁ m₂ : ℝ) ^ 2 = (P : ℝ) * m₁ + m₂ - ((P : ℝ) - 1) := by
          exact_mod_cast hZsq
        linarith [hPm1_ub, hP1_nn]
    · refine hbound_sq _ (2 * b * c) (by nlinarith only [hb, hc]) (by nlinarith only [hb_le, hc_le]) hW_pos ?_ ?_
      · have : ((2 * b * c : ℕ) : ℝ) * (W_gcd m₁ m₂ : ℝ) ^ 2 = (P : ℝ) * m₁ + m₂ + ((P : ℝ) - 1) := by
          exact_mod_cast hWsq
        linarith [hPm1_lb, hm2_nn, hP1_nn]
      · have : ((2 * b * c : ℕ) : ℝ) * (W_gcd m₁ m₂ : ℝ) ^ 2 = (P : ℝ) * m₁ + m₂ + ((P : ℝ) - 1) := by
          exact_mod_cast hWsq
        linarith [hPm1_ub]

end GrasGreenbergBrocard
