import GrasGreenbergBrocard.Thm5_2EffectiveCores

/-!
# Section 6.1: Universal $\mathrm{SL}_2(\mathbb{Z})$ Four-GCD System and Twin Norm Identities

This file formalizes **Proposition 6.1 (i)–(iii)** and **eqs. (6.1)–(6.6)** of the manuscript:
for any two Brocard solutions `4 ≤ n₁ < n₂` (`n_i ! + 1 = m_i ^ 2`), the four greatest common
divisors `X = gcd(A₁, A₂)`, `Y = gcd(B₁, B₂)`, `Z = gcd(A₁, B₂)`, `W = gcd(B₁, A₂)`
satisfy `XYZW = n₁! / 4`, the `SL₂(ℤ)` matrix system (eq. 6.3), the four-squares identities
(eq. 6.4), the twin norm identities in `ℤ[√P]` (eq. 6.5), and the Quadrant IV Legendre lock
(eq. 6.6).
-/

open scoped BigOperators

namespace GrasGreenbergBrocard

set_option maxHeartbeats 800000

/-! ### Definitions (eq. 6.1) -/

def A_sol (m : ℕ) : ℕ := (m - 1) / 2
def B_sol (m : ℕ) : ℕ := (m + 1) / 2
def U_pair (m₁ m₂ : ℕ) : ℕ := (m₂ - m₁) / 2
def V_pair (m₁ m₂ : ℕ) : ℕ := (m₂ + m₁) / 2
def P_ratio (n₁ n₂ : ℕ) : ℕ := Nat.factorial n₂ / Nat.factorial n₁

def X_gcd (m₁ m₂ : ℕ) : ℕ := Nat.gcd (A_sol m₁) (A_sol m₂)
def Y_gcd (m₁ m₂ : ℕ) : ℕ := Nat.gcd (B_sol m₁) (B_sol m₂)
def Z_gcd (m₁ m₂ : ℕ) : ℕ := Nat.gcd (A_sol m₁) (B_sol m₂)
def W_gcd (m₁ m₂ : ℕ) : ℕ := Nat.gcd (B_sol m₁) (A_sol m₂)

private lemma eq_gcd_mul_gcd_of_dvd_mul {d u v : ℕ} (hd : d ∣ u * v) (hcop : Nat.Coprime u v) :
    d = Nat.gcd d u * Nat.gcd d v := by
  have h1 : Nat.gcd d u * Nat.gcd d v ∣ d := by
    have hcop_g : Nat.Coprime (Nat.gcd d u) (Nat.gcd d v) :=
      hcop.coprime_dvd_left (Nat.gcd_dvd_right d u) |>.coprime_dvd_right (Nat.gcd_dvd_right d v)
    exact hcop_g.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left d u) (Nat.gcd_dvd_left d v)
  have h2 : d ∣ Nat.gcd d u * Nat.gcd d v := by
    by_cases hd0 : d = 0
    · subst hd0; simp only [Nat.gcd_zero_left] at hd ⊢; exact hd
    · have hg_pos : 0 < Nat.gcd d u := Nat.gcd_pos_of_pos_left u (Nat.pos_of_ne_zero hd0)
      have hdiv : d = Nat.gcd d u * (d / Nat.gcd d u) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_left d u)).symm
      have h_cop_q : Nat.Coprime (d / Nat.gcd d u) (u / Nat.gcd d u) := by
        have := Nat.coprime_div_gcd_div_gcd hg_pos
        exact this
      have h_dvd_uv : d / Nat.gcd d u ∣ (u / Nat.gcd d u) * v := by
        have hmul : Nat.gcd d u * (d / Nat.gcd d u) ∣ Nat.gcd d u * ((u / Nat.gcd d u) * v) := by
          rw [← hdiv]
          calc d ∣ u * v := hd
            _ = (Nat.gcd d u * (u / Nat.gcd d u)) * v := by
              rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right d u)]
            _ = Nat.gcd d u * ((u / Nat.gcd d u) * v) := by ring
        exact Nat.dvd_of_mul_dvd_mul_left hg_pos hmul
      have h_dvd_v : d / Nat.gcd d u ∣ v := h_cop_q.dvd_of_dvd_mul_left h_dvd_uv
      have h_dvd_d : d / Nat.gcd d u ∣ d := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d u)
      have h_dvd_gv : d / Nat.gcd d u ∣ Nat.gcd d v := Nat.dvd_gcd h_dvd_d h_dvd_v
      calc d = Nat.gcd d u * (d / Nat.gcd d u) := hdiv
        _ ∣ Nat.gcd d u * Nat.gcd d v := mul_dvd_mul_left (Nat.gcd d u) h_dvd_gv
  exact Nat.dvd_antisymm h2 h1

lemma P_ratio_mul_factorial {n₁ n₂ : ℕ} (hlt : n₁ < n₂) :
    P_ratio n₁ n₂ * Nat.factorial n₁ = Nat.factorial n₂ := by
  unfold P_ratio
  exact Nat.div_mul_cancel (Nat.factorial_dvd_factorial (le_of_lt hlt))

lemma P_ratio_ge_two {n₁ n₂ : ℕ} (hn₁ : 4 ≤ n₁) (hlt : n₁ < n₂) : 2 ≤ P_ratio n₁ n₂ := by
  have hmul := P_ratio_mul_factorial hlt
  have hfac_pos : 0 < Nat.factorial n₁ := Nat.factorial_pos n₁
  have hfac_lt : Nat.factorial n₁ < Nat.factorial n₂ :=
    Nat.factorial_lt (by omega) |>.mpr hlt
  have h2 : 2 * Nat.factorial n₁ ≤ Nat.factorial n₂ := by
    calc 2 * Nat.factorial n₁ ≤ (n₁ + 1) * Nat.factorial n₁ :=
          Nat.mul_le_mul_right _ (by omega)
      _ = Nat.factorial (n₁ + 1) := (Nat.factorial_succ n₁).symm
      _ ≤ Nat.factorial n₂ := Nat.factorial_le (by omega)
  nlinarith

lemma m_lt_of_brocard {n₁ n₂ m₁ m₂ : ℕ} (hlt : n₁ < n₂)
    (hm₁ : Nat.factorial n₁ + 1 = m₁ ^ 2) (hm₂ : Nat.factorial n₂ + 1 = m₂ ^ 2) :
    m₁ < m₂ := by
  have hfac_lt : Nat.factorial n₁ < Nat.factorial n₂ := by
    by_cases h0 : n₁ = 0
    · subst h0; have : 2 ≤ n₂ := by omega
      calc Nat.factorial 0 = 1 := rfl
        _ < 2 := by norm_num
        _ = Nat.factorial 2 := by norm_num
        _ ≤ Nat.factorial n₂ := Nat.factorial_le (by omega)
    · exact (Nat.factorial_lt (Nat.pos_of_ne_zero h0)).mpr hlt
  by_contra hle
  push_neg at hle
  have hsq : m₂ ^ 2 ≤ m₁ ^ 2 := Nat.pow_le_pow_left hle 2
  omega

/-- **Proposition 6.1 (Setup)**: Pairwise coprimality of `X, Y, Z, W` and the
factorization `A₁ = X Z`, `B₁ = Y W`, `X Y Z W = n₁! / 4`. -/
theorem prop_6_1_coprime_and_factorization {n₁ n₂ m₁ m₂ : ℕ}
    (hn₁ : 4 ≤ n₁) (hlt : n₁ < n₂)
    (hm₁ : Nat.factorial n₁ + 1 = m₁ ^ 2) (hm₂ : Nat.factorial n₂ + 1 = m₂ ^ 2) :
    let A₁ := A_sol m₁
    let B₁ := B_sol m₁
    let X := X_gcd m₁ m₂
    let Y := Y_gcd m₁ m₂
    let Z := Z_gcd m₁ m₂
    let W := W_gcd m₁ m₂
    0 < X ∧ 0 < Y ∧ 0 < Z ∧ 0 < W ∧
    Nat.Coprime X Y ∧ Nat.Coprime X Z ∧ Nat.Coprime X W ∧
    Nat.Coprime Y Z ∧ Nat.Coprime Y W ∧ Nat.Coprime Z W ∧
    A₁ = X * Z ∧ B₁ = Y * W ∧ 4 * (X * Y * Z * W) = Nat.factorial n₁ := by
  have ⟨hA₁, hB₁, _, hcop1, h4mul1, _, _⟩ := brocard_u1_u2_rel hn₁ hm₁
  have ⟨hA₂, hB₂, _, hcop2, h4mul2, _, _⟩ := brocard_u1_u2_rel (by omega) hm₂
  change 0 < A_sol m₁ at hA₁; change 0 < B_sol m₁ at hB₁
  change Nat.Coprime (A_sol m₁) (B_sol m₁) at hcop1
  change 4 * A_sol m₁ * B_sol m₁ = Nat.factorial n₁ at h4mul1
  change 0 < A_sol m₂ at hA₂; change 0 < B_sol m₂ at hB₂
  change Nat.Coprime (A_sol m₂) (B_sol m₂) at hcop2
  change 4 * A_sol m₂ * B_sol m₂ = Nat.factorial n₂ at h4mul2
  set A₁ := A_sol m₁; set B₁ := B_sol m₁
  set A₂ := A_sol m₂; set B₂ := B_sol m₂
  set X := X_gcd m₁ m₂; set Y := Y_gcd m₁ m₂
  set Z := Z_gcd m₁ m₂; set W := W_gcd m₁ m₂
  have hX_pos : 0 < X := Nat.gcd_pos_of_pos_left A₂ hA₁
  have hY_pos : 0 < Y := Nat.gcd_pos_of_pos_left B₂ hB₁
  have hZ_pos : 0 < Z := Nat.gcd_pos_of_pos_left B₂ hA₁
  have hW_pos : 0 < W := Nat.gcd_pos_of_pos_left A₂ hB₁
  have hXY : Nat.Coprime X Y :=
    hcop1.coprime_dvd_left (Nat.gcd_dvd_left A₁ A₂) |>.coprime_dvd_right (Nat.gcd_dvd_left B₁ B₂)
  have hXZ : Nat.Coprime X Z :=
    hcop2.coprime_dvd_left (Nat.gcd_dvd_right A₁ A₂) |>.coprime_dvd_right (Nat.gcd_dvd_right A₁ B₂)
  have hXW : Nat.Coprime X W :=
    hcop1.coprime_dvd_left (Nat.gcd_dvd_left A₁ A₂) |>.coprime_dvd_right (Nat.gcd_dvd_left B₁ A₂)
  have hYZ : Nat.Coprime Y Z :=
    (hcop1.symm.coprime_dvd_left (Nat.gcd_dvd_left B₁ B₂)).coprime_dvd_right (Nat.gcd_dvd_left A₁ B₂)
  have hYW : Nat.Coprime Y W :=
    (hcop2.symm.coprime_dvd_left (Nat.gcd_dvd_right B₁ B₂)).coprime_dvd_right (Nat.gcd_dvd_right B₁ A₂)
  have hZW : Nat.Coprime Z W :=
    hcop1.coprime_dvd_left (Nat.gcd_dvd_left A₁ B₂) |>.coprime_dvd_right (Nat.gcd_dvd_left B₁ A₂)
  have hdvd_fac : A₁ * B₁ ∣ A₂ * B₂ := by
    have h4 : 4 * (A₁ * B₁) ∣ 4 * (A₂ * B₂) := by
      have : 4 * (A₁ * B₁) = Nat.factorial n₁ := by rw [← mul_assoc]; exact h4mul1
      have h2' : 4 * (A₂ * B₂) = Nat.factorial n₂ := by rw [← mul_assoc]; exact h4mul2
      rw [this, h2']
      exact Nat.factorial_dvd_factorial (le_of_lt hlt)
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4
  have hA₁_eq : A₁ = X * Z :=
    eq_gcd_mul_gcd_of_dvd_mul (dvd_trans (dvd_mul_right A₁ B₁) hdvd_fac) hcop2
  have hB₁_eq : B₁ = Y * W := by
    have hB_dvd : B₁ ∣ B₂ * A₂ := by
      rw [mul_comm B₂ A₂]
      exact dvd_trans (dvd_mul_left B₁ A₁) hdvd_fac
    exact eq_gcd_mul_gcd_of_dvd_mul hB_dvd hcop2.symm
  have hprod : 4 * (X * Y * Z * W) = Nat.factorial n₁ := by
    calc 4 * (X * Y * Z * W) = 4 * (X * Z) * (Y * W) := by ring
      _ = 4 * A₁ * B₁ := by rw [← hA₁_eq, ← hB₁_eq]
      _ = Nat.factorial n₁ := h4mul1
  exact ⟨hX_pos, hY_pos, hZ_pos, hW_pos, hXY, hXZ, hXW, hYZ, hYW, hZW, hA₁_eq, hB₁_eq, hprod⟩

/-- **Proposition 6.1(i)**: Existence and uniqueness of `a, b, c, d > 0` with `a b = P - 1`,
`c d = P`, the `SL₂(ℤ)` matrix system (eq. 6.3), and the four-squares identities (eq. 6.4). -/
theorem prop_6_1_part1_sl2_and_four_squares {n₁ n₂ m₁ m₂ : ℕ}
    (hn₁ : 4 ≤ n₁) (hlt : n₁ < n₂)
    (hm₁ : Nat.factorial n₁ + 1 = m₁ ^ 2) (hm₂ : Nat.factorial n₂ + 1 = m₂ ^ 2) :
    let A₁ := A_sol m₁; let B₁ := B_sol m₁
    let A₂ := A_sol m₂; let B₂ := B_sol m₂
    let U := U_pair m₁ m₂; let V := V_pair m₁ m₂
    let P := P_ratio n₁ n₂
    let X := X_gcd m₁ m₂; let Y := Y_gcd m₁ m₂
    let Z := Z_gcd m₁ m₂; let W := W_gcd m₁ m₂
    ∃! abcd : ℕ × ℕ × ℕ × ℕ,
      let (a, b, c, d) := abcd
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a * b = P - 1 ∧ c * d = P ∧
      A₂ = c * X * W ∧ B₂ = d * Y * Z ∧ U = a * X * Y ∧ V = b * Z * W ∧
      -- eq. (6.3)
      ((Z : ℤ) = (c : ℤ) * W - (a : ℤ) * Y ∧
       (W : ℤ) = (d : ℤ) * Z - (a : ℤ) * X ∧
       (Y : ℤ) = (b : ℤ) * Z - (c : ℤ) * X ∧
       (X : ℤ) = (b : ℤ) * W - (d : ℤ) * Y ∧
       (d : ℤ) * (Y : ℤ) ^ 2 - (c : ℤ) * (X : ℤ) ^ 2 = (b : ℤ) ∧
       (c : ℤ) * (W : ℤ) ^ 2 - (d : ℤ) * (Z : ℤ) ^ 2 = (a : ℤ)) ∧
      -- eq. (6.4)
      (2 * (a : ℤ) * c * (X : ℤ) ^ 2 = (P : ℤ) * m₁ - m₂ - ((P : ℤ) - 1) ∧
       2 * (a : ℤ) * d * (Y : ℤ) ^ 2 = (P : ℤ) * m₁ - m₂ + ((P : ℤ) - 1) ∧
       2 * (b : ℤ) * d * (Z : ℤ) ^ 2 = (P : ℤ) * m₁ + m₂ - ((P : ℤ) - 1) ∧
       2 * (b : ℤ) * c * (W : ℤ) ^ 2 = (P : ℤ) * m₁ + m₂ + ((P : ℤ) - 1)) := by
  have ⟨hX_pos, hY_pos, hZ_pos, hW_pos, hXY, _, hXW, hYZ, _, hZW, hA₁_eq, hB₁_eq, hprod⟩ :=
    prop_6_1_coprime_and_factorization hn₁ hlt hm₁ hm₂
  have ⟨hA₁, hB₁, hB₁_succ, _, h4mul1, _, _⟩ := brocard_u1_u2_rel hn₁ hm₁
  have ⟨hA₂, hB₂, hB₂_succ, _, h4mul2, _, _⟩ := brocard_u1_u2_rel (by omega) hm₂
  have hm_lt : m₁ < m₂ := m_lt_of_brocard hlt hm₁ hm₂
  have ⟨hm₁_odd, hm₁_ge⟩ := brocard_m_odd (by omega) hm₁
  have ⟨hm₂_odd, hm₂_ge⟩ := brocard_m_odd (by omega) hm₂
  set A₁ := A_sol m₁; set B₁ := B_sol m₁
  set A₂ := A_sol m₂; set B₂ := B_sol m₂
  set U := U_pair m₁ m₂; set V := V_pair m₁ m₂
  set P := P_ratio n₁ n₂
  set X := X_gcd m₁ m₂; set Y := Y_gcd m₁ m₂
  set Z := Z_gcd m₁ m₂; set W := W_gcd m₁ m₂
  have hU_eq1 : U + A₁ = A₂ := by
    change (m₂ - m₁) / 2 + (m₁ - 1) / 2 = (m₂ - 1) / 2; omega
  have hU_eq2 : U + B₁ = B₂ := by
    change (m₂ - m₁) / 2 + (m₁ + 1) / 2 = (m₂ + 1) / 2; omega
  have hV_eq1 : V = A₂ + B₁ := by
    change (m₂ + m₁) / 2 = (m₂ - 1) / 2 + (m₁ + 1) / 2; omega
  have hV_eq2 : V = B₂ + A₁ := by
    change (m₂ + m₁) / 2 = (m₂ + 1) / 2 + (m₁ - 1) / 2; omega
  have hU_pos : 0 < U := by change 0 < (m₂ - m₁) / 2; omega
  have hV_pos : 0 < V := by omega
  have hXW_dvd : X * W ∣ A₂ :=
    hXW.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right A₁ A₂) (Nat.gcd_dvd_right B₁ A₂)
  have hYZ_dvd : Y * Z ∣ B₂ :=
    hYZ.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right B₁ B₂) (Nat.gcd_dvd_right A₁ B₂)
  have hX_dvd_U : X ∣ U := by
    have h1 : X ∣ A₁ := Nat.gcd_dvd_left A₁ A₂
    have h2 : X ∣ A₂ := Nat.gcd_dvd_right A₁ A₂
    rw [← hU_eq1] at h2
    exact (Nat.dvd_add_left h1).mp h2
  have hY_dvd_U : Y ∣ U := by
    have h1 : Y ∣ B₁ := Nat.gcd_dvd_left B₁ B₂
    have h2 : Y ∣ B₂ := Nat.gcd_dvd_right B₁ B₂
    rw [← hU_eq2] at h2
    exact (Nat.dvd_add_left h1).mp h2
  have hXY_dvd : X * Y ∣ U := hXY.mul_dvd_of_dvd_of_dvd hX_dvd_U hY_dvd_U
  have hZ_dvd_V : Z ∣ V := by
    rw [hV_eq2]; exact dvd_add (Nat.gcd_dvd_right A₁ B₂) (Nat.gcd_dvd_left A₁ B₂)
  have hW_dvd_V : W ∣ V := by
    rw [hV_eq1]; exact dvd_add (Nat.gcd_dvd_right B₁ A₂) (Nat.gcd_dvd_left B₁ A₂)
  have hZW_dvd : Z * W ∣ V := hZW.mul_dvd_of_dvd_of_dvd hZ_dvd_V hW_dvd_V
  set c := A₂ / (X * W)
  set d := B₂ / (Y * Z)
  set a := U / (X * Y)
  set b := V / (Z * W)
  have hA₂_eq : A₂ = c * X * W := by
    have h := (Nat.div_mul_cancel hXW_dvd).symm
    change A₂ = c * (X * W) at h
    rw [h, mul_assoc]
  have hB₂_eq : B₂ = d * Y * Z := by
    have h := (Nat.div_mul_cancel hYZ_dvd).symm
    change B₂ = d * (Y * Z) at h
    rw [h, mul_assoc]
  have hU_eq : U = a * X * Y := by
    have h := (Nat.div_mul_cancel hXY_dvd).symm
    change U = a * (X * Y) at h
    rw [h, mul_assoc]
  have hV_eq : V = b * Z * W := by
    have h := (Nat.div_mul_cancel hZW_dvd).symm
    change V = b * (Z * W) at h
    rw [h, mul_assoc]
  have ha_pos : 0 < a := by
    by_contra ha0; have ha' : a = 0 := by omega
    rw [ha', zero_mul, zero_mul] at hU_eq; exact absurd hU_eq (Nat.ne_of_gt hU_pos)
  have hb_pos : 0 < b := by
    by_contra hb0; have hb' : b = 0 := by omega
    rw [hb', zero_mul, zero_mul] at hV_eq; exact absurd hV_eq (Nat.ne_of_gt hV_pos)
  have hc_pos : 0 < c := by
    by_contra hc0; have hc' : c = 0 := by omega
    rw [hc', zero_mul, zero_mul] at hA₂_eq; exact absurd hA₂_eq (Nat.ne_of_gt hA₂)
  have hd_pos : 0 < d := by
    by_contra hd0; have hd' : d = 0 := by omega
    rw [hd', zero_mul, zero_mul] at hB₂_eq; exact absurd hB₂_eq (Nat.ne_of_gt hB₂)
  have hP_ge : 2 ≤ P := P_ratio_ge_two hn₁ hlt
  have hcd_eq : c * d = P := by
    have h1 : 4 * (c * d) * (X * Y * Z * W) = P * (4 * (X * Y * Z * W)) := by
      calc 4 * (c * d) * (X * Y * Z * W) = 4 * (c * X * W) * (d * Y * Z) := by ring
        _ = 4 * A₂ * B₂ := by rw [← hA₂_eq, ← hB₂_eq]
        _ = Nat.factorial n₂ := h4mul2
        _ = P * Nat.factorial n₁ := (P_ratio_mul_factorial hlt).symm
        _ = P * (4 * (X * Y * Z * W)) := by rw [hprod]
    have h4xyzw : 0 < 4 * (X * Y * Z * W) := by positivity
    exact Nat.mul_right_cancel h4xyzw h1
  have hab_eq : a * b = P - 1 := by
    have hUV : 4 * U * V = Nat.factorial n₂ - Nat.factorial n₁ := by
      have h1 : 2 * U = m₂ - m₁ := by change 2 * ((m₂ - m₁) / 2) = m₂ - m₁; omega
      have h2 : 2 * V = m₂ + m₁ := by change 2 * ((m₂ + m₁) / 2) = m₂ + m₁; omega
      zify [le_of_lt hm_lt, Nat.factorial_le (le_of_lt hlt)] at h1 h2 ⊢
      have hm1z : (Nat.factorial n₁ : ℤ) + 1 = (m₁ : ℤ) ^ 2 := by exact_mod_cast hm₁
      have hm2z : (Nat.factorial n₂ : ℤ) + 1 = (m₂ : ℤ) ^ 2 := by exact_mod_cast hm₂
      nlinarith
    have h1 : 4 * (a * b) * (X * Y * Z * W) = (P - 1) * (4 * (X * Y * Z * W)) := by
      calc 4 * (a * b) * (X * Y * Z * W) = 4 * (a * X * Y) * (b * Z * W) := by ring
        _ = 4 * U * V := by rw [← hU_eq, ← hV_eq]
        _ = Nat.factorial n₂ - Nat.factorial n₁ := hUV
        _ = P * Nat.factorial n₁ - 1 * Nat.factorial n₁ := by rw [P_ratio_mul_factorial hlt, one_mul]
        _ = (P - 1) * Nat.factorial n₁ := (Nat.sub_mul P 1 (Nat.factorial n₁)).symm
        _ = (P - 1) * (4 * (X * Y * Z * W)) := by rw [hprod]
    have h4xyzw : 0 < 4 * (X * Y * Z * W) := by positivity
    exact Nat.mul_right_cancel h4xyzw h1
  -- eq. (6.3)
  have hZ_lin : (Z : ℤ) = (c : ℤ) * W - (a : ℤ) * Y := by
    have hXz : (0 : ℤ) < X := by exact_mod_cast hX_pos
    have h : (X : ℤ) * Z = (X : ℤ) * ((c : ℤ) * W - (a : ℤ) * Y) := by
      have : (U : ℤ) + A₁ = A₂ := by exact_mod_cast hU_eq1
      have hA₁z : (A₁ : ℤ) = X * Z := by exact_mod_cast hA₁_eq
      have hA₂z : (A₂ : ℤ) = c * X * W := by exact_mod_cast hA₂_eq
      have hUz : (U : ℤ) = a * X * Y := by exact_mod_cast hU_eq
      linarith
    exact mul_left_cancel₀ hXz.ne' h
  have hW_lin : (W : ℤ) = (d : ℤ) * Z - (a : ℤ) * X := by
    have hYz : (0 : ℤ) < Y := by exact_mod_cast hY_pos
    have h : (Y : ℤ) * W = (Y : ℤ) * ((d : ℤ) * Z - (a : ℤ) * X) := by
      have : (U : ℤ) + B₁ = B₂ := by exact_mod_cast hU_eq2
      have hB₁z : (B₁ : ℤ) = Y * W := by exact_mod_cast hB₁_eq
      have hB₂z : (B₂ : ℤ) = d * Y * Z := by exact_mod_cast hB₂_eq
      have hUz : (U : ℤ) = a * X * Y := by exact_mod_cast hU_eq
      linarith
    exact mul_left_cancel₀ hYz.ne' h
  have hY_lin : (Y : ℤ) = (b : ℤ) * Z - (c : ℤ) * X := by
    have hWz : (0 : ℤ) < W := by exact_mod_cast hW_pos
    have h : (W : ℤ) * Y = (W : ℤ) * ((b : ℤ) * Z - (c : ℤ) * X) := by
      have : (V : ℤ) = A₂ + B₁ := by exact_mod_cast hV_eq1
      have hB₁z : (B₁ : ℤ) = Y * W := by exact_mod_cast hB₁_eq
      have hA₂z : (A₂ : ℤ) = c * X * W := by exact_mod_cast hA₂_eq
      have hVz : (V : ℤ) = b * Z * W := by exact_mod_cast hV_eq
      linarith
    exact mul_left_cancel₀ hWz.ne' h
  have hX_lin : (X : ℤ) = (b : ℤ) * W - (d : ℤ) * Y := by
    have hZz : (0 : ℤ) < Z := by exact_mod_cast hZ_pos
    have h : (Z : ℤ) * X = (Z : ℤ) * ((b : ℤ) * W - (d : ℤ) * Y) := by
      have : (V : ℤ) = B₂ + A₁ := by exact_mod_cast hV_eq2
      have hA₁z : (A₁ : ℤ) = X * Z := by exact_mod_cast hA₁_eq
      have hB₂z : (B₂ : ℤ) = d * Y * Z := by exact_mod_cast hB₂_eq
      have hVz : (V : ℤ) = b * Z * W := by exact_mod_cast hV_eq
      linarith
    exact mul_left_cancel₀ hZz.ne' h
  have hYW_XZ : (Y : ℤ) * W - (X : ℤ) * Z = 1 := by
    have h1 : (B₁ : ℤ) - A₁ = 1 := by
      have : B₁ = A₁ + 1 := hB₁_succ
      omega
    have hA₁z : (A₁ : ℤ) = X * Z := by exact_mod_cast hA₁_eq
    have hB₁z : (B₁ : ℤ) = Y * W := by exact_mod_cast hB₁_eq
    linarith
  have hdY_cX : (d : ℤ) * (Y : ℤ) ^ 2 - (c : ℤ) * (X : ℤ) ^ 2 = (b : ℤ) := by
    have h1 : (X : ℤ) + d * Y = b * W := by linarith
    have h2 : (Y : ℤ) + c * X = b * Z := by linarith
    calc (d : ℤ) * (Y : ℤ) ^ 2 - (c : ℤ) * (X : ℤ) ^ 2
        = ((X : ℤ) + d * Y) * Y - ((Y : ℤ) + c * X) * X := by ring
      _ = (b * W) * Y - (b * Z) * X := by rw [h1, h2]
      _ = b * ((Y : ℤ) * W - X * Z) := by ring
      _ = b := by rw [hYW_XZ, mul_one]
  have hcW_dZ : (c : ℤ) * (W : ℤ) ^ 2 - (d : ℤ) * (Z : ℤ) ^ 2 = (a : ℤ) := by
    have h1 : (c : ℤ) * W - Z = a * Y := by linarith
    have h2' : (d : ℤ) * Z - W = a * X := by linarith
    calc (c : ℤ) * (W : ℤ) ^ 2 - (d : ℤ) * (Z : ℤ) ^ 2
        = ((c : ℤ) * W - Z) * W - ((d : ℤ) * Z - W) * Z := by ring
      _ = (a * Y) * W - (a * X) * Z := by rw [h1, h2']
      _ = a * ((Y : ℤ) * W - X * Z) := by ring
      _ = a := by rw [hYW_XZ, mul_one]
  -- eq. (6.4)
  have hcdz : (c : ℤ) * d = P := by exact_mod_cast hcd_eq
  have habz : (a : ℤ) * b = (P : ℤ) - 1 := by
    have : 1 ≤ P := by omega
    zify [this] at hab_eq; exact hab_eq
  have hm1z : (m₁ : ℤ) = A₁ + B₁ := by
    change (m₁ : ℤ) = ((m₁ - 1) / 2 : ℕ) + ((m₁ + 1) / 2 : ℕ); omega
  have hm2z : (m₂ : ℤ) = A₂ + B₂ := by
    change (m₂ : ℤ) = ((m₂ - 1) / 2 : ℕ) + ((m₂ + 1) / 2 : ℕ); omega
  have h2U : 2 * (a : ℤ) * X * Y = (m₂ : ℤ) - m₁ := by
    have h1 : (2 * U : ℕ) = m₂ - m₁ := by change 2 * ((m₂ - m₁) / 2) = m₂ - m₁; omega
    have h2 : (U : ℤ) = a * X * Y := by exact_mod_cast hU_eq
    zify [le_of_lt hm_lt] at h1; linarith
  have h2V : 2 * (b : ℤ) * Z * W = (m₂ : ℤ) + m₁ := by
    have h1 : (2 * V : ℕ) = m₂ + m₁ := by change 2 * ((m₂ + m₁) / 2) = m₂ + m₁; omega
    have h2 : (V : ℤ) = b * Z * W := by exact_mod_cast hV_eq
    omega
  have hm2_sq : (m₂ : ℤ) ^ 2 = (P : ℤ) * (m₁ : ℤ) ^ 2 - ((P : ℤ) - 1) := by
    have h1 : (Nat.factorial n₁ : ℤ) + 1 = (m₁ : ℤ) ^ 2 := by exact_mod_cast hm₁
    have h2 : (Nat.factorial n₂ : ℤ) + 1 = (m₂ : ℤ) ^ 2 := by exact_mod_cast hm₂
    have h3 : (P : ℤ) * (Nat.factorial n₁ : ℤ) = (Nat.factorial n₂ : ℤ) := by
      exact_mod_cast P_ratio_mul_factorial hlt
    linarith
  have hPm1_gt : (m₂ : ℤ) < (P : ℤ) * m₁ := by
    have hP2 : (2 : ℤ) ≤ P := by exact_mod_cast hP_ge
    have hm1_pos : (0 : ℤ) < m₁ := by exact_mod_cast (show 0 < m₁ by omega)
    have hsq_lt : (m₂ : ℤ) ^ 2 < ((P : ℤ) * m₁) ^ 2 := by
      have : ((P : ℤ) * m₁) ^ 2 - (m₂ : ℤ) ^ 2 =
          (P : ℤ) * ((P : ℤ) - 1) * (m₁ : ℤ) ^ 2 + ((P : ℤ) - 1) := by
        rw [hm2_sq]; ring
      nlinarith
    nlinarith
  have hsum_XY : (a : ℤ) * d * (Y : ℤ) ^ 2 + (a : ℤ) * c * (X : ℤ) ^ 2 = (P : ℤ) * m₁ - m₂ := by
    have hsq : ((a : ℤ) * d * (Y : ℤ) ^ 2 + (a : ℤ) * c * (X : ℤ) ^ 2) ^ 2 =
        ((P : ℤ) * m₁ - m₂) ^ 2 := by
      have hdiff : (a : ℤ) * d * (Y : ℤ) ^ 2 - (a : ℤ) * c * (X : ℤ) ^ 2 = (P : ℤ) - 1 := by
        calc (a : ℤ) * d * (Y : ℤ) ^ 2 - (a : ℤ) * c * (X : ℤ) ^ 2
            = (a : ℤ) * (d * Y ^ 2 - c * X ^ 2) := by ring
          _ = (a : ℤ) * b := by rw [hdY_cX]
          _ = (P : ℤ) - 1 := habz
      calc ((a : ℤ) * d * (Y : ℤ) ^ 2 + (a : ℤ) * c * (X : ℤ) ^ 2) ^ 2
          = ((a : ℤ) * d * (Y : ℤ) ^ 2 - (a : ℤ) * c * (X : ℤ) ^ 2) ^ 2 +
            (c * d) * (2 * (a : ℤ) * X * Y) ^ 2 := by ring
        _ = ((P : ℤ) - 1) ^ 2 + (P : ℤ) * ((m₂ : ℤ) - m₁) ^ 2 := by
          rw [hdiff, hcdz, h2U]
        _ = ((P : ℤ) * m₁ - m₂) ^ 2 := by
          have : (P : ℤ) * (m₂ : ℤ) ^ 2 = (P : ℤ) ^ 2 * (m₁ : ℤ) ^ 2 - (P : ℤ) * ((P : ℤ) - 1) := by
            rw [hm2_sq]; ring
          linear_combination this
    have hnonneg : 0 ≤ (a : ℤ) * d * (Y : ℤ) ^ 2 + (a : ℤ) * c * (X : ℤ) ^ 2 := by positivity
    nlinarith
  have hsum_ZW : (b : ℤ) * c * (W : ℤ) ^ 2 + (b : ℤ) * d * (Z : ℤ) ^ 2 = (P : ℤ) * m₁ + m₂ := by
    have hsq : ((b : ℤ) * c * (W : ℤ) ^ 2 + (b : ℤ) * d * (Z : ℤ) ^ 2) ^ 2 =
        ((P : ℤ) * m₁ + m₂) ^ 2 := by
      have hdiff : (b : ℤ) * c * (W : ℤ) ^ 2 - (b : ℤ) * d * (Z : ℤ) ^ 2 = (P : ℤ) - 1 := by
        calc (b : ℤ) * c * (W : ℤ) ^ 2 - (b : ℤ) * d * (Z : ℤ) ^ 2
            = (b : ℤ) * (c * W ^ 2 - d * Z ^ 2) := by ring
          _ = (b : ℤ) * a := by rw [hcW_dZ]
          _ = (a : ℤ) * b := by ring
          _ = (P : ℤ) - 1 := habz
      calc ((b : ℤ) * c * (W : ℤ) ^ 2 + (b : ℤ) * d * (Z : ℤ) ^ 2) ^ 2
          = ((b : ℤ) * c * (W : ℤ) ^ 2 - (b : ℤ) * d * (Z : ℤ) ^ 2) ^ 2 +
            (c * d) * (2 * (b : ℤ) * Z * W) ^ 2 := by ring
        _ = ((P : ℤ) - 1) ^ 2 + (P : ℤ) * ((m₂ : ℤ) + m₁) ^ 2 := by
          rw [hdiff, hcdz, h2V]
        _ = ((P : ℤ) * m₁ + m₂) ^ 2 := by
          have : (P : ℤ) * (m₂ : ℤ) ^ 2 = (P : ℤ) ^ 2 * (m₁ : ℤ) ^ 2 - (P : ℤ) * ((P : ℤ) - 1) := by
            rw [hm2_sq]; ring
          linear_combination this
    have hnonneg : 0 ≤ (b : ℤ) * c * (W : ℤ) ^ 2 + (b : ℤ) * d * (Z : ℤ) ^ 2 := by positivity
    nlinarith
  have hdiff_XY : (a : ℤ) * d * (Y : ℤ) ^ 2 - (a : ℤ) * c * (X : ℤ) ^ 2 = (P : ℤ) - 1 := by
    calc (a : ℤ) * d * (Y : ℤ) ^ 2 - (a : ℤ) * c * (X : ℤ) ^ 2
        = (a : ℤ) * (d * Y ^ 2 - c * X ^ 2) := by ring
      _ = (a : ℤ) * b := by rw [hdY_cX]
      _ = (P : ℤ) - 1 := habz
  have hdiff_ZW : (b : ℤ) * c * (W : ℤ) ^ 2 - (b : ℤ) * d * (Z : ℤ) ^ 2 = (P : ℤ) - 1 := by
    calc (b : ℤ) * c * (W : ℤ) ^ 2 - (b : ℤ) * d * (Z : ℤ) ^ 2
        = (b : ℤ) * (c * W ^ 2 - d * Z ^ 2) := by ring
      _ = (b : ℤ) * a := by rw [hcW_dZ]
      _ = (a : ℤ) * b := by ring
      _ = (P : ℤ) - 1 := habz
  refine ⟨(a, b, c, d), ⟨ha_pos, hb_pos, hc_pos, hd_pos, hab_eq, hcd_eq,
    hA₂_eq, hB₂_eq, hU_eq, hV_eq,
    ⟨hZ_lin, hW_lin, hY_lin, hX_lin, hdY_cX, hcW_dZ⟩,
    ⟨by linarith, by linarith, by linarith, by linarith⟩⟩, ?_⟩
  rintro ⟨a', b', c', d'⟩ ⟨_, _, _, _, _, _, hA₂', hB₂', hU', hV', _, _⟩
  have ha' : a' = a := by
    have h : a' * (X * Y) = a * (X * Y) := by
      calc a' * (X * Y) = a' * X * Y := (mul_assoc _ _ _).symm
        _ = U := hU'.symm
        _ = a * X * Y := hU_eq
        _ = a * (X * Y) := mul_assoc _ _ _
    exact mul_right_cancel₀ (mul_pos hX_pos hY_pos).ne' h
  have hb' : b' = b := by
    have h : b' * (Z * W) = b * (Z * W) := by
      calc b' * (Z * W) = b' * Z * W := (mul_assoc _ _ _).symm
        _ = V := hV'.symm
        _ = b * Z * W := hV_eq
        _ = b * (Z * W) := mul_assoc _ _ _
    exact mul_right_cancel₀ (mul_pos hZ_pos hW_pos).ne' h
  have hc' : c' = c := by
    have h : c' * (X * W) = c * (X * W) := by
      calc c' * (X * W) = c' * X * W := (mul_assoc _ _ _).symm
        _ = A₂ := hA₂'.symm
        _ = c * X * W := hA₂_eq
        _ = c * (X * W) := mul_assoc _ _ _
    exact mul_right_cancel₀ (mul_pos hX_pos hW_pos).ne' h
  have hd' : d' = d := by
    have h : d' * (Y * Z) = d * (Y * Z) := by
      calc d' * (Y * Z) = d' * Y * Z := (mul_assoc _ _ _).symm
        _ = B₂ := hB₂'.symm
        _ = d * Y * Z := hB₂_eq
        _ = d * (Y * Z) := mul_assoc _ _ _
    exact mul_right_cancel₀ (mul_pos hY_pos hZ_pos).ne' h
  simp [ha', hb', hc', hd']

/-- **Proposition 6.1(ii)**: Twin norm identities in `ℤ[√P]` (eq. 6.5). -/
theorem prop_6_1_part2_zsqrtd_identities {n₁ n₂ m₁ m₂ a b c d : ℕ}
    (hn₁ : 4 ≤ n₁) (hlt : n₁ < n₂)
    (hm₁ : Nat.factorial n₁ + 1 = m₁ ^ 2) (hm₂ : Nat.factorial n₂ + 1 = m₂ ^ 2)
    (hcd : c * d = P_ratio n₁ n₂)
    (hA₂ : A_sol m₂ = c * X_gcd m₁ m₂ * W_gcd m₁ m₂)
    (hB₂ : B_sol m₂ = d * Y_gcd m₁ m₂ * Z_gcd m₁ m₂)
    (hdY : (d : ℤ) * (Y_gcd m₁ m₂ : ℤ) ^ 2 - (c : ℤ) * (X_gcd m₁ m₂ : ℤ) ^ 2 = b)
    (hcW : (c : ℤ) * (W_gcd m₁ m₂ : ℤ) ^ 2 - (d : ℤ) * (Z_gcd m₁ m₂ : ℤ) ^ 2 = a) :
    let P := P_ratio n₁ n₂
    let X := X_gcd m₁ m₂; let Y := Y_gcd m₁ m₂
    let Z := Z_gcd m₁ m₂; let W := W_gcd m₁ m₂
    let α₁ : Zsqrtd (P : ℤ) := ⟨(d : ℤ) * Y, (X : ℤ)⟩
    let α₂ : Zsqrtd (P : ℤ) := ⟨(c : ℤ) * W, (Z : ℤ)⟩
    α₁.norm = (b : ℤ) * d ∧
    α₂.norm = (a : ℤ) * c ∧
    α₁ * α₂ = ⟨(P : ℤ) * m₁, (m₂ : ℤ)⟩ ∧
    α₁ * star α₂ = ⟨(P : ℤ), -1⟩ ∧
    ((a : ℤ) * c : Zsqrtd (P : ℤ)) * α₁ = ⟨(P : ℤ), -1⟩ * α₂ := by
  have ⟨_, _, _, _, _, _, _, _, _, _, hA₁_eq, hB₁_eq, _⟩ :=
    prop_6_1_coprime_and_factorization hn₁ hlt hm₁ hm₂
  have ⟨_, _, hB₁_succ, _, _, _, _⟩ := brocard_u1_u2_rel hn₁ hm₁
  have ⟨_, _, hB₂_succ, _, _, _, _⟩ := brocard_u1_u2_rel (by omega) hm₂
  set P := P_ratio n₁ n₂
  set X := X_gcd m₁ m₂; set Y := Y_gcd m₁ m₂
  set Z := Z_gcd m₁ m₂; set W := W_gcd m₁ m₂
  set α₁ : Zsqrtd (P : ℤ) := ⟨(d : ℤ) * Y, (X : ℤ)⟩
  set α₂ : Zsqrtd (P : ℤ) := ⟨(c : ℤ) * W, (Z : ℤ)⟩
  have hcdz : (c : ℤ) * d = P := by exact_mod_cast hcd
  have hA₁z : (A_sol m₁ : ℤ) = X * Z := by exact_mod_cast hA₁_eq
  have hB₁z : (B_sol m₁ : ℤ) = Y * W := by exact_mod_cast hB₁_eq
  have hA₂z : (A_sol m₂ : ℤ) = c * X * W := by exact_mod_cast hA₂
  have hB₂z : (B_sol m₂ : ℤ) = d * Y * Z := by exact_mod_cast hB₂
  have hm1z : (m₁ : ℤ) = (X : ℤ) * Z + Y * W := by
    have : m₁ = A_sol m₁ + B_sol m₁ := by
      change m₁ = (m₁ - 1) / 2 + (m₁ + 1) / 2
      have ⟨_, _⟩ := brocard_m_odd (by omega) hm₁; omega
    omega
  have hm2z : (m₂ : ℤ) = (c : ℤ) * X * W + d * Y * Z := by
    have : m₂ = A_sol m₂ + B_sol m₂ := by
      change m₂ = (m₂ - 1) / 2 + (m₂ + 1) / 2
      have ⟨_, _⟩ := brocard_m_odd (by omega) hm₂; omega
    omega
  have hYW_XZ : (Y : ℤ) * W - X * Z = 1 := by
    have : B_sol m₁ = A_sol m₁ + 1 := hB₁_succ
    omega
  have hB₂_A₂ : (d : ℤ) * Y * Z - c * X * W = 1 := by
    have : B_sol m₂ = A_sol m₂ + 1 := hB₂_succ
    omega
  have hn1 : α₁.norm = (b : ℤ) * d := by
    simp only [α₁, Zsqrtd.norm_def]
    calc ((d : ℤ) * Y) * ((d : ℤ) * Y) - (P : ℤ) * (X : ℤ) * (X : ℤ)
        = ((d : ℤ) * Y) ^ 2 - (c * d) * (X : ℤ) ^ 2 := by rw [hcdz]; ring
      _ = (d : ℤ) * (d * Y ^ 2 - c * X ^ 2) := by ring
      _ = (d : ℤ) * b := by rw [hdY]
      _ = (b : ℤ) * d := by ring
  have hn2 : α₂.norm = (a : ℤ) * c := by
    simp only [α₂, Zsqrtd.norm_def]
    calc ((c : ℤ) * W) * ((c : ℤ) * W) - (P : ℤ) * (Z : ℤ) * (Z : ℤ)
        = ((c : ℤ) * W) ^ 2 - (c * d) * (Z : ℤ) ^ 2 := by rw [hcdz]; ring
      _ = (c : ℤ) * (c * W ^ 2 - d * Z ^ 2) := by ring
      _ = (c : ℤ) * a := by rw [hcW]
      _ = (a : ℤ) * c := by ring
  have hmul12 : α₁ * α₂ = ⟨(P : ℤ) * m₁, (m₂ : ℤ)⟩ := by
    apply Zsqrtd.ext
    · simp only [α₁, α₂]
      calc (d : ℤ) * Y * (c * W) + (P : ℤ) * X * Z
          = (c * d) * (Y * W) + P * (X * Z) := by ring
        _ = (P : ℤ) * (X * Z + Y * W) := by rw [hcdz]; ring
        _ = (P : ℤ) * m₁ := by rw [hm1z]
    · simp only [α₁, α₂]
      rw [hm2z]; ring
  have hmul_conj : α₁ * star α₂ = ⟨(P : ℤ), -1⟩ := by
    apply Zsqrtd.ext
    · simp only [α₁, α₂]
      calc (d : ℤ) * Y * (c * W) + (P : ℤ) * X * (-Z)
          = (c * d) * (Y * W) - P * (X * Z) := by ring
        _ = (P : ℤ) * (Y * W - X * Z) := by rw [hcdz]; ring
        _ = P := by rw [hYW_XZ, mul_one]
    · simp only [α₁, α₂]
      linarith
  have hdiv : ((a : ℤ) * c : Zsqrtd (P : ℤ)) * α₁ = ⟨(P : ℤ), -1⟩ * α₂ := by
    have hnorm_eq : α₂ * star α₂ = ((a : ℤ) * c : Zsqrtd (P : ℤ)) := by
      apply Zsqrtd.ext
      · simp only [α₂]
        have := hn2
        simp only [α₂, Zsqrtd.norm_def] at this
        linarith
      · simp only [α₂]
        ring
    calc ((a : ℤ) * c : Zsqrtd (P : ℤ)) * α₁
        = (α₂ * star α₂) * α₁ := by rw [hnorm_eq]
      _ = (α₁ * star α₂) * α₂ := by ring
      _ = ⟨(P : ℤ), -1⟩ * α₂ := by rw [hmul_conj]
  exact ⟨hn1, hn2, hmul12, hmul_conj, hdiv⟩

/-- **Proposition 6.1(iii)**: At every odd prime `p ≤ n₁` with `p ∤ P(P - 1)`, the four
Legendre characters satisfy `χ_T(p) = +1` whenever `p ∣ T` (`T ∈ {X, Y, Z, W}`), and
obey the Quadrant IV lock `(1 + (-P/p)) * (1 + (-(P-1)/p)) * (1 - (bd/p)) = 0` (eq. 6.6). -/
theorem prop_6_1_part3_characters_and_quadrant_iv {n₁ n₂ m₁ m₂ a b c d p : ℕ}
    (hn₁ : 4 ≤ n₁) (hlt : n₁ < n₂)
    (hm₁ : Nat.factorial n₁ + 1 = m₁ ^ 2) (hm₂ : Nat.factorial n₂ + 1 = m₂ ^ 2)
    (hab : a * b = P_ratio n₁ n₂ - 1) (hcd : c * d = P_ratio n₁ n₂)
    (hdY : (d : ℤ) * (Y_gcd m₁ m₂ : ℤ) ^ 2 - (c : ℤ) * (X_gcd m₁ m₂ : ℤ) ^ 2 = b)
    (hcW : (c : ℤ) * (W_gcd m₁ m₂ : ℤ) ^ 2 - (d : ℤ) * (Z_gcd m₁ m₂ : ℤ) ^ 2 = a)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn₁ : p ≤ n₁) (hp_ndvd : ¬ p ∣ P_ratio n₁ n₂ * (P_ratio n₁ n₂ - 1)) :
    let P := P_ratio n₁ n₂
    let X := X_gcd m₁ m₂; let Y := Y_gcd m₁ m₂
    let Z := Z_gcd m₁ m₂; let W := W_gcd m₁ m₂
    (p ∣ X → chiLegendre ((b : ℤ) * d) p = 1) ∧
    (p ∣ Y → chiLegendre (-(b : ℤ) * c) p = 1) ∧
    (p ∣ Z → chiLegendre ((a : ℤ) * c) p = 1) ∧
    (p ∣ W → chiLegendre (-(a : ℤ) * d) p = 1) ∧
    (1 + chiLegendre (-(P : ℤ)) p) * (1 + chiLegendre (-((P : ℤ) - 1)) p) *
      (1 - chiLegendre ((b : ℤ) * d) p) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ⟨_, _, _, _, hXY, hXZ, hXW, hYZ, hYW, hZW, _, _, hprod⟩ :=
    prop_6_1_coprime_and_factorization hn₁ hlt hm₁ hm₂
  set P := P_ratio n₁ n₂
  set X := X_gcd m₁ m₂; set Y := Y_gcd m₁ m₂
  set Z := Z_gcd m₁ m₂; set W := W_gcd m₁ m₂
  have hp_nP : ¬ p ∣ P := fun h => hp_ndvd (dvd_mul_of_dvd_left h _)
  have hp_nPm1 : ¬ p ∣ P - 1 := fun h => hp_ndvd (dvd_mul_of_dvd_right h _)
  have hp_na : ¬ p ∣ a := fun h => hp_nPm1 (hab ▸ dvd_mul_of_dvd_left h _)
  have hp_nb : ¬ p ∣ b := fun h => hp_nPm1 (hab ▸ dvd_mul_of_dvd_right h _)
  have hp_nc : ¬ p ∣ c := fun h => hp_nP (hcd ▸ dvd_mul_of_dvd_left h _)
  have hp_nd : ¬ p ∣ d := fun h => hp_nP (hcd ▸ dvd_mul_of_dvd_right h _)
  have hmod_nz : ∀ k : ℕ, ¬ p ∣ k → (k : ZMod p) ≠ 0 := by
    intro k hnk h0
    exact hnk ((ZMod.natCast_eq_zero_iff k p).mp h0)
  have hbd_nz : (((b : ℤ) * d : ℤ) : ZMod p) ≠ 0 := by
    push_cast; exact mul_ne_zero (hmod_nz b hp_nb) (hmod_nz d hp_nd)
  have hbc_nz : ((-(b : ℤ) * c : ℤ) : ZMod p) ≠ 0 := by
    push_cast; exact mul_ne_zero (neg_ne_zero.mpr (hmod_nz b hp_nb)) (hmod_nz c hp_nc)
  have hac_nz : (((a : ℤ) * c : ℤ) : ZMod p) ≠ 0 := by
    push_cast; exact mul_ne_zero (hmod_nz a hp_na) (hmod_nz c hp_nc)
  have had_nz : ((-(a : ℤ) * d : ℤ) : ZMod p) ≠ 0 := by
    push_cast; exact mul_ne_zero (neg_ne_zero.mpr (hmod_nz a hp_na)) (hmod_nz d hp_nd)
  have hP_nz : ((-(P : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    push_cast; exact neg_ne_zero.mpr (hmod_nz P hp_nP)
  have hPm1_nz : ((-((P : ℤ) - 1) : ℤ) : ZMod p) ≠ 0 := by
    have h1 : 1 ≤ P := by have := P_ratio_ge_two hn₁ hlt; omega
    have : -((P : ℤ) - 1) = -(((P - 1 : ℕ) : ℤ)) := by omega
    rw [this]; push_cast; exact neg_ne_zero.mpr (hmod_nz (P - 1) hp_nPm1)
  have h_chiX : p ∣ X → chiLegendre ((b : ℤ) * d) p = 1 := by
    intro hpX
    have hX0 : (X : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff X p).mpr hpX
    have hrel : (d : ZMod p) * (Y : ZMod p) ^ 2 - (c : ZMod p) * (X : ZMod p) ^ 2 = (b : ZMod p) := by
      have h := congrArg (Int.cast : ℤ → ZMod p) hdY
      push_cast at h
      exact h
    rw [hX0, zero_pow (by norm_num), mul_zero, sub_zero] at hrel
    simp only [chiLegendre, dif_pos hp]
    refine (legendreSym.eq_one_iff p hbd_nz).mpr ⟨(d : ZMod p) * (Y : ZMod p), ?_⟩
    push_cast; rw [← hrel]; ring
  have h_chiY : p ∣ Y → chiLegendre (-(b : ℤ) * c) p = 1 := by
    intro hpY
    have hY0 : (Y : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff Y p).mpr hpY
    have hrel : (d : ZMod p) * (Y : ZMod p) ^ 2 - (c : ZMod p) * (X : ZMod p) ^ 2 = (b : ZMod p) := by
      have h := congrArg (Int.cast : ℤ → ZMod p) hdY
      push_cast at h
      exact h
    rw [hY0, zero_pow (by norm_num), mul_zero, zero_sub] at hrel
    simp only [chiLegendre, dif_pos hp]
    refine (legendreSym.eq_one_iff p hbc_nz).mpr ⟨(c : ZMod p) * (X : ZMod p), ?_⟩
    push_cast
    calc -((b : ZMod p)) * (c : ZMod p) = -(-((c : ZMod p) * (X : ZMod p) ^ 2)) * (c : ZMod p) := by rw [hrel]
      _ = (c : ZMod p) * (X : ZMod p) * ((c : ZMod p) * (X : ZMod p)) := by ring
  have h_chiZ : p ∣ Z → chiLegendre ((a : ℤ) * c) p = 1 := by
    intro hpZ
    have hZ0 : (Z : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff Z p).mpr hpZ
    have hrel : (c : ZMod p) * (W : ZMod p) ^ 2 - (d : ZMod p) * (Z : ZMod p) ^ 2 = (a : ZMod p) := by
      have h := congrArg (Int.cast : ℤ → ZMod p) hcW
      push_cast at h
      exact h
    rw [hZ0, zero_pow (by norm_num), mul_zero, sub_zero] at hrel
    simp only [chiLegendre, dif_pos hp]
    refine (legendreSym.eq_one_iff p hac_nz).mpr ⟨(c : ZMod p) * (W : ZMod p), ?_⟩
    push_cast; rw [← hrel]; ring
  have h_chiW : p ∣ W → chiLegendre (-(a : ℤ) * d) p = 1 := by
    intro hpW
    have hW0 : (W : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff W p).mpr hpW
    have hrel : (c : ZMod p) * (W : ZMod p) ^ 2 - (d : ZMod p) * (Z : ZMod p) ^ 2 = (a : ZMod p) := by
      have h := congrArg (Int.cast : ℤ → ZMod p) hcW
      push_cast at h
      exact h
    rw [hW0, zero_pow (by norm_num), mul_zero, zero_sub] at hrel
    simp only [chiLegendre, dif_pos hp]
    refine (legendreSym.eq_one_iff p had_nz).mpr ⟨(d : ZMod p) * (Z : ZMod p), ?_⟩
    push_cast
    calc -((a : ZMod p)) * (d : ZMod p) = -(-((d : ZMod p) * (Z : ZMod p) ^ 2)) * (d : ZMod p) := by rw [hrel]
      _ = (d : ZMod p) * (Z : ZMod p) * ((d : ZMod p) * (Z : ZMod p)) := by ring
  have hlock : (1 + chiLegendre (-(P : ℤ)) p) * (1 + chiLegendre (-((P : ℤ) - 1)) p) *
      (1 - chiLegendre ((b : ℤ) * d) p) = 0 := by
    have hp_dvd_fac : p ∣ Nat.factorial n₁ := Nat.dvd_factorial hp.pos hpn₁
    have hp_dvd_xyzw : p ∣ X * Y * Z * W := by
      rw [← hprod] at hp_dvd_fac
      exact (hp.dvd_mul.mp hp_dvd_fac).resolve_left (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from h))))
    have hp_or : p ∣ X ∨ p ∣ Y ∨ p ∣ Z ∨ p ∣ W := by
      rcases hp.dvd_mul.mp hp_dvd_xyzw with h3 | hW
      · rcases hp.dvd_mul.mp h3 with h2 | hZ
        · rcases hp.dvd_mul.mp h2 with hX | hY
          · exact Or.inl hX
          · exact Or.inr (Or.inl hY)
        · exact Or.inr (Or.inr (Or.inl hZ))
      · exact Or.inr (Or.inr (Or.inr hW))
    have hcdz : (c : ℤ) * d = P := by exact_mod_cast hcd
    have habz : (a : ℤ) * b = (P : ℤ) - 1 := by
      have : 1 ≤ P := by have := P_ratio_ge_two hn₁ hlt; omega
      zify [this] at hab; exact hab
    simp only [chiLegendre, dif_pos hp]
    have hχY_rel : legendreSym p (-(b : ℤ) * c) =
        legendreSym p (-(P : ℤ)) * legendreSym p ((b : ℤ) * d) := by
      have hsq : (-(b : ℤ) * c) * d ^ 2 = (-(P : ℤ)) * ((b : ℤ) * d) := by
        rw [← hcdz]; ring
      have hd2 : legendreSym p ((d : ℤ) ^ 2) = 1 :=
        (legendreSym.eq_one_iff p (pow_ne_zero 2 (by push_cast; exact hmod_nz d hp_nd))).mpr ⟨(d : ZMod p), by push_cast; ring⟩
      calc legendreSym p (-(b : ℤ) * c)
          = legendreSym p (-(b : ℤ) * c) * legendreSym p ((d : ℤ) ^ 2) := by rw [hd2, mul_one]
        _ = legendreSym p ((-(b : ℤ) * c) * (d : ℤ) ^ 2) := (legendreSym.mul p _ _).symm
        _ = legendreSym p ((-(P : ℤ)) * ((b : ℤ) * d)) := by rw [hsq]
        _ = legendreSym p (-(P : ℤ)) * legendreSym p ((b : ℤ) * d) := legendreSym.mul p _ _
    have hχW_rel : legendreSym p (-(a : ℤ) * d) =
        legendreSym p (-((P : ℤ) - 1)) * legendreSym p ((b : ℤ) * d) := by
      have hsq : (-(a : ℤ) * d) * b ^ 2 = (-((P : ℤ) - 1)) * ((b : ℤ) * d) := by
        rw [← habz]; ring
      have hb2 : legendreSym p ((b : ℤ) ^ 2) = 1 :=
        (legendreSym.eq_one_iff p (pow_ne_zero 2 (by push_cast; exact hmod_nz b hp_nb))).mpr ⟨(b : ZMod p), by push_cast; ring⟩
      calc legendreSym p (-(a : ℤ) * d)
          = legendreSym p (-(a : ℤ) * d) * legendreSym p ((b : ℤ) ^ 2) := by rw [hb2, mul_one]
        _ = legendreSym p ((-(a : ℤ) * d) * (b : ℤ) ^ 2) := (legendreSym.mul p _ _).symm
        _ = legendreSym p ((-((P : ℤ) - 1)) * ((b : ℤ) * d)) := by rw [hsq]
        _ = legendreSym p (-((P : ℤ) - 1)) * legendreSym p ((b : ℤ) * d) := legendreSym.mul p _ _
    have hχZ_rel : legendreSym p ((a : ℤ) * c) =
        legendreSym p (-(P : ℤ)) * legendreSym p (-((P : ℤ) - 1)) * legendreSym p ((b : ℤ) * d) := by
      have hsq : ((a : ℤ) * c) * (b * d) ^ 2 = (-(P : ℤ)) * (-((P : ℤ) - 1)) * ((b : ℤ) * d) := by
        rw [← habz, ← hcdz]; ring
      have hbd2 : legendreSym p (((b : ℤ) * d) ^ 2) = 1 :=
        (legendreSym.eq_one_iff p (pow_ne_zero 2 hbd_nz)).mpr ⟨(b : ZMod p) * (d : ZMod p), by push_cast; ring⟩
      calc legendreSym p ((a : ℤ) * c)
          = legendreSym p ((a : ℤ) * c) * legendreSym p (((b : ℤ) * d) ^ 2) := by rw [hbd2, mul_one]
        _ = legendreSym p (((a : ℤ) * c) * ((b : ℤ) * d) ^ 2) := (legendreSym.mul p _ _).symm
        _ = legendreSym p (((-(P : ℤ)) * (-((P : ℤ) - 1))) * ((b : ℤ) * d)) := by rw [hsq]
        _ = legendreSym p (-(P : ℤ)) * legendreSym p (-((P : ℤ) - 1)) * legendreSym p ((b : ℤ) * d) := by
          rw [legendreSym.mul, legendreSym.mul]
    have hP_pm1 : legendreSym p (-(P : ℤ)) = 1 ∨ legendreSym p (-(P : ℤ)) = -1 :=
      (legendreSym.eq_one_or_neg_one p hP_nz)
    have hPm1_pm1 : legendreSym p (-((P : ℤ) - 1)) = 1 ∨ legendreSym p (-((P : ℤ) - 1)) = -1 :=
      (legendreSym.eq_one_or_neg_one p hPm1_nz)
    rcases hP_pm1 with hP1 | hPneg1
    · rcases hPm1_pm1 with hPm1 | hPm1neg1
      · have hbd_eq1 : legendreSym p ((b : ℤ) * d) = 1 := by
          rcases hp_or with hX | hY | hZ | hW
          · have h := h_chiX hX; simp only [chiLegendre, dif_pos hp] at h; exact h
          · have h := h_chiY hY; simp only [chiLegendre, dif_pos hp] at h
            rw [hχY_rel, hP1, one_mul] at h; exact h
          · have h := h_chiZ hZ; simp only [chiLegendre, dif_pos hp] at h
            rw [hχZ_rel, hP1, hPm1, one_mul, one_mul] at h; exact h
          · have h := h_chiW hW; simp only [chiLegendre, dif_pos hp] at h
            rw [hχW_rel, hPm1, one_mul] at h; exact h
        rw [hbd_eq1]; ring
      · rw [hPm1neg1]; ring
    · rw [hPneg1]; ring
  exact ⟨h_chiX, h_chiY, h_chiZ, h_chiW, hlock⟩

end GrasGreenbergBrocard
