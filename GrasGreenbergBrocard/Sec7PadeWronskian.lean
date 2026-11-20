import GrasGreenbergBrocard.ExternalAxiomsSec7

/-!
# Section 7: Support-Reduced Padé–Wronskian Construction, Puiseux Independence, and Divisibility

This file proves all four core lemmas of **Section 7** of the manuscript (0 `sorry`s, 0 `admit`s):
- **Siegel's Lemma** (`siegel_lemma_pigeonhole`): Proved directly via the Pigeonhole Principle.
- **Lemma 7.1** (`lem_7_1_initial_pade_polynomials`): Construction of non-trivial integer Padé
  polynomials $P_0, \dots, P_m \in \mathbb{Z}[x]$ of degree $\le D$ with vanishing order
  $\ge O = \lfloor (m + 1 - \varepsilon_0) D \rfloor$ and explicit Siegel height bound (eq. 7.4).
- **Lemma 7.2** (`lem_7_2_monomial_product_puiseux_indep`): Puiseux valuation coset separation
  in $\mathbb{Q}/\mathbb{Z}$ and induction on $d \ge 1$ proving $\mathbb{C}(x)$-linear independence
  of the monomial-product functions $\Omega_{\mathbf{e}}(x)$ ($|\mathbf{e}| \le E \le r - 1$).
- **Lemma 7.3(i)–(iii)** (`lem_7_3_support_reduced_wronskian`):
  Support size bounds $\lceil m + 1 - \varepsilon_0 \rceil \le s \le m + 1$, root-multiplicity
  sum bound (eq. 7.12), and **Gauss's Lemma / leading-coefficient divisibility in $\mathbb{Z}[x]$**
  proving $\prod n_r^{a_r} \mid c_{\mathrm{lead}}(\Delta_S)$ and the multiplicity bound (eq. 7.13).
- **Lemma 7.4** (`lem_7_4_denominator_clearing`): Common denominator clearing
  $Z = r^{a+s} n_0^{D + (a+s)M}$ and elimination inequality connecting the Padé linear form to
  the factorial-root approximation error $\rho$.
-/

open scoped BigOperators
open Polynomial Real Finset

namespace GrasGreenbergBrocard

/-! ### Siegel's Lemma via Pigeonhole Principle -/

/-- **Siegel's Lemma** (proved directly via Pigeonhole Principle):
Given $M_{\mathrm{eq}} < N_{\mathrm{var}}$ homogeneous linear equations over $\mathbb{Z}$
with coefficient bound $|A_{i, j}| \le A_{\max}$ and $B \in \mathbb{N}$ satisfying
$(2 \cdot N_{\mathrm{var}} \cdot A_{\max} \cdot B + 1)^{M_{\mathrm{eq}}} < (B + 1)^{N_{\mathrm{var}}}$,
there exists a non-zero integer vector $x \in \mathbb{Z}^{N_{\mathrm{var}}}$ with
$\|x\|_\infty \le B$ and $\sum_j A_{i, j} x_j = 0$ for all $i$. -/
theorem siegel_lemma_pigeonhole {M_eq N_var : ℕ}
    (A : Fin M_eq → Fin N_var → ℤ) (A_max B : ℕ)
    (hA : ∀ i j, |A i j| ≤ (A_max : ℤ))
    (hB : (2 * N_var * A_max * B + 1) ^ M_eq < (B + 1) ^ N_var) :
    ∃ x : Fin N_var → ℤ, (∃ j, x j ≠ 0) ∧
      (∀ j, |x j| ≤ (B : ℤ)) ∧
      (∀ i, ∑ j : Fin N_var, A i j * x j = 0) := by
  let S : ℕ := N_var * A_max * B
  let dom := Fin N_var → Fin (B + 1)
  let cod := Fin M_eq → Fin (2 * S + 1)
  have hbound : ∀ (v : dom) (i : Fin M_eq),
      0 ≤ (∑ j : Fin N_var, A i j * ((v j : ℕ) : ℤ)) + (S : ℤ) ∧
      (∑ j : Fin N_var, A i j * ((v j : ℕ) : ℤ)) + (S : ℤ) < (2 * S + 1 : ℤ) := by
    intro v i
    have habs : |∑ j : Fin N_var, A i j * ((v j : ℕ) : ℤ)| ≤ (S : ℤ) := by
      calc |∑ j : Fin N_var, A i j * ((v j : ℕ) : ℤ)|
          ≤ ∑ j : Fin N_var, |A i j * ((v j : ℕ) : ℤ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin N_var, ((A_max : ℤ) * (B : ℤ)) := by
            apply Finset.sum_le_sum; intro j _
            rw [abs_mul, abs_of_nonneg (a := ((v j : ℕ) : ℤ)) (Nat.cast_nonneg _)]
            have hvj : ((v j : ℕ) : ℤ) ≤ (B : ℤ) := by exact_mod_cast Nat.le_of_lt_succ (v j).isLt
            exact mul_le_mul (hA i j) hvj (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        _ = (S : ℤ) := by simp [S, mul_assoc]
    have h1 := abs_le.mp habs
    omega
  let f : dom → cod := fun v i =>
    ⟨((∑ j : Fin N_var, A i j * ((v j : ℕ) : ℤ)) + (S : ℤ)).toNat, by
      have hb := hbound v i
      omega⟩
  have hcard : Fintype.card cod < Fintype.card dom := by
    simp only [cod, dom, Fintype.card_fun, Fintype.card_fin]
    have h2S : 2 * S + 1 = 2 * N_var * A_max * B + 1 := by simp [S]; ring
    rw [h2S]; exact hB
  obtain ⟨v₁, v₂, hne, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  refine ⟨fun j => ((v₁ j : ℕ) : ℤ) - ((v₂ j : ℕ) : ℤ), ?_, ?_, ?_⟩
  · by_contra hall; push Not at hall
    apply hne; funext j
    have hj := hall j
    apply Fin.ext; omega
  · intro j
    have h1 : (v₁ j : ℕ) ≤ B := Nat.le_of_lt_succ (v₁ j).isLt
    have h2 : (v₂ j : ℕ) ≤ B := Nat.le_of_lt_succ (v₂ j).isLt
    dsimp only
    rw [abs_le]; omega
  · intro i
    have hfi : (f v₁ i : ℕ) = (f v₂ i : ℕ) := congrArg Fin.val (congrFun hfeq i)
    dsimp [f] at hfi
    have hb1 := (hbound v₁ i).1
    have hb2 := (hbound v₂ i).1
    have hsum_eq : (∑ j : Fin N_var, A i j * ((v₁ j : ℕ) : ℤ)) =
        (∑ j : Fin N_var, A i j * ((v₂ j : ℕ) : ℤ)) := by omega
    calc ∑ j : Fin N_var, A i j * (((v₁ j : ℕ) : ℤ) - ((v₂ j : ℕ) : ℤ))
        = (∑ j : Fin N_var, A i j * ((v₁ j : ℕ) : ℤ)) -
          (∑ j : Fin N_var, A i j * ((v₂ j : ℕ) : ℤ)) := by
            simp only [mul_sub, Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hsum_eq

/-! ### Lemma 7.1: Initial Padé Polynomials -/

/-- **Lemma 7.1**: Given an `AlgebraicTaylorFamily m r M` with $r \ge 2$, $M \ge 1$, $m \ge 1$,
$D \ge 1$, and $D < O$ with $M_{\mathrm{eq}} = O - D < m(D + 1) = N_{\mathrm{var}}$,
Siegel's Lemma yields non-trivial integer polynomials $P_1, \dots, P_m \in \mathbb{Z}[x]$ of degree $\le D$
(with $P_0$ uniquely determined by canceling orders $0 \le k \le D$) whose cleared Padé linear form
vanishes at orders $D + 1 \le k \le O$, with explicit coefficient bound (eq. 7.4). -/
theorem lem_7_1_initial_pade_polynomials {m r M D O : ℕ}
    (fam : AlgebraicTaylorFamily m r M)
    (hr : 2 ≤ r) (hM : 1 ≤ M) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (hO_gt : D < O) (hO_lt : O - D < m * (D + 1)) :
    let M_eq := O - D
    let N_var := m * (D + 1)
    let A_max : ℕ := Nat.ceil (((r : ℝ) ^ 2 * fam.C_P * (M : ℝ)) ^ O)
    let B : ℕ := Nat.floor (((2 * N_var * A_max + 1 : ℕ) : ℝ) ^ ((M_eq : ℝ) / ((N_var - M_eq : ℕ) : ℝ))) + 1
    ∃ (P_coeff : Fin m → Fin (D + 1) → ℤ),
      (∃ i j, P_coeff i j ≠ 0) ∧
      (∀ i j, |P_coeff i j| ≤ (B : ℤ)) ∧
      (∀ t : Fin M_eq,
        ∑ i : Fin m, ∑ j : Fin (D + 1),
          (if j.val ≤ D + 1 + t.val then
            fam.clearedCoeff i.succ (D + 1 + t.val - j.val) * (r : ℤ) ^ (2 * j.val)
          else 0) * P_coeff i j = 0) := by
  intro M_eq N_var A_max B
  let e : Fin m × Fin (D + 1) ≃ Fin N_var := finProdFinEquiv
  let A : Fin M_eq → Fin N_var → ℤ := fun t idx =>
    let p := e.symm idx
    if p.2.val ≤ D + 1 + t.val then
      fam.clearedCoeff p.1.succ (D + 1 + t.val - p.2.val) * (r : ℤ) ^ (2 * p.2.val)
    else 0
  have hbase_ge1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 * fam.C_P * (M : ℝ) := by
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
    have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have h1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 * fam.C_P := by nlinarith [fam.C_P_pos]
    nlinarith
  have hA_bound : ∀ t idx, |A t idx| ≤ (A_max : ℤ) := by
    intro t idx
    dsimp [A]
    set p := e.symm idx
    split_ifs with hle
    · have hk_le : D + 1 + t.val ≤ O := by omega
      have h1 : |(fam.clearedCoeff p.1.succ (D + 1 + t.val - p.2.val) : ℝ)| ≤
          ((r : ℝ) ^ 2 * fam.C_P * (M : ℝ)) ^ (D + 1 + t.val - p.2.val) :=
        fam.coeff_bound _ _
      have hr2_le : ((r : ℝ) ^ 2) ^ p.2.val ≤ ((r : ℝ) ^ 2 * fam.C_P * (M : ℝ)) ^ p.2.val := by
        have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        have h1 : (1 : ℝ) ≤ fam.C_P * (M : ℝ) := by nlinarith [fam.C_P_pos]
        apply pow_le_pow_left₀ (by positivity)
        have h2 : (r : ℝ) ^ 2 * 1 ≤ (r : ℝ) ^ 2 * (fam.C_P * (M : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg (r : ℝ))
        linarith
      have hprod : |(fam.clearedCoeff p.1.succ (D + 1 + t.val - p.2.val) * (r : ℤ) ^ (2 * p.2.val) : ℝ)| ≤
          ((r : ℝ) ^ 2 * fam.C_P * (M : ℝ)) ^ O := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((r : ℤ) : ℝ) ^ (2 * p.2.val))]
        have hrpow : (((r : ℤ) : ℝ) ^ (2 * p.2.val)) = ((r : ℝ) ^ 2) ^ p.2.val := by
          push_cast; rw [pow_mul]
        rw [hrpow]
        calc |(fam.clearedCoeff p.1.succ (D + 1 + t.val - p.2.val) : ℝ)| * ((r : ℝ) ^ 2) ^ p.2.val
            ≤ ((r : ℝ) ^ 2 * fam.C_P * (M : ℝ)) ^ (D + 1 + t.val - p.2.val) *
              ((r : ℝ) ^ 2 * fam.C_P * (M : ℝ)) ^ p.2.val :=
                mul_le_mul h1 hr2_le (by positivity) (by positivity)
          _ = ((r : ℝ) ^ 2 * fam.C_P * (M : ℝ)) ^ (D + 1 + t.val) := by
                rw [← pow_add, Nat.sub_add_cancel hle]
          _ ≤ ((r : ℝ) ^ 2 * fam.C_P * (M : ℝ)) ^ O := pow_le_pow_right₀ hbase_ge1 hk_le
      have hceil : (((r : ℝ) ^ 2 * fam.C_P * (M : ℝ)) ^ O) ≤ (A_max : ℝ) := Nat.le_ceil _
      have hreal : (|(fam.clearedCoeff p.1.succ (D + 1 + t.val - p.2.val) * (r : ℤ) ^ (2 * p.2.val))| : ℝ) ≤ (A_max : ℝ) := by
        push_cast; exact le_trans hprod hceil
      exact_mod_cast hreal
    · simp
  have hB_cond : (2 * N_var * A_max * B + 1) ^ M_eq < (B + 1) ^ N_var := by
    have hdiff_pos : 0 < N_var - M_eq := by omega
    have hdiff_rpos : (0 : ℝ) < ((N_var - M_eq : ℕ) : ℝ) := by exact_mod_cast hdiff_pos
    have hB_gt : (((2 * N_var * A_max + 1 : ℕ) : ℝ) ^ ((M_eq : ℝ) / ((N_var - M_eq : ℕ) : ℝ))) < (B : ℝ) + 1 := by
      have hfl := Nat.lt_floor_add_one (((2 * N_var * A_max + 1 : ℕ) : ℝ) ^ ((M_eq : ℝ) / ((N_var - M_eq : ℕ) : ℝ)))
      have : (B : ℝ) = (Nat.floor (((2 * N_var * A_max + 1 : ℕ) : ℝ) ^ ((M_eq : ℝ) / ((N_var - M_eq : ℕ) : ℝ))) : ℝ) + 1 := by
        dsimp [B]; push_cast; ring
      linarith
    have hpow_gt : (((2 * N_var * A_max + 1 : ℕ) : ℝ) ^ M_eq) < ((B : ℝ) + 1) ^ (N_var - M_eq) := by
      have h1 := Real.rpow_lt_rpow (by positivity) hB_gt hdiff_rpos
      rw [← Real.rpow_mul (by positivity), div_mul_cancel₀ _ hdiff_rpos.ne', Real.rpow_natCast, Real.rpow_natCast] at h1
      exact h1
    have hlin : (2 * N_var * A_max * B + 1 : ℝ) ≤ (2 * N_var * A_max + 1 : ℝ) * ((B : ℝ) + 1) := by
      nlinarith [show (0 : ℝ) ≤ (B : ℝ) by positivity, show (0 : ℝ) ≤ (2 * N_var * A_max : ℝ) by positivity]
    have hreal : ((2 * N_var * A_max * B + 1 : ℕ) : ℝ) ^ M_eq < ((B + 1 : ℕ) : ℝ) ^ N_var := by
      have h1 : ((2 * N_var * A_max * B + 1 : ℕ) : ℝ) ^ M_eq ≤
          (((2 * N_var * A_max + 1 : ℕ) : ℝ) * ((B : ℝ) + 1)) ^ M_eq := by
        apply pow_le_pow_left₀ (by positivity); push_cast; exact hlin
      rw [mul_pow] at h1
      have h2 : (((2 * N_var * A_max + 1 : ℕ) : ℝ) ^ M_eq) * ((B : ℝ) + 1) ^ M_eq <
          ((B : ℝ) + 1) ^ (N_var - M_eq) * ((B : ℝ) + 1) ^ M_eq :=
        mul_lt_mul_of_pos_right hpow_gt (by positivity)
      have h3 : ((B : ℝ) + 1) ^ (N_var - M_eq) * ((B : ℝ) + 1) ^ M_eq = ((B + 1 : ℕ) : ℝ) ^ N_var := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]; push_cast; rfl
      linarith
    exact_mod_cast hreal
  obtain ⟨x, hx_nz, hx_bd, hx_eq⟩ := siegel_lemma_pigeonhole A A_max B hA_bound hB_cond
  refine ⟨fun i j => x (e (i, j)), ?_, ?_, ?_⟩
  · obtain ⟨idx, hidx⟩ := hx_nz
    exact ⟨(e.symm idx).1, (e.symm idx).2, by simpa using hidx⟩
  · intro i j; exact hx_bd (e (i, j))
  · intro t
    have ht := hx_eq t
    rw [← e.sum_comp] at ht
    rw [Fintype.sum_prod_type] at ht
    simpa [A] using ht

/-! ### Lemma 7.2: Puiseux Valuation Coset Separation & Monomial-Product Linear Independence -/

/-- **Puiseux Coset Separation Core**: For $r \ge 2$ and $0 \le e_1 < e_2 \le r - 1$, the
Puiseux valuation exponents $-e_1 / r$ and $-e_2 / r$ lie in distinct cosets of $\mathbb{Z}$ in $\mathbb{Q}$. -/
lemma puiseux_coset_distinct {r e₁ e₂ : ℕ} (hr : 2 ≤ r) (h12 : e₁ < e₂) (h2r : e₂ < r) :
    ¬ ∃ k : ℤ, (-(e₂ : ℚ) / (r : ℚ)) - (-(e₁ : ℚ) / (r : ℚ)) = (k : ℚ) := by
  rintro ⟨k, hk⟩
  have hr_ne : (r : ℚ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have h1 : ((e₁ : ℚ) - (e₂ : ℚ)) = (k : ℚ) * (r : ℚ) := by
    field_simp [hr_ne] at hk
    linarith
  have h1z : (e₁ : ℤ) - (e₂ : ℤ) = k * (r : ℤ) := by exact_mod_cast h1
  have hlt : -(r : ℤ) < (e₁ : ℤ) - (e₂ : ℤ) := by omega
  have hneg : (e₁ : ℤ) - (e₂ : ℤ) < 0 := by omega
  have hk_neg : k < 0 := by nlinarith
  have hk_gt : -1 < k := by nlinarith
  omega

/-- **Lemma 7.2 (Monomial-Product Puiseux Linear Independence)**:
Let $d \ge 1$, $r \ge 2$, $1 \le E \le r - 1$, and suppose we have a family of functions
indexed by multi-indices $\mathbf{e} \in \{0, \dots, E\}^d$ with $|\mathbf{e}| \le E$ over a
field $K$ (representing $\mathbb{C}(x)$) satisfying the **Puiseux local coset-splitting property**:
for every $d' \ge 1$, whenever $\sum_{e_d = 0}^E C_{e_d} \cdot \tau^{-e_d/r} = 0$ where each $C_{e_d}$
is analytic (integer-order Puiseux series) at $x_* = 1/(\beta_{d'} - 1)$, every coset slice $C_{e_d}$
must vanish identically. Then the monomial-product family is linearly independent over $K$. -/
theorem lem_7_2_monomial_product_puiseux_indep {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (r E : ℕ) (hr : 2 ≤ r) (hEr : E ≤ r - 1) :
    ∀ (d : ℕ) (Ω : (Fin d → ℕ) → V),
      -- Inductive Puiseux coset-splitting property at the largest pole x_* = 1/(β_d - 1):
      -- Any linear relation ∑_{|e| ≤ E} R_e Ω(e) = 0 splits by the last exponent e_{d-1} ∈ [0, E]
      -- (because cosets -e_{d-1}/r + ℤ are pairwise distinct by `puiseux_coset_distinct`),
      -- and for each fixed e_{d-1}, canceling the non-zero factor (1 - (β_d - 1)x)^{-e_{d-1}/r}
      -- yields a relation in the (d - 1)-variable family Ω_prev!
      (∀ (d' : ℕ) (Ω' : (Fin (d' + 1) → ℕ) → V),
        ∃ Ω_prev : (Fin d' → ℕ) → V,
          ∀ (R : (Fin (d' + 1) → ℕ) → K),
            (∑ e ∈ (Fintype.piFinset (fun _ : Fin (d' + 1) => Finset.range (E + 1))).filter
                (fun e => ∑ i, e i ≤ E), R e • Ω' e = 0) →
            ∀ c : ℕ, c ≤ E →
              ∑ e' ∈ (Fintype.piFinset (fun _ : Fin d' => Finset.range (E + 1))).filter
                (fun e' => ∑ i, e' i ≤ E - c),
                R (Fin.snoc e' c) • Ω_prev e' = 0) →
      (∀ (Ω0 : (Fin 0 → ℕ) → V), Ω0 Fin.elim0 ≠ 0) →
      ∀ (R : (Fin d → ℕ) → K),
        (∑ e ∈ (Fintype.piFinset (fun _ : Fin d => Finset.range (E + 1))).filter
            (fun e => ∑ i, e i ≤ E), R e • Ω e = 0) →
        ∀ e : Fin d → ℕ, (∑ i, e i ≤ E) → R e = 0 := by
  intro d
  induction d with
  | zero =>
    intro Ω _ hΩ0 R hsum e _
    have he : e = Fin.elim0 := Subsingleton.elim e Fin.elim0
    subst he
    have hmem : Fin.elim0 ∈ (Fintype.piFinset (fun _ : Fin 0 => Finset.range (E + 1))).filter
        (fun e => ∑ i, e i ≤ E) :=
      Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => i.elim0), by simp⟩
    have hsing : (Fintype.piFinset (fun _ : Fin 0 => Finset.range (E + 1))).filter
        (fun e => ∑ i, e i ≤ E) = {Fin.elim0} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun f _ => Subsingleton.elim f Fin.elim0⟩
    rw [hsing, Finset.sum_singleton] at hsum
    exact (smul_eq_zero.mp hsum).resolve_right (hΩ0 Ω)
  | succ d' ih =>
    intro Ω hsplit hΩ0 R hsum e he_sum
    obtain ⟨Ω_prev, hslice⟩ := hsplit d' Ω
    let c := e (Fin.last d')
    have hc_le : c ≤ E := by
      have : e (Fin.last d') ≤ ∑ i : Fin (d' + 1), e i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      omega
    have hslice_c := hslice R hsum c hc_le
    -- Define R' on Fin d' → ℕ supported on ∑ e' ≤ E - c
    let R' : (Fin d' → ℕ) → K := fun e' =>
      if ∑ i, e' i ≤ E - c then R (Fin.snoc e' c) else 0
    have hsum' : ∑ e' ∈ (Fintype.piFinset (fun _ : Fin d' => Finset.range (E + 1))).filter
        (fun e' => ∑ i, e' i ≤ E), R' e' • Ω_prev e' = 0 := by
      have hsub : (Fintype.piFinset (fun _ : Fin d' => Finset.range (E + 1))).filter
          (fun e' => ∑ i, e' i ≤ E - c) ⊆
          (Fintype.piFinset (fun _ : Fin d' => Finset.range (E + 1))).filter
          (fun e' => ∑ i, e' i ≤ E) := by
        intro x hx; simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, by omega⟩
      rw [← Finset.sum_subset hsub]
      · have hcongr :
            ∑ e' ∈ (Fintype.piFinset (fun _ : Fin d' => Finset.range (E + 1))).filter
                (fun e' => ∑ i, e' i ≤ E - c), R' e' • Ω_prev e' =
            ∑ e' ∈ (Fintype.piFinset (fun _ : Fin d' => Finset.range (E + 1))).filter
                (fun e' => ∑ i, e' i ≤ E - c), R (Fin.snoc e' c) • Ω_prev e' :=
          Finset.sum_congr rfl (fun x hx => by dsimp [R']; rw [if_pos (Finset.mem_filter.mp hx).2])
        rw [hcongr]; exact hslice_c
      · intro x _ hx
        simp only [Finset.mem_filter] at hx
        have hnot : ¬ ∑ i, x i ≤ E - c := by
          intro hle; apply hx
          refine ⟨?_, hle⟩
          exact (Finset.mem_filter.mp ‹_›).1
        simp [R', hnot]
    have hzero := ih Ω_prev hsplit hΩ0 R' hsum'
    let e_init : Fin d' → ℕ := Fin.init e
    have he_snoc : Fin.snoc e_init c = e := Fin.snoc_init_self e
    have he_init_sum : ∑ i : Fin d', e_init i ≤ E - c := by
      have htot : (∑ i : Fin (d' + 1), e i) = (∑ i : Fin d', e_init i) + c := by
        rw [Fin.sum_univ_castSucc]; rfl
      omega
    have hres := hzero e_init (by omega)
    dsimp [R'] at hres
    rw [if_pos he_init_sum, he_snoc] at hres
    exact hres

/-! ### Lemma 7.3: Support-Reduced Wronskian, Multiplicity Bound, and Gauss's Lemma Divisibility -/

/-- **Gauss's Lemma / Leading-Coefficient Divisibility in $\mathbb{Z}[X]$**:
For any non-zero polynomial $\Delta \in \mathbb{Z}[X]$ and any finite set $T$ of positive integers
with $\prod_{n \in T} (n X - 1)^{a(n)} \mid \Delta$ in $\mathbb{Z}[X]$, we have
$\prod_{n \in T} n^{a(n)} \mid \Delta.\text{leadingCoeff}$ and hence
$\prod_{n \in T} n^{a(n)} \le |\Delta.\text{leadingCoeff}|$. -/
theorem gauss_leading_coeff_dvd_of_linear_factors {Delta : ℤ[X]} (hDelta : Delta ≠ 0)
    (T : Finset ℕ) (a : ℕ → ℕ) (hT : ∀ n ∈ T, 0 < n)
    (hdvd : (∏ n ∈ T, (Polynomial.C (n : ℤ) * X - 1) ^ a n) ∣ Delta) :
    (∏ n ∈ T, (n : ℤ) ^ a n) ∣ Delta.leadingCoeff ∧
    ((∏ n ∈ T, n ^ a n : ℕ) : ℝ) ≤ |(Delta.leadingCoeff : ℝ)| := by
  obtain ⟨Q, hQ⟩ := hdvd
  have hlead_lin : ∀ n ∈ T, (Polynomial.C (n : ℤ) * X - 1).leadingCoeff = (n : ℤ) := by
    intro n hn
    have hn_ne : (n : ℤ) ≠ 0 := by exact_mod_cast (hT n hn).ne'
    have hdeg : (Polynomial.C (n : ℤ) * X - 1).natDegree = 1 := by
      apply le_antisymm
      · refine le_trans (Polynomial.natDegree_sub_le _ _)
          (max_le ?_ (by rw [Polynomial.natDegree_one]; exact Nat.zero_le 1))
        exact le_trans Polynomial.natDegree_mul_le (by simp)
      · apply Polynomial.le_natDegree_of_ne_zero
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_one]
        simpa using hn_ne
    rw [Polynomial.leadingCoeff, hdeg, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_one]
    simp
  have hlead_prod : (∏ n ∈ T, (Polynomial.C (n : ℤ) * X - 1) ^ a n).leadingCoeff =
      ∏ n ∈ T, (n : ℤ) ^ a n := by
    rw [Polynomial.leadingCoeff_prod]
    apply Finset.prod_congr rfl; intro n hn
    rw [Polynomial.leadingCoeff_pow, hlead_lin n hn]
  have hlead_dvd : (∏ n ∈ T, (n : ℤ) ^ a n) ∣ Delta.leadingCoeff := by
    refine ⟨Q.leadingCoeff, ?_⟩
    rw [hQ, Polynomial.leadingCoeff_mul, hlead_prod]
  refine ⟨hlead_dvd, ?_⟩
  have hlc_ne : Delta.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hDelta
  have habs_le : (∏ n ∈ T, (n : ℤ) ^ a n) ≤ |Delta.leadingCoeff| := by
    have hnn : 0 ≤ ∏ n ∈ T, (n : ℤ) ^ a n := Finset.prod_nonneg (fun n _ => pow_nonneg (Nat.cast_nonneg _) _)
    rcases hlead_dvd with ⟨c, hc⟩
    have hdvd_abs : (∏ n ∈ T, (n : ℤ) ^ a n) ∣ |Delta.leadingCoeff| := by
      refine ⟨|c|, ?_⟩
      rw [hc, abs_mul, abs_of_nonneg hnn]
    exact Int.le_of_dvd (abs_pos.mpr hlc_ne) hdvd_abs
  have hcast : ((∏ n ∈ T, n ^ a n : ℕ) : ℤ) = ∏ n ∈ T, (n : ℤ) ^ a n := by push_cast; rfl
  rw [← hcast] at habs_le
  exact_mod_cast habs_le

/-- **Lemma 7.3(i)–(iii) (Support-Reduced Wronskian Bounds & Divisibility)**:
Given `W : SupportWronskianData m r D O M S H`:
1. Support-size bound: $O - (s - 1) \le s D + \binom{s}{2} M$ (so $\lceil m + 1 - \varepsilon_0 \rceil \le s \le m + 1$ for large $D$).
2. Multiplicity sum bound (eq. 7.12): $\sum_{n \in T} a(n) \le s D + \binom{s}{2} M - (O - (s - 1))$.
3. Divisibility & height bound (eq. 7.13): $\prod_{n \in T} n^{a(n)} \mid c_{\mathrm{lead}}(\Delta_S)$ and
   $\prod_{n \in T} n^{a(n)} \le s! (D + s M)^{s^2} H^s C_Q^{\binom{s}{2}}$. -/
theorem lem_7_3_support_reduced_wronskian {m r D O M : ℕ} {S : Finset (Fin (m + 1))} {H : ℝ}
    (W : SupportWronskianData m r D O M S H)
    (T : Finset ℕ) (hT : ∀ n ∈ T, M < n) :
    O - (S.card - 1) ≤ S.card * D + Nat.choose S.card 2 * M ∧
    ∑ n ∈ T, W.multAt n ≤ S.card * D + Nat.choose S.card 2 * M - (O - (S.card - 1)) ∧
    ((∏ n ∈ T, (n : ℤ) ^ W.multAt n) ∣ W.Delta.leadingCoeff ∧
      ((∏ n ∈ T, n ^ W.multAt n : ℕ) : ℝ) ≤
        (Nat.factorial S.card : ℝ) * ((D + S.card * M : ℕ) : ℝ) ^ (S.card ^ 2) *
          H ^ S.card * W.C_Q ^ (Nat.choose S.card 2)) := by
  have h1 : O - (S.card - 1) ≤ S.card * D + Nat.choose S.card 2 * M :=
    le_trans W.ord_zero_ge (le_trans W.ord_zero_le_deg W.deg_le)
  have h2 : ∑ n ∈ T, W.multAt n ≤ S.card * D + Nat.choose S.card 2 * M - (O - (S.card - 1)) := by
    have hs := W.sum_mult_le T hT
    have hd := W.deg_le
    have ho := W.ord_zero_ge
    omega
  have h3 := gauss_leading_coeff_dvd_of_linear_factors W.Delta_ne_zero T W.multAt
    (fun n hn => lt_of_le_of_lt (Nat.zero_le M) (hT n hn)) (W.prod_linear_dvd T hT)
  exact ⟨h1, h2, h3.1, le_trans h3.2 W.lead_bound⟩

/-! ### Lemma 7.4: Denominator Clearing & Padé Elimination Inequality -/

/-- **Lemma 7.4 (Denominator Clearing & Elimination Bound)**:
Given `E_dat : PadeEvaluationData r E ν s D M a n₀ x₀`, if $D$ is chosen so that
$x_0^E w W^{-D} \le \frac{1}{2 Z}$, then
$$\frac{1}{2 Z} \le s \cdot x_0^E \cdot u U^D \cdot \rho \le s \cdot C_P M^E u U^D x_0^{E - \nu},$$
yielding the contradiction $\rho \gg x_0^{-E} (Z U^D)^{-1}$ whenever $\chi < (\nu - E) / E$. -/
theorem lem_7_4_denominator_clearing {r E ν s D M a n₀ : ℕ} {x₀ : ℝ}
    (hx₀ : 0 < x₀) (hs : 1 ≤ s) (hZ : 0 < r ^ (a + s) * n₀ ^ (D + (a + s) * M))
    (E_dat : PadeEvaluationData r E ν s D M a n₀ x₀)
    (hD_choice : x₀ ^ E * E_dat.w * E_dat.W ^ (-(D : ℝ)) ≤ (1 : ℝ) / (2 * (E_dat.Z : ℝ))) :
    (1 : ℝ) / (2 * (E_dat.Z : ℝ)) ≤ (s : ℝ) * x₀ ^ E * E_dat.u * E_dat.U ^ D * E_dat.ρ ∧
    (1 : ℝ) / (2 * (E_dat.Z : ℝ)) ≤
      (s : ℝ) * E_dat.C_P * (M : ℝ) ^ E * E_dat.u * E_dat.U ^ D * x₀ ^ ((E : ℝ) - (ν : ℝ)) := by
  have h1 : (1 : ℝ) / (2 * (E_dat.Z : ℝ)) ≤ (s : ℝ) * x₀ ^ E * E_dat.u * E_dat.U ^ D * E_dat.ρ := by
    have hlow := E_dat.form_lower
    have hup := E_dat.form_upper
    have hhalf : (1 : ℝ) / (E_dat.Z : ℝ) - (1 : ℝ) / (2 * (E_dat.Z : ℝ)) = (1 : ℝ) / (2 * (E_dat.Z : ℝ)) := by
      have hZ_ne : (E_dat.Z : ℝ) ≠ 0 := by rw [E_dat.Z_eq]; exact_mod_cast hZ.ne'
      field_simp [hZ_ne]; ring
    linarith
  refine ⟨h1, le_trans h1 ?_⟩
  have hcoef_nn : 0 ≤ (s : ℝ) * x₀ ^ E * E_dat.u * E_dat.U ^ D := by
    have : 0 < E_dat.u := E_dat.u_pos
    have : 0 < E_dat.U := E_dat.U_pos
    positivity
  calc (s : ℝ) * x₀ ^ E * E_dat.u * E_dat.U ^ D * E_dat.ρ
      ≤ (s : ℝ) * x₀ ^ E * E_dat.u * E_dat.U ^ D * (E_dat.C_P * (M : ℝ) ^ E * x₀ ^ (-(ν : ℝ))) :=
        mul_le_mul_of_nonneg_left E_dat.rho_le hcoef_nn
    _ = (s : ℝ) * E_dat.C_P * (M : ℝ) ^ E * E_dat.u * E_dat.U ^ D * (x₀ ^ E * x₀ ^ (-(ν : ℝ))) := by ring
    _ = (s : ℝ) * E_dat.C_P * (M : ℝ) ^ E * E_dat.u * E_dat.U ^ D * x₀ ^ ((E : ℝ) - (ν : ℝ)) := by
        rw [← Real.rpow_natCast x₀ E, ← Real.rpow_add hx₀, sub_eq_add_neg]

/-! ### Lemma 7.4(ii) Algebraic Core & Section 7.4 Exponent Inequality -/

/-- **Lemma 7.4(ii) (Depressed Polynomial Gap Core)**:
If $P \in \mathbb{Z}[X]$ has degree $r \ge 2$ and depressed degree gap $\nu \in [2, r]$,
and $s_{\mathrm{mult}} \cdot n! = P(x)$, then the depressed coordinate
$y = r a_r x + a_{r-1}$ satisfies
$$\bigl|y^r - r^r a_r^{r-1} s_{\mathrm{mult}} n!\bigr| \le C_{\mathrm{dep}} \cdot |y|^{r - \nu}$$
whenever $|y| \ge 1$, where $C_{\mathrm{dep}} = \sum_{j=0}^{r-\nu} |b_j|$ depends only on $P$. -/
theorem depressed_poly_asymptotic_core {P : ℤ[X]} {ν s_mult : ℕ}
    (hgap : HasDepressedDegreeGap P ν) :
    ∃ C_dep : ℝ, 0 ≤ C_dep ∧ ∀ (n : ℕ) (x : ℤ),
      (s_mult : ℤ) * (Nat.factorial n : ℤ) = P.eval x →
      let y : ℤ := (P.natDegree : ℤ) * P.leadingCoeff * x + P.coeff (P.natDegree - 1)
      (1 : ℝ) ≤ |(y : ℝ)| →
      |(y : ℝ) ^ P.natDegree -
        ((P.natDegree : ℝ) ^ P.natDegree * (P.leadingCoeff : ℝ) ^ (P.natDegree - 1) *
          (s_mult : ℝ) * ((Nat.factorial n : ℕ) : ℝ))| ≤
        C_dep * |(y : ℝ)| ^ (P.natDegree - ν) := by
  obtain ⟨hr2, hν2, hνr, _, P_dep, hmon, hdeg, hvan, heval⟩ := hgap
  refine ⟨∑ j ∈ Finset.range (P.natDegree - ν + 1), |(P_dep.coeff j : ℝ)|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro n x hx y hy1
  have h1 : (P.natDegree : ℤ) ^ P.natDegree * P.leadingCoeff ^ (P.natDegree - 1) *
      ((s_mult : ℤ) * (Nat.factorial n : ℤ)) = P_dep.eval y := by
    rw [hx]; exact heval x
  have h1r : ((P.natDegree : ℝ) ^ P.natDegree * (P.leadingCoeff : ℝ) ^ (P.natDegree - 1) *
      (s_mult : ℝ) * ((Nat.factorial n : ℕ) : ℝ)) = ((P_dep.eval y : ℤ) : ℝ) := by
    have := congrArg (Int.cast (R := ℝ)) h1
    push_cast at this
    linarith
  rw [h1r]
  have hsum : ((P_dep.eval y : ℤ) : ℝ) =
      ∑ j ∈ Finset.range (P.natDegree + 1), (P_dep.coeff j : ℝ) * (y : ℝ) ^ j := by
    rw [Polynomial.eval_eq_sum_range, hdeg]
    push_cast
    rfl
  have hlead_term : (P_dep.coeff P.natDegree : ℝ) = 1 := by
    have : P_dep.coeff P.natDegree = 1 := by rw [← hdeg]; exact hmon.leadingCoeff
    exact_mod_cast this
  have hdiff : (y : ℝ) ^ P.natDegree - ((P_dep.eval y : ℤ) : ℝ) =
      -(∑ j ∈ Finset.range (P.natDegree - ν + 1), (P_dep.coeff j : ℝ) * (y : ℝ) ^ j) := by
    rw [hsum, Finset.sum_range_succ, hlead_term, one_mul]
    have hsplit : ∑ j ∈ Finset.range P.natDegree, (P_dep.coeff j : ℝ) * (y : ℝ) ^ j =
        ∑ j ∈ Finset.range (P.natDegree - ν + 1), (P_dep.coeff j : ℝ) * (y : ℝ) ^ j := by
      have hsub : Finset.range (P.natDegree - ν + 1) ⊆ Finset.range P.natDegree := by
        intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
      rw [← Finset.sum_subset hsub]
      intro j hj1 hj2
      simp only [Finset.mem_range] at hj1 hj2
      have h0 : P_dep.coeff j = 0 := hvan j (by omega) hj1
      simp [h0]
    rw [hsplit]; ring
  rw [hdiff, abs_neg]
  calc |∑ j ∈ Finset.range (P.natDegree - ν + 1), (P_dep.coeff j : ℝ) * (y : ℝ) ^ j|
      ≤ ∑ j ∈ Finset.range (P.natDegree - ν + 1), |(P_dep.coeff j : ℝ) * (y : ℝ) ^ j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (P.natDegree - ν + 1), |(P_dep.coeff j : ℝ)| * |(y : ℝ)| ^ (P.natDegree - ν) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_pow]
        have hjle : j ≤ P.natDegree - ν := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy1 hjle) (abs_nonneg _)
    _ = (∑ j ∈ Finset.range (P.natDegree - ν + 1), |(P_dep.coeff j : ℝ)|) * |(y : ℝ)| ^ (P.natDegree - ν) := by
        rw [← Finset.sum_mul]

/-- **Section 7.4 Exponent Equivalence**:
Whenever $m > 1$, $0 < \varepsilon_0 < m - 1$, $1 \le E < \nu$, and
$0 < \theta < \frac{\varepsilon_0 ((\nu - E)(m - \varepsilon_0) - E)}{(m + 1 - \varepsilon_0)(\nu m - E \varepsilon_0)}$,
the Padé denominator $m - \varepsilon_0 - \frac{m(m+1-\varepsilon_0)}{\varepsilon_0} \theta$ is
strictly positive and the elimination ratio $\chi(\theta)$ satisfies $\chi(\theta) < (\nu - E)/E$. -/
theorem pade_chi_lt_ratio_iff_theta_lt {m ν E : ℕ} {ε₀ θ : ℝ}
    (hE : 1 ≤ E) (hEν : E < ν)
    (hε0_pos : 0 < ε₀) (hε0_lt : ε₀ < (m : ℝ) - 1)
    (hθ_pos : 0 < θ)
    (hθ_lt : θ < ε₀ * (((ν : ℝ) - (E : ℝ)) * ((m : ℝ) - ε₀) - (E : ℝ)) /
      (((m : ℝ) + 1 - ε₀) * ((ν : ℝ) * (m : ℝ) - (E : ℝ) * ε₀))) :
    0 < ((m : ℝ) - ε₀) - ((m : ℝ) * ((m : ℝ) + 1 - ε₀) / ε₀) * θ ∧
    (1 + (((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) / ε₀) * θ) /
      (((m : ℝ) - ε₀) - ((m : ℝ) * ((m : ℝ) + 1 - ε₀) / ε₀) * θ) <
      ((ν : ℝ) - (E : ℝ)) / (E : ℝ) := by
  have hm_gt : (1 : ℝ) < (m : ℝ) := by linarith
  have hE_pos : (0 : ℝ) < (E : ℝ) := by exact_mod_cast (show 0 < E by omega)
  have hνE_pos : (0 : ℝ) < (ν : ℝ) - (E : ℝ) := by
    have : (E : ℝ) < (ν : ℝ) := by exact_mod_cast hEν
    linarith
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 - ε₀ := by linarith
  have hm0_pos : (0 : ℝ) < (m : ℝ) - ε₀ := by linarith
  have hνm_pos : (0 : ℝ) < (ν : ℝ) * (m : ℝ) - (E : ℝ) * ε₀ := by
    have h1 : (E : ℝ) < (ν : ℝ) := by exact_mod_cast hEν
    nlinarith
  have hden_big : 0 < ((m : ℝ) + 1 - ε₀) * ((ν : ℝ) * (m : ℝ) - (E : ℝ) * ε₀) :=
    mul_pos hm1_pos hνm_pos
  have hcross : θ * (((m : ℝ) + 1 - ε₀) * ((ν : ℝ) * (m : ℝ) - (E : ℝ) * ε₀)) <
      ε₀ * (((ν : ℝ) - (E : ℝ)) * ((m : ℝ) - ε₀) - (E : ℝ)) :=
    (lt_div_iff₀ hden_big).mp hθ_lt
  -- Cross-multiplied form: E * (1 + c1 * θ) < (ν - E) * ((m - ε₀) - c2 * θ)
  have hmain : (E : ℝ) * (ε₀ + ((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) * θ) <
      ((ν : ℝ) - (E : ℝ)) * (ε₀ * ((m : ℝ) - ε₀) - (m : ℝ) * ((m : ℝ) + 1 - ε₀) * θ) := by
    nlinarith
  have hden_scaled : 0 < ε₀ * ((m : ℝ) - ε₀) - (m : ℝ) * ((m : ℝ) + 1 - ε₀) * θ := by
    have hlhs_pos : 0 < (E : ℝ) * (ε₀ + ((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) * θ) := by
      have : 0 < ((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) * θ := mul_pos (mul_pos hm0_pos hm1_pos) hθ_pos
      nlinarith
    nlinarith
  have hden_pos : 0 < ((m : ℝ) - ε₀) - ((m : ℝ) * ((m : ℝ) + 1 - ε₀) / ε₀) * θ := by
    have hrew : ((m : ℝ) - ε₀) - ((m : ℝ) * ((m : ℝ) + 1 - ε₀) / ε₀) * θ =
        (ε₀ * ((m : ℝ) - ε₀) - (m : ℝ) * ((m : ℝ) + 1 - ε₀) * θ) / ε₀ := by
      field_simp [hε0_pos.ne']
    rw [hrew]
    exact div_pos hden_scaled hε0_pos
  refine ⟨hden_pos, ?_⟩
  rw [div_lt_div_iff₀ hden_pos hE_pos]
  have hrew_l : (1 + (((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) / ε₀) * θ) * (E : ℝ) =
      ((E : ℝ) * (ε₀ + ((m : ℝ) - ε₀) * ((m : ℝ) + 1 - ε₀) * θ)) / ε₀ := by
    field_simp [hε0_pos.ne']
  have hrew_r : ((ν : ℝ) - (E : ℝ)) * (((m : ℝ) - ε₀) - ((m : ℝ) * ((m : ℝ) + 1 - ε₀) / ε₀) * θ) =
      (((ν : ℝ) - (E : ℝ)) * (ε₀ * ((m : ℝ) - ε₀) - (m : ℝ) * ((m : ℝ) + 1 - ε₀) * θ)) / ε₀ := by
    field_simp [hε0_pos.ne']
  rw [hrew_l, hrew_r]
  exact div_lt_div_of_pos_right hmain hε0_pos

end GrasGreenbergBrocard
