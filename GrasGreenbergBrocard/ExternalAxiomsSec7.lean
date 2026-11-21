import Mathlib
import GrasGreenbergBrocard.Sec7TaylorSeries

/-!
# External Axioms for Section 7 (Support-Reduced Padé–Wronskian & Monomial-Product Counting Bounds)

**Defect D1 (Part 1) resolved**: `canonicalMonomialTaylorFamily` is now a **concrete `def`**
constructed in `Sec7TaylorSeries.lean` inside Mathlib's `PowerSeries ℤ` with **zero external axioms**.

All remaining external axioms in this file represent established, peer-reviewed mathematical
results external to the manuscript's own contributions, canonically scoped to the concrete
monomial-product family and Padé polynomials:
1. **Siegel (1949), Ch. 2, Lemma 4; Bui–Pratt–Zaharescu (2023), Lemmas 5.4, 5.6, 6.3**
   (`canonicalSupportWronskian`)
2. **Bui–Pratt–Zaharescu (2023), Proposition 3.4 & Lemmas 5.6, 6.3**
   (`bpz_cauchy_leibniz_pade_eval`)
-/

open scoped BigOperators
open Polynomial Real Finset

namespace GrasGreenbergBrocard

/-- Solution predicate for a polynomial-factorial equation $s_{\mathrm{mult}} \cdot n! = P(x)$. -/
def IsPolyFactSol (s_mult : ℕ) (P : ℤ[X]) (n : ℕ) : Prop :=
  ∃ x : ℤ, (s_mult : ℤ) * (Nat.factorial n : ℤ) = P.eval x

/-- A polynomial $P \in \mathbb{Z}[X]$ of degree $r \ge 2$ has depressed degree gap $\nu$
($2 \le \nu \le r$) if its depressed polynomial $P_{\mathrm{dep}}(y) = y^r + \sum_{j=0}^{r-\nu} b_j y^j$
satisfies $r^r a_r^{r-1} P(x) = P_{\mathrm{dep}}(r a_r x + a_{r-1})$ for all $x \in \mathbb{Z}$. -/
def HasDepressedDegreeGap (P : ℤ[X]) (ν : ℕ) : Prop :=
  2 ≤ P.natDegree ∧ 2 ≤ ν ∧ ν ≤ P.natDegree ∧ P.leadingCoeff ≠ 0 ∧
  ∃ P_dep : ℤ[X], P_dep.Monic ∧ P_dep.natDegree = P.natDegree ∧
    (∀ j : ℕ, P.natDegree - ν < j → j < P.natDegree → P_dep.coeff j = 0) ∧
    ∀ x : ℤ,
      (P.natDegree : ℤ) ^ P.natDegree * P.leadingCoeff ^ (P.natDegree - 1) * P.eval x =
        P_dep.eval ((P.natDegree : ℤ) * P.leadingCoeff * x + P.coeff (P.natDegree - 1))

/-- The $i = 0$ Padé polynomial coefficients $p_{0, v}$ ($0 \le v \le D$) uniquely determined
from `P_coeff` ($P_1, \dots, P_m$) and `fam.clearedCoeff` by canceling Taylor orders
$0 \le v \le D$ (manuscript eq. 7.5). -/
def padeP0Coeff {m r M D : ℕ} (fam : AlgebraicTaylorFamily m r M)
    (P_coeff : Fin m → Fin (D + 1) → ℤ) (v : Fin (D + 1)) : ℤ :=
  - ∑ i : Fin m, ∑ j : Fin (D + 1),
      if j.val ≤ v.val then
        fam.clearedCoeff i.succ (v.val - j.val) * (r : ℤ) ^ (2 * j.val) * P_coeff i j
      else 0

/-- Differential Wronskian data for a non-zero Padé linear form
$L(x) = \sum_{i \in S} P_i(x) f_i(x)$ supported on $S \subseteq \mathrm{Fin}(m+1)$ with $s = |S|$,
packaging Siegel (1949) Ch. 2 Lemma 4 and Bui–Pratt–Zaharescu (2023) Lemmas 5.4, 5.6, 6.3. -/
structure SupportWronskianData (m r D O M : ℕ) (S : Finset (Fin (m + 1))) (H : ℝ) where
  /-- The support-reduced differential Wronskian polynomial $\Delta_S(x) \in \mathbb{Z}[x]$. -/
  Delta : ℤ[X]
  /-- Non-vanishing of $\Delta_S(x)$ from $\mathbb{C}(x)$-linear independence of $\{f_i : i \in S\}$. -/
  Delta_ne_zero : Delta ≠ 0
  /-- Degree bound $\deg(\Delta_S) \le s D + \binom{s}{2} M$. -/
  deg_le : Delta.natDegree ≤ S.card * D + Nat.choose S.card 2 * M
  /-- Order of vanishing at $x = 0$ is $\ge O - (s - 1)$. -/
  ord_zero : ℕ
  ord_zero_ge : O - (S.card - 1) ≤ ord_zero
  ord_zero_le_deg : ord_zero ≤ Delta.natDegree
  /-- Root multiplicity $a(n_0) = \operatorname{ord}_{x = 1/n_0}(\Delta_S)$ for any integer $n_0 > M$. -/
  multAt : ℕ → ℕ
  /-- Divisibility in $\mathbb{Z}[x]$: for any finite set $T$ of distinct integers $n_r > M$,
      $\prod_{n_r \in T} (n_r X - 1)^{a(n_r)} \mid \Delta_S(X)$ in $\mathbb{Z}[X]$ and
      $\sum_{n_r \in T} a(n_r) \le \deg(\Delta_S) - \operatorname{ord}_{x=0}(\Delta_S)$. -/
  sum_mult_le : ∀ T : Finset ℕ, (∀ n ∈ T, M < n) →
    ∑ n ∈ T, multAt n ≤ Delta.natDegree - ord_zero
  prod_linear_dvd : ∀ T : Finset ℕ, (∀ n ∈ T, M < n) →
    (∏ n ∈ T, (Polynomial.C (n : ℤ) * X - 1) ^ multAt n) ∣ Delta
  /-- Leading coefficient bound $|\operatorname{lead}(\Delta_S)| \le C_{\Delta}(s, D, M, H)$. -/
  C_Q : ℝ
  C_Q_ge_one : 1 ≤ C_Q
  lead_bound : |(Delta.leadingCoeff : ℝ)| ≤
    (Nat.factorial S.card : ℝ) * ((D + S.card * M : ℕ) : ℝ) ^ (S.card ^ 2) *
      H ^ S.card * C_Q ^ (Nat.choose S.card 2)

/-- **Siegel (1949), Ch. 2, Lemma 4 & Bui–Pratt–Zaharescu (2023), Lemmas 5.4, 5.6, 6.3
(Canonical Support-Reduced Wronskian)**. -/
axiom canonicalSupportWronskian {d E r D O M B : ℕ}
    (hd : 1 ≤ d) (hE : 1 ≤ E) (hr : 2 ≤ r) (hEr : E ≤ r - 1) (hM : 1 ≤ M)
    (β : Fin d → ℕ)
    (hβ_lo : ∀ i, r ≤ β i) (hβ_hi : ∀ i, β i ≤ M) (hβ_dvd : ∀ i, r ∣ β i)
    (hβ_mono : StrictMono β)
    (P_coeff : Fin (Nat.choose (d + E) d - 1) → Fin (D + 1) → ℤ)
    (S : Finset (Fin ((Nat.choose (d + E) d - 1) + 1)))
    (hD : 1 ≤ D) (hO_gt : D < O)
    (hP_nz : ∃ i j, P_coeff i j ≠ 0)
    (hP_bd : ∀ i j, |P_coeff i j| ≤ (B : ℤ))
    (hP_van : ∀ t : Fin (O - D),
      ∑ i : Fin (Nat.choose (d + E) d - 1), ∑ j : Fin (D + 1),
        (if j.val ≤ D + 1 + t.val then
          (canonicalMonomialTaylorFamily hd hE hr hEr hM β hβ_lo hβ_hi hβ_dvd hβ_mono).clearedCoeff
            i.succ (D + 1 + t.val - j.val) * (r : ℤ) ^ (2 * j.val)
        else 0) * P_coeff i j = 0)
    (hS_zero : (0 : Fin ((Nat.choose (d + E) d - 1) + 1)) ∈ S ↔
      ∃ v : Fin (D + 1), padeP0Coeff
        (canonicalMonomialTaylorFamily hd hE hr hEr hM β hβ_lo hβ_hi hβ_dvd hβ_mono)
        P_coeff v ≠ 0)
    (hS_eq : ∀ i : Fin (Nat.choose (d + E) d - 1),
      i.succ ∈ S ↔ ∃ j : Fin (D + 1), P_coeff i j ≠ 0) :
    SupportWronskianData (Nat.choose (d + E) d - 1) r D O M S (((D + 1) * B + 1 : ℕ) : ℝ)

/-- Evaluated Padé–Wronskian Diophantine approximation data at a cluster base point $n_0$
(Bui–Pratt–Zaharescu 2023, Proposition 3.4 & Lemmas 5.6, 6.3). -/
structure PadeEvaluationData (r E ν s D M a n₀ : ℕ) (x₀ : ℝ) where
  /-- Common denominator $Z = r^{a+s} n_0^{D + (a+s)M}$. -/
  Z : ℕ
  Z_eq : Z = r ^ (a + s) * n₀ ^ (D + (a + s) * M)
  /-- Value of the selected full-rank linear form evaluated at the rational approximations. -/
  nonZeroFormVal : ℝ
  /-- Lower bound from non-vanishing integer linear combination after clearing $Z$:
      $|L_{\text{row}}(q)| \ge 1 / Z$. -/
  form_lower : (1 : ℝ) / (Z : ℝ) ≤ nonZeroFormVal
  /-- Cauchy/Leibniz derivative upper bound and factorial-root approximation bound:
      $1 / Z \le s \cdot x_0^E \cdot u U^D \cdot \rho + x_0^E \cdot w W^{-D}$. -/
  u : ℝ
  U : ℝ
  w : ℝ
  W : ℝ
  ρ : ℝ
  C_P : ℝ
  u_pos : 0 < u
  U_pos : 0 < U
  w_pos : 0 < w
  W_pos : 0 < W
  C_P_pos : 0 < C_P
  rho_le : ρ ≤ C_P * ((2 * n₀ : ℕ) : ℝ) ^ (((M * ν : ℕ) : ℝ) / (r : ℝ)) * x₀ ^ (-(ν : ℝ))
  form_upper : nonZeroFormVal ≤ (s : ℝ) * x₀ ^ E * u * U ^ D * ρ + x₀ ^ E * w * W ^ (-(D : ℝ))

/-- **Bui–Pratt–Zaharescu (2023), Lemmas 5.6 & 6.3 (Cauchy/Leibniz Cleared Padé Evaluation)**. -/
axiom bpz_cauchy_leibniz_pade_eval (r ν d E : ℕ) (ε₀ : ℝ)
    (s_mult : ℕ) (P : ℤ[X])
    (hr : 2 ≤ r) (hν : 2 ≤ ν) (hd : 1 ≤ d) (hE : 1 ≤ E)
    (hE_le : E ≤ min (r - 1) (ν - 1))
    (hε0_pos : 0 < ε₀)
    (hε0_lt : ε₀ < ((Nat.choose (d + E) d - 1 : ℕ) : ℝ) - 1)
    (hs_mult : 1 ≤ s_mult) (hP_deg : P.natDegree = r) (hP_gap : HasDepressedDegreeGap P ν) :
    ∃ (C_1 C_2 C_3 C_0 : ℝ), 1 ≤ C_1 ∧ 1 ≤ C_2 ∧ 1 ≤ C_3 ∧ 1 ≤ C_0 ∧
      ∀ (N M D B : ℕ) (β : Fin d → ℕ)
        (P_coeff : Fin (Nat.choose (d + E) d - 1) → Fin (D + 1) → ℤ)
        (S : Finset (Fin ((Nat.choose (d + E) d - 1) + 1)))
        (n₀ : ℕ)
        (hM : 1 ≤ M) (h8M : 8 * M < N)
        (hD_ge : 10 * (Nat.choose (d + E) d - 1) ≤ D) (hD1 : 1 ≤ D)
        (hO_gt : D < Nat.floor ((((Nat.choose (d + E) d - 1 : ℕ) : ℝ) + 1 - ε₀) * (D : ℝ)))
        (hβ_lo : ∀ i, r ≤ β i) (hβ_hi : ∀ i, β i ≤ M) (hβ_dvd : ∀ i, r ∣ β i)
        (hβ_mono : StrictMono β)
        (hP_nz : ∃ i j, P_coeff i j ≠ 0)
        (hP_bd : ∀ i j, |P_coeff i j| ≤ (B : ℤ))
        (hP_van : ∀ t : Fin (Nat.floor ((((Nat.choose (d + E) d - 1 : ℕ) : ℝ) + 1 - ε₀) * (D : ℝ)) - D),
          ∑ i : Fin (Nat.choose (d + E) d - 1), ∑ j : Fin (D + 1),
            (if j.val ≤ D + 1 + t.val then
              (canonicalMonomialTaylorFamily hd hE hr (le_trans hE_le (min_le_left _ _)) hM
                β hβ_lo hβ_hi hβ_dvd hβ_mono).clearedCoeff
                i.succ (D + 1 + t.val - j.val) * (r : ℤ) ^ (2 * j.val)
            else 0) * P_coeff i j = 0)
        (hS_zero : (0 : Fin ((Nat.choose (d + E) d - 1) + 1)) ∈ S ↔
          ∃ v : Fin (D + 1), padeP0Coeff
            (canonicalMonomialTaylorFamily hd hE hr (le_trans hE_le (min_le_left _ _)) hM
              β hβ_lo hβ_hi hβ_dvd hβ_mono)
            P_coeff v ≠ 0)
        (hS_eq : ∀ i : Fin (Nat.choose (d + E) d - 1),
          i.succ ∈ S ↔ ∃ j : Fin (D + 1), P_coeff i j ≠ 0),
        N ≤ n₀ → n₀ ≤ 2 * N →
        IsPolyFactSol s_mult P n₀ →
        (∀ i, IsPolyFactSol s_mult P (n₀ - β i)) →
        let W := canonicalSupportWronskian hd hE hr (le_trans hE_le (min_le_left _ _)) hM
          β hβ_lo hβ_hi hβ_dvd hβ_mono P_coeff S hD1 hO_gt hP_nz hP_bd hP_van hS_zero hS_eq
        ∃ (x₀ : ℝ) (E_dat : PadeEvaluationData r E ν S.card D M (W.multAt n₀) n₀ x₀),
          1 < x₀ ∧
          |Real.log x₀ - Real.log ((Nat.factorial n₀ : ℕ) : ℝ) / (r : ℝ)| ≤ C_0 ∧
          E_dat.C_P ≤ C_1 ∧
          E_dat.U ≤ (C_1 * (M : ℝ)) ^
            (((((Nat.choose (d + E) d - 1 : ℕ) : ℝ) - ε₀) *
              (((Nat.choose (d + E) d - 1 : ℕ) : ℝ) + 1 - ε₀)) / ε₀) ∧
          (N : ℝ) ^ (((Nat.choose (d + E) d - 1 : ℕ) : ℝ) + 1 - ε₀) *
            (C_2 * (M : ℝ)) ^
              (-((((Nat.choose (d + E) d - 1 : ℕ) : ℝ) *
                (((Nat.choose (d + E) d - 1 : ℕ) : ℝ) + 1 - ε₀)) / ε₀)) ≤ E_dat.W ∧
          E_dat.u ≤ (C_3 * (N : ℝ)) ^ ((W.multAt n₀ + S.card) * M + W.multAt n₀ + S.card) *
            (10 : ℝ) ^ (((Nat.choose (d + E) d - 1 : ℕ) : ℝ) / ε₀ * (M : ℝ)) ∧
          E_dat.w ≤ (((Nat.choose (d + E) d - 1) + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) *
            (C_3 * (N : ℝ)) ^ (2 * ((W.multAt n₀ + S.card) * M + W.multAt n₀ + S.card)) *
            (4 : ℝ) ^ (((Nat.choose (d + E) d - 1 : ℕ) : ℝ) / ε₀ * (M : ℝ))

end GrasGreenbergBrocard
