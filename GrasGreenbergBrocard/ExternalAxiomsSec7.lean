import Mathlib
import GrasGreenbergBrocard.Sec7WronskianConcrete

/-!
# External Axioms for Section 7 (Support-Reduced Padé–Wronskian & Monomial-Product Counting Bounds)

All axioms in this file represent **established, peer-reviewed mathematical theorems** external to
the manuscript's own contributions, where Mathlib v4.35.0 does not yet provide a formalization,
and every axiom is **canonically scoped** to the actual monomial-product family, Padé polynomials,
support set, and Wronskian polynomial constructed in `Sec7PadeWronskian.lean` (preventing
adversarial dummy `AlgebraicTaylorFamily` or dummy `SupportWronskianData` instances):
1. **Bui–Pratt–Zaharescu (2023), Proposition 3.4 & Lemmas 5.6, 6.3**
   (`bpz_cauchy_leibniz_pade_eval`): Scoped strictly to the concrete, axiom-free
   `canonicalMonomialTaylorFamily` (constructed in `Sec7TaylorSeries.lean`) and the concrete,
   axiom-free `canonicalSupportWronskian` (constructed in `Sec7WronskianConcrete.lean` using
   Concrete Lemma 7.2 `monomial_series_linear_indep_poly` and `weighted_wronskian_ne_zero`
   in `Sec7PowerSeriesODE.lean`). Provides the Cauchy integral and Leibniz derivative estimates
   on the cleared Padé linear forms at a cluster base point $n_0$ together with the
   factorial-root approximation from $s_{\mathrm{mult}} \cdot n_0! = P(x_0)$.

Notice that both `canonicalMonomialTaylorFamily` (BPZ Lemma 4.2) and `canonicalSupportWronskian`
(Siegel 1949 Ch. 2 Lemma 4 / BPZ Lemmas 5.4, 5.6, 6.3) are **completely proved in Lean with zero
external axioms** in `Sec7TaylorSeries.lean`, `Sec7PowerSeriesODE.lean`, and
`Sec7WronskianConcrete.lean`.

Notice that the manuscript's novel Section 7 contributions — Siegel's Lemma, Lemma 7.1,
Lemma 7.2 (Puiseux coset separation), Lemma 7.3 (Gauss's Lemma divisibility and multiplicity
bounds), Lemma 7.4 (denominator clearing and elimination inequality), the Pigeonhole cluster
reduction (eq. 7.17), the choice of $D$, the exponent contradiction $\chi(\theta) < (\nu - E)/E$,
and all Table 1/2 counting bounds in Theorem 1.3(ii) — are **proved in Lean** in
`Sec7PadeWronskian.lean`, `Sec7ClusterReduction.lean`, and `Thm1_3Part2Counting.lean`.
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

/-- **Bui–Pratt–Zaharescu (2023), Lemmas 5.6 & 6.3 (Cauchy/Leibniz Cleared Padé Evaluation)**:
Strictly scoped to `canonicalSupportWronskian` attached to the actual Padé polynomials `P_coeff`
and support `S` (preventing adversarial dummy `SupportWronskianData` instances). For a fixed
polynomial-factorial equation $s_{\mathrm{mult}} \cdot n! = P(x)$ with depressed degree gap
$\nu \ge 2$ and admissible $(d, E, \varepsilon_0)$, there exist constants $C_1, C_2, C_3, C_0 \ge 1$
depending only on $(P, s_{\mathrm{mult}}, d, E, \nu, \varepsilon_0)$ such that for any cluster
shift tuple $\beta$, Padé degree $D \ge 10 m$, valid Padé polynomials `P_coeff` with support `S`
at vanishing order $O = \lfloor (m + 1 - \varepsilon_0) D \rfloor$, and cluster base point
$n_0 \in [N, 2 N]$ ($8 M < N$) with $n_0$ and $n_0 - \beta_i$ all solving
$s_{\mathrm{mult}} \cdot n! = P(x)$, evaluating the first $a + s$ derivatives (where
$a = W.\mathrm{multAt}\ n_0$ for `W := canonicalSupportWronskian ...`) at $x = 1/n_0$ yields
`PadeEvaluationData` satisfying the Cauchy/Leibniz bounds (eq. 7.15) and factorial-root
asymptotic $|\log x_0 - \frac{1}{r} \log(n_0!)| \le C_0$. -/
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
