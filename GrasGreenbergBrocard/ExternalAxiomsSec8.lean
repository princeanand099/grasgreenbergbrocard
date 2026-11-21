import GrasGreenbergBrocard.Thm1_1Collapse
import GrasGreenbergBrocard.ValuationParityLayer
import GrasGreenbergBrocard.RealQuadField

/-!
# External Axioms for Section 8 (Frey–Hellegouarch Elliptic Curves & Effective Class Group Bounds)

All axioms in this file represent **established, peer-reviewed mathematical theorems** external to
the manuscript's own contributions, where Mathlib v4.35.0 does not yet provide a formalization:
1. **Curve-level elliptic-curve interfaces (Defect D3(3) resolved)**:
   - `IsModular (E : WeierstrassCurve ℤ) : Prop` — modularity of $E/\mathbb{Q}$ (Wiles 1995;
     Breuil–Conrad–Diamond–Taylor 2001).
   - `conductor (E : WeierstrassCurve ℤ) : ℕ` — arithmetic conductor $N(E)$ (Tate's algorithm).
   - `HasSurjectiveModLGalRep (E : WeierstrassCurve ℤ) (ℓ : ℕ) : Prop` — surjectivity of
     $\bar{\rho}_{E, \ell} : \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\mathbb{F}_\ell)$
     (Mazur 1978; Kenku 1982; Serre 1972; Tate's $p$-adic uniformization).
   - Note that `frobeniusTrace (freyCurveE m) p = legendreSym p (-m)`, the $p = 2$ minimality
     scaling `freyE_p2_minimal_scaling`, and `freyCurveE2` are all **proved directly in Lean with
     zero axioms** in `Thm8_1FreyCurves.lean`.
2. **Real quadratic class group & Tatuzawa's theorem (Defect D6(b) resolved)**:
   - `RealQuadClassGroupData` is anchored directly to Mathlib's `realQuadClassNumber (q_n n)`
     (`NumberField.classNumber (RealQuadK (q_n n))`) and the concrete narrow class group subgroups
     `narrowTwoSylow (q_n n)` and `narrowOddPart (q_n n)` defined in `RealQuadField.lean`.
   - Dirichlet's analytic class number formula (Davenport 2000, Ch. 6), Gauss's genus theory
     (Gauss 1801), and Tatuzawa's effective refinement of Siegel's theorem (Tatuzawa 1951).
-/

open Real Filter

namespace GrasGreenbergBrocard

/-- Concrete Mathlib `WeierstrassCurve ℤ` model of the Frey curve
$\mathcal{E}_n : Y^2 = X^3 + 2m X^2 + X$. -/
def freyCurveE (m : ℕ) : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := 2 * (m : ℤ)
  a₃ := 0
  a₄ := 1
  a₆ := 0

/-- Concrete Mathlib `WeierstrassCurve ℤ` model of the Level-2 Frey curve
$F_n^{(2)} : Y^2 = V^3 - 2 X_1 V^2 - 4 V + 8 X_1$. -/
def freyCurveF2 (X₁ : ℕ) : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := -2 * (X₁ : ℤ)
  a₃ := 0
  a₄ := -4
  a₆ := 8 * (X₁ : ℤ)

/-! ### Curve-Level External Elliptic-Curve Predicates & Classical Literature Axioms (Defect D3(3)) -/

/-- Modularity of an integral Weierstrass model $E/\mathbb{Q}$ (existence of a weight-2 newform
of level $N(E)$ with matching $L$-function). -/
axiom IsModular (E : WeierstrassCurve ℤ) : Prop

/-- Arithmetic conductor $N(E) \in \mathbb{N}$ of an integral Weierstrass model $E/\mathbb{Q}$. -/
axiom conductor (E : WeierstrassCurve ℤ) : ℕ

/-- Surjectivity of the mod-$\ell$ Galois representation
$\bar{\rho}_{E, \ell} : \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\mathbb{F}_\ell)$. -/
axiom HasSurjectiveModLGalRep (E : WeierstrassCurve ℤ) (ℓ : ℕ) : Prop

/-- **Modularity Theorem (Wiles 1995; Taylor–Wiles 1995; Breuil–Conrad–Diamond–Taylor 2001)**:
Every nonsingular elliptic curve $E/\mathbb{Q}$ (`E.Δ ≠ 0`) is modular. -/
axiom bcdt_modularity_theorem (E : WeierstrassCurve ℤ) (hΔ : E.Δ ≠ 0) : IsModular E

/-- **Tate's Algorithm & Ogg–Saito Conductor Formula (Tate 1975; Silverman, Adv. Topics Ch. IV)**:
For any nonsingular integral Weierstrass model $E/\mathbb{Q}$ whose odd bad primes $S_{\mathrm{odd}}$
all have multiplicative reduction (`p ∣ E.Δ ∧ ¬ p ∣ E.c₄`) and all other odd primes have good
reduction (`¬ p ∣ E.Δ`), the conductor satisfies
$N(E) = 2^\alpha \prod_{p \in S_{\mathrm{odd}}} p$ with $\alpha \le 8$. -/
axiom tate_algorithm_semistable_conductor (E : WeierstrassCurve ℤ) (hΔ : E.Δ ≠ 0)
    (S_odd : Finset ℕ)
    (hS_pr : ∀ p ∈ S_odd, p.Prime ∧ 3 ≤ p)
    (hS_mult : ∀ p ∈ S_odd, (p : ℤ) ∣ E.Δ ∧ ¬ (p : ℤ) ∣ E.c₄)
    (hS_good : ∀ p : ℕ, p.Prime → 3 ≤ p → p ∉ S_odd → ¬ (p : ℤ) ∣ E.Δ) :
    ∃ α : ℕ, α ≤ 8 ∧ conductor E = 2 ^ α * ∏ p ∈ S_odd, p

/-- **Mazur (1978), Kenku (1982), Serre (1972), & Tate $p$-Adic Uniformization**:
Let $E/\mathbb{Q}$ be a nonsingular integral Weierstrass model ($a_1 = a_3 = 0$) with full rational
2-torsion ($X^3 + a_2 X^2 + a_4 X + a_6$ splits into three distinct linear factors over $\mathbb{Z}$)
and multiplicative reduction at a prime $p \ge 5$ with $v_p(\Delta(E)) = 2$ and $p \nmid c_4(E)$
(hence $v_p(j(E)) = -2 < 0$, so $\ell \nmid v_p(j(E))$ for all primes $\ell \ge 5$).
Then $\bar{\rho}_{E, \ell}$ is surjective onto $\mathrm{GL}_2(\mathbb{F}_\ell)$ for every prime
$\ell \ge 5$. -/
axiom mazur_kenku_serre_surjectivity (E : WeierstrassCurve ℤ)
    (hΔ : E.Δ ≠ 0) (ha1 : E.a₁ = 0) (ha3 : E.a₃ = 0)
    (h2tors : ∃ r₁ r₂ r₃ : ℤ, r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₂ ≠ r₃ ∧
      ∀ x : ℤ, x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ = (x - r₁) * (x - r₂) * (x - r₃))
    (hmult : ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧
      padicValNat p E.Δ.natAbs = 2 ∧ ¬ (p : ℤ) ∣ E.c₄) :
    ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → HasSurjectiveModLGalRep E ℓ

/-! ### Anchored Real Quadratic Class Group Data & Tatuzawa's Theorem (Defect D6(b)) -/

/-- Fundamental discriminant $D_n \in \{q_n, 4 q_n\}$ of $K_n = \mathbb{Q}(\sqrt{q_n})$. -/
def fundDisc (n : ℕ) : ℕ :=
  if q_n n % 4 = 1 then q_n n else 4 * q_n n

/-- Number of distinct prime factors $\omega(N)$ of $N$. -/
def omegaNat (N : ℕ) : ℕ := N.primeFactors.card

/-- Real quadratic class group, narrow class group $\mathrm{Cl}^+(q_n) \simeq \mathcal{A}_2(q_n) \oplus \mathrm{Cl}_{\mathrm{odd}}^+(q_n)$,
regulator, and $L(1, \chi_{D_n})$ invariants of $K_n = \mathbb{Q}(\sqrt{q_n})$, anchored directly
to Mathlib's `realQuadClassNumber (q_n n)` (`NumberField.classNumber (RealQuadK (q_n n))`) and the
concrete subgroups `narrowTwoSylow (q_n n)` and `narrowOddPart (q_n n)` from `RealQuadField.lean`. -/
structure RealQuadClassGroupData (n X₁ Y₁ : ℕ) where
  h : ℕ
  h_eq : h = realQuadClassNumber (q_n n)
  h_pos : 0 < h
  R : ℝ
  R_pos : 0 < R
  R_le_log_eps : R ≤ Real.log (pellUnit (q_n n) X₁ Y₁)
  L1_val : ℝ
  L1_pos : 0 < L1_val
  dirichlet_cnf : (h : ℝ) * R = (1 / 2 : ℝ) * Real.sqrt (fundDisc n : ℝ) * L1_val
  card_A2 : ℕ
  card_A2_eq : ∀ [Fact (¬ IsSquare (q_n n : ℚ))], card_A2 = Nat.card (narrowTwoSylow (q_n n))
  card_A2_pos : 0 < card_A2
  card_Cl_odd : ℕ
  card_Cl_odd_eq : ∀ [Fact (¬ IsSquare (q_n n : ℚ))], card_Cl_odd = Nat.card (narrowOddPart (q_n n))
  card_Cl_odd_pos : 0 < card_Cl_odd
  narrow_class_decomp : card_A2 * card_Cl_odd = 2 * h
  rank2_A2 : ℕ
  gauss_genus_rank2 : rank2_A2 = omegaNat (fundDisc n) - 1
  exp_A2 : ℕ
  exp_A2_pos : 0 < exp_A2
  card_A2_le_exp_pow_rank : card_A2 ≤ exp_A2 ^ rank2_A2

/-- **Dirichlet Class Number Formula & Gauss Genus Theory** (Davenport 2000, Ch. 6; Gauss 1801):
Canonical real quadratic class group and regulator data of $K_n = \mathbb{Q}(\sqrt{q_n})$
($n \ge 8$, $N(\varepsilon_n) = +1$), anchored to `realQuadClassNumber (q_n n)` and
`NarrowClassGroup (q_n n)`. -/
axiom canonicalRealQuadClassGroup {n X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁) :
    RealQuadClassGroupData n X₁ Y₁

/-- **Tatuzawa's Effective Refinement of Siegel's Theorem** (T. Tatuzawa, *Japan. J. Math.* 21
(1951), 163–178): For any $\varepsilon \in (0, 1/8)$, there exists at most one exceptional
fundamental discriminant $D_* \in \mathbb{N}$ such that for every $n \ge 8$ with
`fundDisc n ≠ D_*`, the canonical $L$-value of $K_n = \mathbb{Q}(\sqrt{q_n})$ satisfies
$L(1, \chi_{D_n}) > 0.655\,\varepsilon\,D_n^{-\varepsilon}$. -/
axiom tatuzawa_effective_siegel (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 8) :
    ∃ D_star : ℕ, ∀ (n X₁ Y₁ : ℕ) (hn : 8 ≤ n) (hfund : IsFundamentalPell (q_n n) X₁ Y₁),
      fundDisc n ≠ D_star →
      (0.655 : ℝ) * ε * (fundDisc n : ℝ) ^ (-ε) <
        (canonicalRealQuadClassGroup hn hfund).L1_val

end GrasGreenbergBrocard
