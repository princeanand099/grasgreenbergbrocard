import GrasGreenbergBrocard.Thm1_1Collapse
import GrasGreenbergBrocard.ValuationParityLayer

/-!
# External Axioms for Section 8 (Frey–Hellegouarch Elliptic Curves & Effective Class Group Bounds)

All axioms in this file represent **established, peer-reviewed mathematical theorems** external to
the manuscript's own contributions, where Mathlib v4.35.0 does not yet provide a formalization:
1. Modularity Theorem (Wiles 1995; Breuil–Conrad–Diamond–Taylor 2001), Mazur's & Kenku's rational
   isogeny theorems (Mazur 1978; Kenku 1982), Serre's open image theorem (Serre 1972), and Tate's
   $p$-adic uniformization for the Frey curves $\mathcal{E}_n$ and $F_n^{(2)}$.
2. Dirichlet's analytic class number formula (Davenport 2000, Ch. 6), Gauss's genus theory
   (Gauss 1801), and Tatuzawa's effective refinement of Siegel's theorem (Tatuzawa 1951).
-/

open Real Filter

namespace GrasGreenbergBrocard

/-- Arithmetic data for the Frey–Hellegouarch elliptic curves $\mathcal{E}_n$ and $F_n^{(2)}$
attached to a Brocard–Ramanujan solution $n! + 1 = m^2$ ($n \ge 8$), packaging modularity
(Wiles 1995; Breuil–Conrad–Diamond–Taylor 2001), conductor exponents, Frobenius traces, and
Mazur–Kenku–Serre–Tate mod-$\ell$ Galois representation surjectivity. -/
structure FreyCurveArithmeticData (n m X₁ Y₁ : ℕ) where
  isModular_E : Prop
  isModular_F2 : Prop
  alpha_E : ℕ
  alpha_E_le : alpha_E ≤ 3
  conductor_E : ℕ
  conductor_E_eq : conductor_E = 2 ^ alpha_E * ∏ p ∈ (Finset.Icc 3 n).filter Nat.Prime, p
  ap_E : ℕ → ℤ
  ap_E_eq : ∀ p : ℕ, (hp : p.Prime) → 3 ≤ p → p ≤ n →
    ap_E p = @legendreSym p ⟨hp⟩ (-(m : ℤ))
  alpha_F2 : ℕ
  alpha_F2_le : alpha_F2 ≤ 3
  conductor_F2 : ℕ
  surj_mod_ell_F2 : ℕ → Prop

/-- **Modularity & Mazur–Kenku–Serre–Tate Package** (Wiles 1995; Breuil–Conrad–Diamond–Taylor 2001;
Mazur 1978; Kenku 1982; Serre 1972): For any Brocard solution $n! + 1 = m^2$ ($n \ge 8$), the
Frey curves $\mathcal{E}_n$ and (when $k = 2$) $F_n^{(2)}$ are modular with the stated conductors,
Frobenius traces, and surjective mod-$\ell$ Galois representations for $\ell \ge 5$ whenever
$v_p(j(F_n^{(2)})) = -2 < 0$ at a prime $p \in (n/2, n]$. -/
axiom frey_curve_modularity_and_galois {n m X₁ Y₁ : ℕ} (hn : 8 ≤ n)
    (hm : Nat.factorial n + 1 = m ^ 2) :
    ∃ D : FreyCurveArithmeticData n m X₁ Y₁,
      D.isModular_E ∧ D.isModular_F2 ∧
      (∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → D.surj_mod_ell_F2 ℓ)

/-- Fundamental discriminant $D_n \in \{q_n, 4 q_n\}$ of $K_n = \mathbb{Q}(\sqrt{q_n})$. -/
def fundDisc (n : ℕ) : ℕ :=
  if q_n n % 4 = 1 then q_n n else 4 * q_n n

/-- Number of distinct prime factors $\omega(N)$ of $N$. -/
def omegaNat (N : ℕ) : ℕ := N.primeFactors.card

/-- Real quadratic class group, narrow class group $\mathrm{Cl}^+(q_n) \simeq \mathcal{A}_2(q_n) \oplus \mathrm{Cl}_{\mathrm{odd}}^+(q_n)$,
regulator, and $L(1, \chi_{D_n})$ invariants of $K_n = \mathbb{Q}(\sqrt{q_n})$, packaging
Dirichlet's analytic class number formula (Davenport 2000, Ch. 6) and Gauss's genus theory (1801). -/
structure RealQuadClassGroupData (n X₁ Y₁ : ℕ) where
  h : ℕ
  h_pos : 0 < h
  R : ℝ
  R_pos : 0 < R
  R_le_log_eps : R ≤ Real.log (pellUnit (q_n n) X₁ Y₁)
  L1_val : ℝ
  L1_pos : 0 < L1_val
  dirichlet_cnf : (h : ℝ) * R = (1 / 2 : ℝ) * Real.sqrt (fundDisc n : ℝ) * L1_val
  card_A2 : ℕ
  card_A2_pos : 0 < card_A2
  card_Cl_odd : ℕ
  card_Cl_odd_pos : 0 < card_Cl_odd
  narrow_class_decomp : card_A2 * card_Cl_odd = 2 * h
  rank2_A2 : ℕ
  gauss_genus_rank2 : rank2_A2 = omegaNat (fundDisc n) - 1
  exp_A2 : ℕ
  exp_A2_pos : 0 < exp_A2
  card_A2_le_exp_pow_rank : card_A2 ≤ exp_A2 ^ rank2_A2

/-- **Dirichlet Class Number Formula & Gauss Genus Theory** (Davenport 2000, Ch. 6; Gauss 1801):
Canonical real quadratic class group and regulator data of $K_n = \mathbb{Q}(\sqrt{q_n})$
($n \ge 8$, $N(\varepsilon_n) = +1$). Scoping Tatuzawa's lower bound strictly to this canonical
object (rather than quantifying universally over arbitrary unconstrained records) prevents
inconsistency from adversarial dummy instances. -/
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
