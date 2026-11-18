import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.PellFundamental

/-!
# External Axioms and Core Definitions for Section 5

All external axioms in this file encode established, peer-reviewed mathematical results
external to the manuscript's own contributions, where Mathlib v4.35.0 does not yet
contain a formalization. Zero manuscript-owned lemmas, propositions, or theorems
are axiomatized here.

External sources:
1. O. Perron, *Die Lehre von den Kettenbrüchen*, Band I, 3rd ed., Teubner, 1954, §25
   (Lagrange's midpoint symmetry theorem for regular continued fractions of `√D`).
2. H. Davenport, *Multiplicative Number Theory*, 3rd ed., Springer GTM 74, 2000, Chapter 19
   (Explicit formula for `ψ(x, χ)` and de la Vallée Poussin zero-free region with at most
   one simple real Landau–Siegel zero).
3. C. F. Gauss, *Disquisitiones Arithmeticae*, 1801; L. Rédei, *Arithmetischer Beweis des
   Satzes über die Anzahl der durch vier teilbaren Invarianten der absoluten Klassengruppe
   im quadratischen Zahlkörper*, J. Reine Angew. Math. 171 (1934), 55–60; H. Hasse (1930)
   (Hilbert 90, Hasse norm theorem, Gauss genus theory, and Rédei–Reichardt 4-rank theorem
   for `Cl^+(q_n)`).
-/

noncomputable section

open Real Finset BigOperators

namespace GrasGreenbergBrocard

/-- Square-free core `core(m) = ∏_{2 ∤ v_p(m)} p` of a positive integer `m`. -/
def coreNat (m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => padicValNat p m % 2 = 1), p

/-- Square part `z(m) = ∏_{p ∣ m} p^{⌊v_p(m)/2⌋}` so that `m = coreNat m * (sqPartNat m)^2`. -/
def sqPartNat (m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors, p ^ (padicValNat p m / 2)

/-- Odd part `m* = m / 2^{v_2(m)}` of `m`. -/
def oddPartNat (m : ℕ) : ℕ :=
  m / 2 ^ padicValNat 2 m

/-- Total Legendre character evaluation `χ_d(p) = (d / p)` for `p` prime, `0` otherwise. -/
def chiLegendre (d : ℤ) (p : ℕ) : ℤ :=
  if hp : p.Prime then @legendreSym p ⟨hp⟩ d else 0

/-- **Perron (1954, §25) — Lagrange's Midpoint Symmetry Theorem**:
For any non-square positive integer `D` with fundamental Pell solution `(X₁, Y₁)`
(`IsFundamentalPell D X₁ Y₁`) such that `x^2 - D y^2 = -1` has no integer solution,
the regular continued fraction of `√D` has even period length `L(D)`, and the complete
quotient denominator `Q_M^*` at the half-period `M = L(D)/2` satisfies `0 < Q_M^* < 2√D`,
`Q_M^* ∣ 2D`, and `Q_M^* = 2^a δ` with `a ∈ {-1, 0, 1}` and `δ ∈ {core(X₁ - 1), core(X₁ + 1)}`. -/
structure CFMidpointData (D X₁ Y₁ : ℕ) where
  period : ℕ
  denom : ℕ
  even_period : Even period
  denom_pos : 0 < denom
  denom_lt : (denom : ℝ) < 2 * Real.sqrt (D : ℝ)
  denom_dvd : denom ∣ 2 * D
  denom_core : ∃ δ : ℕ, (δ = coreNat (X₁ - 1) ∨ δ = coreNat (X₁ + 1)) ∧
    (denom = δ ∨ denom = 2 * δ ∨ 2 * denom = δ)

axiom perron_cf_midpoint_symmetry (D X₁ Y₁ : ℕ) (hD_nsq : ¬ IsSquare D)
    (hfund : IsFundamentalPell D X₁ Y₁)
    (hneg : ∀ x y : ℤ, x ^ 2 - (D : ℤ) * y ^ 2 ≠ -1) :
    Nonempty (CFMidpointData D X₁ Y₁)

/-- **Davenport (2000, Chapter 19)** — Explicit formula for `ψ(x, χ)` and de la Vallée
Poussin zero-free region: there exist absolute effective constants `c₀, c₃, C > 0` and
`N₀ ≥ 8` such that for every `n ≥ N₀` and every non-square `d : ℤ` (`d ≠ 0`) with
`4 |d| ≤ exp(2 c₀ √(log n))`, the real character `χ_d(p) = (d / p)` satisfies
`∑_{n/2 < p ≤ n} χ_d(p) log p ≤ C n exp(-c₃ √(log n))`
(since any exceptional Landau–Siegel zero `β₁ ∈ (0, 1)` contributes `-(n^{β₁} - (n/2)^{β₁})/β₁ < 0`). -/
axiom davenport_real_char_half_band_upper :
    ∃ c₀ c₃ C : ℝ, 0 < c₀ ∧ 0 < c₃ ∧ 0 < C ∧ ∃ N₀ : ℕ, 8 ≤ N₀ ∧
      ∀ n : ℕ, N₀ ≤ n → ∀ d : ℤ, d ≠ 0 → ¬ IsSquare d →
        4 * (d.natAbs : ℝ) ≤ Real.exp (2 * c₀ * Real.sqrt (Real.log (n : ℝ))) →
        ∑ p ∈ (Finset.Ioc (n / 2) n).filter (fun p => p.Prime ∧ 3 ≤ p),
          (chiLegendre d p : ℝ) * Real.log (p : ℝ) ≤
            C * (n : ℝ) * Real.exp (-c₃ * Real.sqrt (Real.log (n : ℝ)))

/-- Odd ramified prime set `L₀(n) = Podd(n) \ {2}` (Section 5.2). -/
def L0 (n : ℕ) : Finset ℕ :=
  (Podd n).filter (3 ≤ ·)

/-- Additive Legendre index `ℓ_p(a) ∈ 𝔽₂` defined by `(-1)^{ℓ_p(a)} = (a/p)` for `p ∤ a`. -/
def legendreIdx (p : ℕ) (a : ℤ) : ZMod 2 :=
  if chiLegendre a p = -1 then 1 else 0

/-- Ramified Rédei symbol matrix `R_n^{ram}` over `𝔽₂` acting on `L₀(n) → 𝔽₂` (Section 5.2),
including the `p = 2` congruence constraints when `2 ∣ D_n` (i.e., `q_n % 4 ≠ 1`). -/
def redeiRow (n : ℕ) (p : ℕ) (y : L0 n → ZMod 2) : ZMod 2 :=
  (∑ p' : L0 n,
    if p'.1 = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) * y p'
    else legendreIdx p (p'.1 : ℤ) * y p')

/-- Kernel `ker_{𝔽₂}(R_n^{ram})` of the ramified Rédei symbol matrix over `𝔽₂` (Section 5.2).
When `q_n % 4 ≠ 1` (`2 ∣ D_n`), vectors in the kernel also satisfy `c₂(y) ≡ 1 (mod 8)`,
encoded via the two linear equations `∑ ((p-1)/2) y_p = 0` and `∑ ((p^2-1)/8) y_p = 0` in `𝔽₂`. -/
def redeiKernel (n : ℕ) : Submodule (ZMod 2) (L0 n → ZMod 2) where
  carrier := {y | (∀ p ∈ L0 n, redeiRow n p y = 0) ∧
    (q_n n % 4 ≠ 1 →
      (∑ p : L0 n, (((p.1 - 1) / 2 : ℕ) : ZMod 2) * y p = 0) ∧
      (∑ p : L0 n, (((p.1 ^ 2 - 1) / 8 : ℕ) : ZMod 2) * y p = 0))}
  zero_mem' := by
    refine ⟨fun p _ => ?_, fun _ => ⟨?_, ?_⟩⟩ <;> simp [redeiRow]
  add_mem' {a b} ha hb := by
    refine ⟨fun p hp => ?_, fun hq => ⟨?_, ?_⟩⟩
    · have ha1 := ha.1 p hp
      have hb1 := hb.1 p hp
      simp only [redeiRow, Pi.add_apply, mul_add, Finset.sum_add_distrib] at ha1 hb1 ⊢
      rw [ha1, hb1, add_zero]
    · have ha2 := (ha.2 hq).1
      have hb2 := (hb.2 hq).1
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha2, hb2, add_zero]
    · have ha3 := (ha.2 hq).2
      have hb3 := (hb.2 hq).2
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha3, hb3, add_zero]
  smul_mem' c {a} ha := by
    refine ⟨fun p hp => ?_, fun hq => ⟨?_, ?_⟩⟩
    · have ha1 := ha.1 p hp
      simp only [redeiRow, Pi.smul_apply, smul_eq_mul] at ha1 ⊢
      have h_eq : ∀ p' : L0 n,
          (if p'.1 = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) * (c * a p')
           else legendreIdx p (p'.1 : ℤ) * (c * a p')) =
          c * (if p'.1 = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) * a p'
               else legendreIdx p (p'.1 : ℤ) * a p') := by
        intro p'; split_ifs <;> ring
      simp_rw [h_eq, ← Finset.mul_sum, ha1, mul_zero]
    · have ha2 := (ha.2 hq).1
      simp only [Pi.smul_apply, smul_eq_mul]
      have h_eq : ∀ p : L0 n, (((p.1 - 1) / 2 : ℕ) : ZMod 2) * (c * a p) =
          c * ((((p.1 - 1) / 2 : ℕ) : ZMod 2) * a p) := fun p => by ring
      simp_rw [h_eq, ← Finset.mul_sum, ha2, mul_zero]
    · have ha3 := (ha.2 hq).2
      simp only [Pi.smul_apply, smul_eq_mul]
      have h_eq : ∀ p : L0 n, (((p.1 ^ 2 - 1) / 8 : ℕ) : ZMod 2) * (c * a p) =
          c * ((((p.1 ^ 2 - 1) / 8 : ℕ) : ZMod 2) * a p) := fun p => by ring
      simp_rw [h_eq, ← Finset.mul_sum, ha3, mul_zero]

/-- **Gauss (1801) / Hasse (1930) / Rédei–Reichardt (1934)**:
Exact sequence of `𝔽₂`-vector spaces
`0 → H^1(Gal(K_n/ℚ), O_{K_n}^{×,+}) → ker_{𝔽₂}(R_n^{ram}) → Cl^+(q_n)[2] ∩ 2 Cl^+(q_n) → 0`
for `n ≥ 8`, where `H^1(Gal(K_n/ℚ), O_{K_n}^{×,+}) = {1, η_n} ≃ 𝔽₂` is spanned by the
continued-fraction midpoint vector `y^{mid}(n) ∈ ker_{𝔽₂}(R_n^{ram})`. -/
structure RedeiNarrowClassData (n : ℕ) (yMid : redeiKernel n) where
  Cl4Rank : Type
  [instAdd : AddCommGroup Cl4Rank]
  [instMod : Module (ZMod 2) Cl4Rank]
  [instFin : Module.Finite (ZMod 2) Cl4Rank]
  rank4 : ℕ
  h_rank4 : Module.finrank (ZMod 2) Cl4Rank = rank4
  psiPlus : redeiKernel n →ₗ[ZMod 2] Cl4Rank
  psiPlus_surjective : Function.Surjective psiPlus
  ker_psiPlus_eq_span : LinearMap.ker psiPlus = Submodule.span (ZMod 2) {yMid}

attribute [instance] RedeiNarrowClassData.instAdd RedeiNarrowClassData.instMod RedeiNarrowClassData.instFin

axiom redei_reichardt_exact_sequence (n : ℕ) (hn : 8 ≤ n) (yMid : redeiKernel n)
    (hyMid_ne : yMid ≠ 0) :
    Nonempty (RedeiNarrowClassData n yMid)

end GrasGreenbergBrocard
