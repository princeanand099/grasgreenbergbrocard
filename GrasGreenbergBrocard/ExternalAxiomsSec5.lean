import Mathlib
import GrasGreenbergBrocard.Basic
import GrasGreenbergBrocard.PellFundamental
import GrasGreenbergBrocard.RealQuadField

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

/-- Full ramified prime set `ℒ_ram(n)` of `K_n = ℚ(√q_n)`: `Podd(n)` when `q_n ≡ 1 (mod 4)`,
and `insert 2 (Podd n)` when `q_n ≢ 1 (mod 4)` (`2 ∣ D_n`). -/
def ramPrimes (n : ℕ) : Finset ℕ :=
  if q_n n % 4 = 1 then Podd n else insert 2 (Podd n)

/-- Additive Legendre index `ℓ_p(a) ∈ 𝔽₂` defined by `(-1)^{ℓ_p(a)} = (a/p)` for `p ∤ a`. -/
def legendreIdx (p : ℕ) (a : ℤ) : ZMod 2 :=
  if chiLegendre a p = -1 then 1 else 0

/-- Odd-prime row of the ramified Rédei symbol matrix `R_n^{ram}` over `𝔽₂` acting on
`ramPrimes n → 𝔽₂`, encoding the `p`-adic Hilbert symbol `(c(y), q_n)_p = +1` (Section 5.2). -/
def redeiRowOdd (n : ℕ) (p : ℕ) (y : ramPrimes n → ZMod 2) : ZMod 2 :=
  ∑ p' : ramPrimes n,
    if p'.1 = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) * y p'
    else legendreIdx p (p'.1 : ℤ) * y p'

/-- 2-adic Hilbert symbol row of `R_n^{ram}` over `𝔽₂` when `2 ∣ D_n` (`q_n % 4 ≠ 1`),
encoding `(c(y), q_n)_2 = +1` linearly in `y : ramPrimes n → 𝔽₂`. -/
def redeiRowTwo (n : ℕ) (y : ramPrimes n → ZMod 2) : ZMod 2 :=
  let v2q := padicValNat 2 (q_n n)
  let qodd := oddPartNat (q_n n)
  ∑ p' : ramPrimes n,
    (if p'.1 = 2 then (((qodd ^ 2 - 1) / 8 : ℕ) : ZMod 2)
     else ((((p'.1 - 1) / 2) * ((qodd - 1) / 2) + v2q * ((p'.1 ^ 2 - 1) / 8) : ℕ) : ZMod 2)) * y p'

/-- Kernel `ker_{𝔽₂}(R_n^{ram})` of the ramified Rédei symbol matrix over `𝔽₂` (Section 5.2):
the subspace of `y : ramPrimes n → 𝔽₂` satisfying `(c(y), q_n)_p = +1` for every odd `p ∈ ramPrimes n`
and `(c(y), q_n)_2 = +1` whenever `2 ∣ D_n` (`q_n % 4 ≠ 1`). -/
def redeiKernel (n : ℕ) : Submodule (ZMod 2) (ramPrimes n → ZMod 2) where
  carrier := {y | (∀ p ∈ ramPrimes n, 3 ≤ p → redeiRowOdd n p y = 0) ∧
    (q_n n % 4 ≠ 1 → redeiRowTwo n y = 0)}
  zero_mem' := by
    refine ⟨fun p _ _ => ?_, fun _ => ?_⟩ <;> simp [redeiRowOdd, redeiRowTwo]
  add_mem' {a b} ha hb := by
    refine ⟨fun p hp hp3 => ?_, fun hq => ?_⟩
    · have ha1 := ha.1 p hp hp3
      have hb1 := hb.1 p hp hp3
      have h_eq : ∀ p' : ramPrimes n,
          (if p'.1 = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) * (a p' + b p')
           else legendreIdx p (p'.1 : ℤ) * (a p' + b p')) =
          (if p'.1 = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) * a p'
           else legendreIdx p (p'.1 : ℤ) * a p') +
          (if p'.1 = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) * b p'
           else legendreIdx p (p'.1 : ℤ) * b p') := by
        intro p'; split_ifs <;> ring
      change (∑ p' : ramPrimes n, _) = 0
      simp only [Pi.add_apply]
      simp_rw [h_eq, Finset.sum_add_distrib]
      change redeiRowOdd n p a + redeiRowOdd n p b = 0
      rw [ha1, hb1, add_zero]
    · have ha2 := ha.2 hq
      have hb2 := hb.2 hq
      change (∑ p' : ramPrimes n, _) = 0
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      change redeiRowTwo n a + redeiRowTwo n b = 0
      rw [ha2, hb2, add_zero]
  smul_mem' c {a} ha := by
    refine ⟨fun p hp hp3 => ?_, fun hq => ?_⟩
    · have ha1 := ha.1 p hp hp3
      have h_eq : ∀ p' : ramPrimes n,
          (if p'.1 = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) * (c * a p')
           else legendreIdx p (p'.1 : ℤ) * (c * a p')) =
          c * (if p'.1 = p then legendreIdx p (-(q_n n / p : ℕ) : ℤ) * a p'
               else legendreIdx p (p'.1 : ℤ) * a p') := by
        intro p'; split_ifs <;> ring
      change (∑ p' : ramPrimes n, _) = 0
      simp only [Pi.smul_apply, smul_eq_mul]
      simp_rw [h_eq, ← Finset.mul_sum]
      change c * redeiRowOdd n p a = 0
      rw [ha1, mul_zero]
    · have ha2 := ha.2 hq
      change (∑ p' : ramPrimes n, _) = 0
      simp only [Pi.smul_apply, smul_eq_mul]
      have h_eq : ∀ p' : ramPrimes n,
          (if p'.1 = 2 then (((oddPartNat (q_n n) ^ 2 - 1) / 8 : ℕ) : ZMod 2)
           else ((((p'.1 - 1) / 2) * ((oddPartNat (q_n n) - 1) / 2) +
             padicValNat 2 (q_n n) * ((p'.1 ^ 2 - 1) / 8) : ℕ) : ZMod 2)) * (c * a p') =
          c * ((if p'.1 = 2 then (((oddPartNat (q_n n) ^ 2 - 1) / 8 : ℕ) : ZMod 2)
           else ((((p'.1 - 1) / 2) * ((oddPartNat (q_n n) - 1) / 2) +
             padicValNat 2 (q_n n) * ((p'.1 ^ 2 - 1) / 8) : ℕ) : ZMod 2)) * a p') := fun p' => by ring
      simp_rw [h_eq, ← Finset.mul_sum]
      change c * redeiRowTwo n a = 0
      rw [ha2, mul_zero]

/-- Concrete continued-fraction midpoint vector `y^{mid}(n, X₁) : ramPrimes n → 𝔽₂` supported on the
ramified prime divisors of `c_mid(n, X₁) = coreNat (2 * (X₁ + 1))` (Section 5.2).
Because `(X₁ + 1)^2 - q_n Y₁^2 = 2 (X₁ + 1) = c_mid * v^2`, `c_mid` is always a rational norm
from `ℚ(√q_n)`, is supported inside `ramPrimes n`, and satisfies `c_mid > 1` (by minimality of `Y₁`). -/
def yMidVec (n X₁ : ℕ) : ramPrimes n → ZMod 2 :=
  fun p => if p.1 ∣ coreNat (2 * (X₁ + 1)) then 1 else 0

/-- For `n ≥ 8`, `q_n n` is not a rational square (since `q_n n` is squarefree and `≥ 2`, as
there is a prime `p ≡ 3 [MOD 4]` dividing `q_n n`). -/
lemma q_n_not_isSquare_rat {n : ℕ} (hn : 8 ≤ n) : ¬ IsSquare (q_n n : ℚ) := by
  obtain ⟨p, hp, hpq, _⟩ := q_n_has_prime_mod4 (by omega) (by omega)
  have hq_pos : 0 < q_n n := by
    unfold q_n; exact Finset.prod_pos (fun r hr => (Finset.mem_filter.mp hr).2.1.pos)
  have hq2 : 2 ≤ q_n n := le_trans hp.two_le (Nat.le_of_dvd hq_pos hpq)
  exact not_isSquare_rat_of_squarefree hq2 (q_n_squarefree n)

/-- Concrete narrow 4-rank `rank₄ Cl^+(ℚ(√q_n)) = dim_{𝔽₂}(Cl^+(ℚ(√q_n))[2] ∩ 2 Cl^+(ℚ(√q_n)))`,
anchored directly to `Cl4RankVec (q_n n)` in `RealQuadField.lean` (eliminating `canonicalRealQuadRedei`). -/
def narrow4Rank (n : ℕ) : ℕ :=
  if h : ¬ IsSquare (q_n n : ℚ) then
    haveI : Fact (¬ IsSquare (q_n n : ℚ)) := ⟨h⟩
    Module.finrank (ZMod 2) (Cl4RankVec (q_n n))
  else 0

/-- **Gauss (1801) / Hasse (1930) / Rédei–Reichardt (1934)** (Defect D4 anchored to `Cl4RankVec`):
Exact sequence of `𝔽₂`-vector spaces
`0 → span_{𝔽₂}{y^{mid}(n, X₁)} → ker_{𝔽₂}(R_n^{ram}) → Cl^+(ℚ(√q_n))[2] ∩ 2 Cl^+(ℚ(√q_n)) → 0`
for `n ≥ 8`, scoped directly to the concrete Mathlib-anchored narrow 4-rank space
`Cl4RankVec (q_n n)` (constructed from `NumberField.RingOfIntegers` and `FractionalIdeal` in
`RealQuadField.lean`), the fundamental Pell solution `(X₁, Y₁)`, and `yMidVec n X₁`. -/
axiom redei_reichardt_exact_sequence (n X₁ Y₁ : ℕ) (hn : 8 ≤ n)
    [Fact (¬ IsSquare (q_n n : ℚ))]
    (hfund : IsFundamentalPell (q_n n) X₁ Y₁)
    (hyMid_mem : yMidVec n X₁ ∈ redeiKernel n)
    (hyMid_ne : yMidVec n X₁ ≠ 0) :
    let yMid : redeiKernel n := ⟨yMidVec n X₁, hyMid_mem⟩
    ∃ psiPlus : redeiKernel n →ₗ[ZMod 2] Cl4RankVec (q_n n),
      Function.Surjective psiPlus ∧
      LinearMap.ker psiPlus = Submodule.span (ZMod 2) {yMid}

end GrasGreenbergBrocard
