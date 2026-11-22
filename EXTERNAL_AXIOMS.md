# External Axioms Inventory

All **28 custom axioms** in `GrasGreenbergBrocard` are isolated in **six** dedicated files and audited across **92 public declarations** in `GrasGreenbergBrocard/AuditAxioms.lean` (zero `sorryAx`, zero `Lean.ofReduceBool`/`Lean.trustCompiler`).

## Eliminated Axioms (De-Axiomatized into Mathlib Proofs)

The following previously axiomatized statements have been **completely eliminated** and proved unconditionally from Mathlib `v4.35.0`:
- `padic_log_regulator_pell_power` (`ExternalAxiomsSec3.lean`): **eliminated**; manuscript eq. (3.6) is now proved directly in $\mathbb{Q}_p$ in `PadicRegulator.lean` (`realQuadPadicRegVal_pell_power`).
- `canonicalRealQuadRedei` (`ExternalAxiomsSec5.lean`): **eliminated**; `narrow4Rank` is now defined directly on Mathlib's narrow class group `Cl4RankVec` in `RealQuadField.lean`.
- `canonicalMonomialTaylorFamily` (`ExternalAxiomsSec7.lean`): **eliminated**; now a concrete `def` over `PowerSeries ℤ` in `Sec7TaylorSeries.lean`.
- `canonicalSupportWronskian` (`ExternalAxiomsSec7.lean`): **eliminated**; now a concrete `def` over `ℤ[X]` in `Sec7WronskianConcrete.lean`, proved from Concrete Lemma 7.2 (`monomial_series_linear_indep_poly`), Wronskian non-vanishing (`weighted_wronskian_ne_zero`), `Matrix.adjugate_mul`, and Gauss's Lemma in `Sec7PowerSeriesODE.lean` and `Sec7WronskianConcrete.lean`.
- Section 8 Frobenius trace axioms (`a_p` of $\mathcal{E}_n$ and $F_n^{(2)}$): **eliminated**; now proved directly over `ZMod p` in `Thm8_1FreyCurves.lean` (`frobeniusTrace_freyCurveE`, `freyE_p2_minimal_scaling`, `frobeniusTrace_freyCurveE2`).

## 1. `GrasGreenbergBrocard/ExternalAxiomsAnalytic.lean` (6 axioms)

| Axiom | Published Source | Role & Soundness Conditions |
| :--- | :--- | :--- |
| `de_la_vallee_poussin_theta` | de la Vallée Poussin (1899) | Classical zero-free region error term for $\vartheta(x) = x + O(x \exp(-c\sqrt{\log x}))$ |
| `chebyshev_pi_upper` | Chebyshev (1852) | Effective upper bound $\pi(x) \le C x / \log x$ |
| `pnt_pi_asymptotic` | Hadamard / de la Vallée Poussin (1896) | Prime Number Theorem $\pi(x) \sim x / \log x$ |
| `mertens_first_theorem` | Mertens (1874) | $\sum_{3 \le p \le x} \frac{\log p}{p - 1} = \log x + O(1)$ |
| `vaaler_extremal_polynomials` | Vaaler (1985), Thm. 18 | Extremal trigonometric polynomial majorants/minorants for sawtooth functions |
| `vaughan_van_der_corput_prime_sum` | Iwaniec & Kowalski (2004), Prop. 13.4, Cor. 8.11/8.13, Thm. 8.25 | Type I/II prime exponential sum bound with `T₀ ≤ (n : ℝ) ^ 2` enforced |

## 2. `GrasGreenbergBrocard/ExternalAxiomsSec3.lean` (9 axioms)

| Axiom | Published Source | Role & Soundness Conditions |
| :--- | :--- | :--- |
| `breusch_bertrand_mod4` | Breusch (1932), *Math. Z.* 34, 505–526 | Existence of prime $p \equiv 3 \pmod 4$ in $(x, 2x]$ for $x \ge 7$ |
| `rosser_schoenfeld_theta_diff` | Rosser–Schoenfeld (1962), Thm. 10 | Explicit $\vartheta(n) - \vartheta(n/2) > 0.4 n$ for $n \ge 116$ |
| `stirling_log_factorial_remainder` | Classical Euler–Maclaurin / Stirling | $\log(n!) = n \log n - n + \frac{1}{2}\log(2\pi n) + O(n^{-1})$ |
| `erdos_selfridge_consecutive_product_not_square` | Erdős–Selfridge (1975), *Illinois J. Math.* 19 | Product of $\ge 2$ consecutive positive integers is never a square |
| `nagura_prime_in_interval` | Nagura (1952), *Proc. Japan Acad.* 28 | Prime in $(x, \frac{6}{5}x)$ for $x \ge 25$ |
| `canonicalRealQuadIwasawa` | Standard Iwasawa invariants of $\mathbb{Q}(\sqrt{q})$ | Anchored to Mathlib `realQuadClassNumber q`, `realQuadPadicRegVal q p`, and `realQuadSplits q p` (`RealQuadField.lean`, `PadicRegulator.lean`); only the unformalized Iwasawa module invariants ($T_{K,p}$, $\lambda_p^*$, $\lambda_p$, $\mu_p$, $L_p(1,\chi_D)$) remain external |
| `leopoldt_coates_valuation_law` | Leopoldt / Washington (1997), Thm. 5.24; Coates (1977), App. Lemma 8 | Requires `Squarefree q`; links `realQuadClassNumber q` and `realQuadPadicRegVal q p` to $L_p(1, \chi_D)$ and $\#T_{K,p}$ |
| `iwasawa_main_conjecture_free_rank` | Ferrero–Washington (1979), Mazur–Wiles (1984), Greenberg (1978, Prop. 3) | $\mu_p(\chi_D) = 0$, freeness of $X_p(K_\infty)$, and $\lambda_p^*(K) = \lambda_p(\chi_D) \ge 1$ when $T_{K,p} \ne 0$ |
| `ozaki_taya_split_prime_iwasawa` | Ozaki (1997, Prop. 1), Taya (1996, Cor. 2–3, Thm. 4), Yanagisawa (2026) | Split-prime unramified Iwasawa module co-invariants and Taya's $\lambda_p(K) \ge 1$ criterion |

## 3. `GrasGreenbergBrocard/ExternalAxiomsSec4.lean` (1 axiom)

| Axiom | Published Source | Role |
| :--- | :--- | :--- |
| `mertens_first_theorem_odd_primes` | Mertens (1874) | $\sum_{3 \le p \le x} \frac{\log p}{p - 1} = \log x - \gamma - \log 2 + o(1)$ |

## 4. `GrasGreenbergBrocard/ExternalAxiomsSec5.lean` (3 axioms)

| Axiom | Published Source | Role & Soundness Conditions |
| :--- | :--- | :--- |
| `perron_cf_midpoint_symmetry` | Perron (1954), §25 | Continued-fraction midpoint symmetry for fundamental Pell unit $X_1 + Y_1\sqrt{q}$ |
| `davenport_real_char_half_band_upper` | Davenport (2000), Chapter 19 | Explicit formula for $\psi(x, \chi)$ and de la Vallée Poussin zero-free region on half-bands |
| `redei_reichardt_exact_sequence` | Gauss (1801); Hasse (1930); Rédei (1934) | Anchored directly to Mathlib `Cl4RankVec` (`narrow4Rank n`), the repaired `ramPrimes n` (including $p = 2$ when $2 \mid D_n$), exact 2-adic Hilbert row `redeiRowTwo`, and the Lean-proved `yMidVec_mem_redeiKernel` and `yMidVec_ne_zero` |

## 5. `GrasGreenbergBrocard/ExternalAxiomsSec7.lean` (1 axiom)

Only **one** external axiom remains in Section 7. The algebraic Taylor family (`canonicalMonomialTaylorFamily`), the rational power-series ODEs, Concrete Lemma 7.2 (`monomial_series_linear_indep_poly`), Wronskian non-vanishing (`weighted_wronskian_ne_zero`), the concrete support-reduced Wronskian (`canonicalSupportWronskian`), Siegel's Lemma, Lemma 7.1, eq. (7.1) depression, eq. (7.17) cluster reduction, and the exponent elimination algebra (`dyadic_cluster_elimination_proved`) are all **proved from Mathlib with 0 external axioms**.

| Axiom | Published Source | Role |
| :--- | :--- | :--- |
| `bpz_cauchy_leibniz_pade_eval` | Bui–Pratt–Zaharescu (2023), Prop. 3.4 & Lemmas 5.6, 6.3 | Scoped to the concrete `def canonicalMonomialTaylorFamily` and concrete `def canonicalSupportWronskian` with `hS_zero` and `hS_eq`; yields `PadeEvaluationData` with `rho_le : ρ ≤ C_P * (2 * n₀)^(M * ν / r) * x₀^(-ν)` |

## 6. `GrasGreenbergBrocard/ExternalAxiomsSec8.lean` (8 axioms)

Section 8's bundled record axioms have been decomposed into 3 explicit elliptic-curve predicates, 3 named published theorems, the class-group record (anchored to Mathlib `NumberField.classNumber` and `NarrowClassGroup`), and Tatuzawa's theorem. All Frobenius traces and $p=2$ minimality identities are proved directly in Mathlib.

| Axiom | Published Source | Role & Soundness Conditions |
| :--- | :--- | :--- |
| `IsModular` | Elliptic curve modularity predicate on `WeierstrassCurve ℤ` | Predicate asserting modularity of a rational elliptic curve |
| `conductor` | Elliptic curve conductor on `WeierstrassCurve ℤ` | Arithmetic conductor $N(E) \in \mathbb{N}$ |
| `HasSurjectiveModLGalRep` | Mod-$\ell$ Galois representation surjectivity on `WeierstrassCurve ℤ` | Predicate asserting surjectivity of $\bar{\rho}_{E, \ell}$ |
| `bcdt_modularity_theorem` | Wiles (1995); Breuil–Conrad–Diamond–Taylor (2001) | Every nonsingular `WeierstrassCurve ℤ` is modular |
| `tate_algorithm_semistable_conductor` | Tate (1975); Silverman (1994), Ch. IV | Exact conductor formula for semistable Frey curves |
| `mazur_kenku_serre_surjectivity` | Mazur (1978); Kenku (1982); Serre (1972) | Surjectivity of $\bar{\rho}_{E, \ell}$ for $\ell \ge 5$ on semistable curves with full 2-torsion |
| `canonicalRealQuadClassGroup` | Davenport (2000), Ch. 6; Gauss (1801) | Anchored directly to Mathlib `realQuadClassNumber`, `narrowTwoSylow`, and `narrowOddPart` (`RealQuadField.lean`); only the analytic Dirichlet class number formula linking $h \cdot R$ to $L(1, \chi_D)$ remains external |
| `tatuzawa_effective_siegel` | Tatuzawa (1951), *Japan. J. Math.* 21, 163–178 | Effective Siegel lower bound $L(1, \chi_D) > \frac{0.655 \varepsilon}{D^\varepsilon}$ with at most one exceptional discriminant |
