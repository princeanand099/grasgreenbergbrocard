# External Axioms Register

All external axioms in this repository represent established, peer-reviewed results from analytic number theory, algebraic number theory, Diophantine approximation, and arithmetic geometry. **Zero manuscript-owned theorems, propositions, or lemmas are axiomatized.**

Every `axiom` declaration is strictly isolated inside five `ExternalAxioms*.lean` files (`ExternalAxiomsAnalytic.lean`, `ExternalAxiomsSec3.lean`, `ExternalAxiomsSec5.lean`, `ExternalAxiomsSec7.lean`, `ExternalAxiomsSec8.lean`). Following the two-stage adversarial audit ([PR #7](https://github.com/princeanand099/grasgreenbergbrocard/pull/7), merge SHA `d22839cc`; [PR #8](https://github.com/princeanand099/grasgreenbergbrocard/pull/8), merge SHA `0def862b`), all axioms are tightly scoped with their full mathematical hypotheses and verified via `GrasGreenbergBrocard/AuditAxioms.lean` ([CI Log `56e1d6d4`](https://github.com/princeanand099/grasgreenbergbrocard/commit/56e1d6d4bca09efcde64400ed0b5fb3fe1c5e309)).

## Section 2 Analytic Axioms (`GrasGreenbergBrocard/ExternalAxiomsAnalytic.lean`)

- `de_la_vallee_poussin_theta`: Classical Prime Number Theorem for Chebyshev's $\theta(x) = \sum_{p \le x} \log p$ with de la Vallée Poussin error term $|\theta(x) - x| \le C x \exp(-c\sqrt{\log x})$.
  - *Source*: C.-J. de la Vallée Poussin (1899); H. Davenport, *Multiplicative Number Theory* (3rd ed., 2000), Ch. 18.
  - *Used in*: `ValuationParityLayer.lean`, `ValuationParityThm*.lean`, `ValuationParityMod*.lean`, `Thm1_1Collapse.lean`, `Thm4_2QuarticCores.lean`, `Prop5_1MidpointBias.lean`, `Thm6_4CapacityDiamond.lean`, `Thm8_1FreyCurves.lean`, `Thm8_2TatuzawaClassGroup.lean`.
- `chebyshev_pi_upper`: Chebyshev upper bound $\pi(x) \le C x / \log x$.
  - *Source*: P. L. Chebyshev (1852); G. H. Hardy & E. M. Wright, *An Introduction to the Theory of Numbers*, Theorem 7.
  - *Used in*: `ValuationParityThm*.lean`, `Thm1_1Collapse.lean`, `Thm4_2QuarticCores.lean`, `Thm6_4CapacityDiamond.lean`, `Thm8_2TatuzawaClassGroup.lean`.
- `pnt_pi_asymptotic`: Prime Number Theorem asymptotic $\pi(x) \sim x / \log x$.
  - *Source*: J. Hadamard (1896); C.-J. de la Vallée Poussin (1896).
  - *Used in*: `Thm8_2TatuzawaClassGroup.lean`.
- `mertens_first_theorem`: Mertens's first theorem $\sum_{p \le x} (\log p)/p = \log x + O(1)$.
  - *Source*: F. Mertens, *J. Reine Angew. Math.* 78 (1874), 46–62.
  - *Used in*: `ValuationParityThm*.lean`, `ValuationParityMod*.lean`, `Lem6_3ParityFlipOsc.lean`, `Lem6_3ParityFlip.lean`, `Thm6_4CapacityDiamond.lean`.
- `vaaler_extremal_polynomials`: Vaaler's extremal trigonometric polynomial majorants and minorants for sawtooth and indicator functions with explicit $L^1$ error $1/(H+1)$.
  - *Source*: J. D. Vaaler, *Some extremal functions in Fourier analysis*, Bull. Amer. Math. Soc. 12 (1985), 183–216.
  - *Used in*: `ValuationParityVaaler.lean`, `VaalerMod.lean`, `Lem6_3ParityFlipOsc.lean`.
- `vaughan_van_der_corput_prime_sum` (tightened in PR #8 with `IsPrimeSubinterval P I` and `AntitoneOn w (Set.Icc P (2 * P))`): Vaughan's identity combined with van der Corput's method for exponential sums $\sum_{p \in I} w(p) e(F(p))$ over primes in a genuine contiguous subinterval $I \subseteq [P, 2P]$ with a monotone decreasing weight $w$.
  - *Source*: R. C. Vaughan, *Sommes trigonométriques sur les nombres premiers*, C. R. Acad. Sci. Paris 285 (1977), 981–983; S. W. Graham & G. Kolesnik, *Van der Corput's Method of Exponential Sums* (1991).
  - *Used in*: `ExpSumBounds.lean`, `ExpSumBoundsMod.lean`, `ValuationParityThm*.lean`, `ValuationParityMod*.lean`, `Lem6_3ParityFlipOsc.lean` (exclusively with monotone weight $w(t) = 1/t$).

## Section 3 Axioms (`GrasGreenbergBrocard/ExternalAxiomsSec3.lean`)

- `breusch_bertrand_mod4`: Breusch's refinement of Bertrand's postulate guaranteeing primes in specified residue classes modulo $4$ in dyadic intervals.
  - *Source*: R. Breusch, *Zur Verallgemeinerung des Bertrandschen Postulates*, Math. Z. 34 (1932), 505–526.
  - *Used in*: `Picard2Torsion.lean`, `Thm1_1Collapse.lean`, `Prop4_1SmoothBiquad.lean`, `Thm4_2QuarticCores.lean`, `Prop5_1MidpointBias.lean`, `Thm5_3RedeiCohomology.lean`, `Thm8_1FreyCurves.lean`.
- `rosser_schoenfeld_theta_diff`: Explicit Rosser–Schoenfeld bounds on Chebyshev's $\theta(x) - \theta(y)$.
  - *Source*: J. B. Rosser & L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94.
  - *Used in*: `Thm1_1Collapse.lean`, `Thm5_2EffectiveCores.lean`.
- `stirling_log_factorial_remainder`: Stirling's formula with explicit remainder bound for $\log(n!)$.
  - *Source*: H. Robbins, *A remark on Stirling's formula*, Amer. Math. Monthly 62 (1955), 26–29.
  - *Used in*: `Thm1_1Collapse.lean`.
- `erdos_selfridge_consecutive_product_not_square`: A product of two or more consecutive positive integers is never a perfect square.
  - *Source*: P. Erdős & J. L. Selfridge, *The product of consecutive integers is never a power*, Illinois J. Math. 19 (1975), 292–301.
  - *Used in*: `Thm1_1Collapse.lean`, `Thm8_2TatuzawaClassGroup.lean`.
- `nagura_prime_in_interval`: Existence of a prime in $[x, \frac{6}{5}x]$ for $x \ge 25$.
  - *Source*: J. Nagura, *On the interval containing at least one prime number*, Proc. Japan Acad. 28 (1952), 177–181.
  - *Audit note*: Declared as an auxiliary helper; **not** in the axiom closure of any of the 42 audited theorems in `AuditAxioms.lean`.
- `canonicalRealQuadIwasawa` (scoped in PR #7): Canonical real quadratic Iwasawa invariant record `RealQuadIwasawaInvariants q p` attached to $\mathbb{Q}(\sqrt{q})$ at an odd prime $p$.
- `leopoldt_coates_valuation_law`: Leopoldt–Coates $p$-adic valuation law relating $v_p(L_p(1, \chi))$ to the $p$-adic regulator and class number of $\mathbb{Q}(\sqrt{q})$.
  - *Source*: J. Coates, *p-adic L-functions and Iwasawa's theory*, Algebraic Number Fields (Durham 1975), Academic Press (1977), 269–353.
  - *Used in*: `Thm1_2Iwasawa.lean`.
- `iwasawa_main_conjecture_free_rank`: Iwasawa Main Conjecture / Mazur–Wiles relation for the $\mathbb{Z}_p$-rank and invariants of the cyclotomic $\mathbb{Z}_p$-extension of $\mathbb{Q}(\sqrt{q})$.
  - *Source*: B. Mazur & A. Wiles, *Class fields of abelian extensions of $\mathbb{Q}$*, Invent. Math. 76 (1984), 179–330.
  - *Used in*: `Thm1_2Iwasawa.lean`.
- `ozaki_taya_split_prime_iwasawa`: Ozaki–Taya criterion for Iwasawa invariants of real quadratic fields at split primes $p$.
  - *Source*: M. Ozaki & H. Taya, *On the Iwasawa $\lambda_2$-invariants of certain families of real quadratic fields*, Manuscripta Math. 94 (1997), 437–444; H. Taya (1999).
  - *Used in*: `Thm1_2Iwasawa.lean`.

## Section 4 Axioms (`GrasGreenbergBrocard/ExternalAxiomsSec4.lean`)

- **Zero external axioms.** `ExternalAxiomsSec4.lean` contains only definitions and algebraic infrastructure; all Section 4 theorems depend exclusively on Mathlib and earlier sections (`breusch_bertrand_mod4` and Section 2 analytic axioms).

## Section 5 Axioms (`GrasGreenbergBrocard/ExternalAxiomsSec5.lean`)

- `perron_cf_midpoint_symmetry` (with `CFMidpointData`): Midpoint symmetry of the regular continued fraction expansion of $\sqrt{D}$ for the fundamental Pell solution $(X_1, Y_1)$ of $X^2 - D Y^2 = 1$.
  - *Source*: O. Perron, *Die Lehre von den Kettenbrüchen* (3rd ed.), §25; G. H. Hardy & E. M. Wright, *An Introduction to the Theory of Numbers*, Theorem 10.7.5.
  - *Used in*: `Prop5_1MidpointBias.lean`.
- `davenport_real_char_half_band_upper`: Upper-half real character sum bound $\sum_{n/2 < p \le n} \left(\frac{d}{p}\right)\log p \le C n \exp(-c_3\sqrt{\log n})$.
  - *Source*: H. Davenport, *Multiplicative Number Theory* (3rd ed., 2000), Ch. 19.
  - *Used in*: `Thm5_2EffectiveCores.lean`.
- `redei_reichardt_exact_sequence` (with `RedeiNarrowClassData`, `redeiKernel`): Gauss genus theory and Rédei–Reichardt $4$-rank cohomology exact sequence $0 \to \mathrm{span}_{\mathbb{F}_2}\{y^{\mathrm{mid}}\} \to \ker_{\mathbb{F}_2}(R_n^{\mathrm{ram}}) \to \mathrm{Cl}^+(q_n)[2] \cap 2\mathrm{Cl}^+(q_n) \to 0$.
  - *Source*: L. Rédei & H. Reichardt, *J. Reine Angew. Math.* 170 (1933), 69–74; C. F. Gauss, *Disquisitiones Arithmeticae* (1801).
  - *Used in*: `Thm5_3RedeiCohomology.lean`.

## Section 6 Axioms

- **Zero new external axioms.** All six Section 6 modules (`Prop6_1FourGCD`, `Prop6_2ConsecutiveSquareShift`, `Lem6_3ParityFlipOsc`, `Lem6_3ParityFlip`, `Thm6_4CapacityDiamond`, `Thm6_4PolarizationConcentration`) are proved directly from Mathlib and the tightened Section 2 analytic infrastructure.

## Section 7 Axioms (`GrasGreenbergBrocard/ExternalAxiomsSec7.lean`)

- `bpz_lemma_4_2_taylor_family` (with `AlgebraicTaylorFamily`): Analytic Taylor-series expansion and cleared-coefficient height bound $|r^{2j} c_{i,j}| \le (r^2 C_P M)^j$ for algebraic branches of $s \cdot n! = P(x)$.
  - *Source*: H. M. Bui, K. Pratt & A. Zaharescu, *Power savings for counting solutions to polynomial-factorial equations*, Adv. Math. 422 (2023), Lemma 4.2.
  - *Audit note*: Auxiliary declaration; **not** in the axiom closure of any of the 42 audited theorems in `AuditAxioms.lean`.
- `siegel_bpz_support_wronskian` (hardened in PR #7 with explicit Padé vanishing-order hypothesis `hO`): Non-vanishing of the generalized Padé–Wronskian determinant $\Delta(z) \in \mathbb{Z}[z]$ with degree and coefficient height bounds.
  - *Source*: C. L. Siegel, *Transcendental Numbers* (1949), Ch. 2 Lemma 4; Bui–Pratt–Zaharescu (2023), Lemmas 5.4, 5.6, and 6.3.
  - *Audit note*: Auxiliary declaration; `lem_7_3_support_reduced_wronskian` in `Sec7PadeWronskian.lean` is proved **purely from standard Lean axioms** without invoking this axiom.
- `bpz_dyadic_cluster_elimination` (hardened in PR #7 with `IsPolyFactSol` and `HasDepressedDegreeGap`): Dyadic cluster elimination from the Padé–Wronskian exponent $\theta_{d,E,\nu}(\varepsilon_0)$, bounding solutions in $[M, 2M]$ by $O_\delta(M^{1 - \theta + \delta})$.
  - *Source*: Bui–Pratt–Zaharescu (2023), Prop. 3.4 & §5.
  - *Used in*: `Thm1_3Part2Counting.lean` (together with the internally proved `brocard_poly_depressed_gap`).

## Section 8 Axioms (`GrasGreenbergBrocard/ExternalAxiomsSec8.lean`)

- `frey_curve_modularity_and_galois` (with `FreyCurveArithmeticData`): Modularity of $\mathcal{E}_n$ and $F_n^{(2)}$, conductor formula, Frobenius trace $a_p(\mathcal{E}_n) = \left(\frac{-m}{p}\right)$, and surjectivity of $\bar{\rho}_{F_n^{(2)},\ell} : \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\mathbb{F}_\ell)$ for all primes $\ell \ge 5$.
  - *Source*: A. Wiles (1995); C. Breuil, B. Conrad, F. Diamond & R. Taylor (2001); B. Mazur (1978); M. A. Kenku (1982); J.-P. Serre (1972).
  - *Used in*: `Thm8_1FreyCurves.lean`.
- `canonicalRealQuadClassGroup` (scoped in PR #7, replacing the un-scoped `dirichlet_cnf_and_gauss_genus` record): Canonical `RealQuadClassGroupData` for $\mathbb{Q}(\sqrt{q_n})$ encoding Dirichlet's analytic class number formula $h(q_n) R(q_n) = \frac{1}{2}\sqrt{D_n} L(1, \chi_{D_n})$ and Gauss genus theory $\mathrm{rank}_2(\mathcal{A}_2(q_n)) = \omega(D_n) - 1$.
  - *Source*: H. Davenport, *Multiplicative Number Theory* (3rd ed., 2000), Ch. 6; C. F. Gauss, *Disquisitiones Arithmeticae* (1801).
  - *Used in*: `Thm8_2TatuzawaClassGroup.lean`.
- `tatuzawa_effective_siegel` (scoped in PR #7 to `canonicalRealQuadClassGroup`): Effective lower bound $L(1, \chi_D) > 0.655\,\varepsilon\,D^{-\varepsilon}$ for all fundamental discriminants $D > 0$ with at most one exception $D_*$.
  - *Source*: T. Tatuzawa, *On a theorem of Siegel*, Japan. J. Math. 21 (1951), 163–178.
  - *Used in*: `Thm8_2TatuzawaClassGroup.lean`.
