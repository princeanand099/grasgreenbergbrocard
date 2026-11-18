# External Axiom Register

All external axioms in this repository represent established, peer-reviewed mathematical results external to the manuscript's own contributions, where Mathlib v4.35.0 does not yet provide a formalization. **Zero** manuscript-owned lemmas, propositions, corollaries, or theorems are axiomatized.

## Section 2 Axioms (`GrasGreenbergBrocard/ExternalAxiomsAnalytic.lean`)
- **van der Corput $k$-th Derivative Exponential Sum Bound**: Classical van der Corput / exponent-pair bound for $\sum_{a < p \le b} e(f(p))$ on smooth phases (Montgomery–Vaughan / Graham–Kolesnik). Used in `ExpSumBounds.lean` and `ExpSumBoundsMod.lean`.
- **Mertens's Second Theorem / Harmonic Prime Sum**: Asymptotic $\sum_{p \le x} \frac{\log p}{p - 1} = \log x + O(1)$ (Mertens 1874). Used in `ValuationParityDigits.lean` and `ValuationParityThm.lean`.
- **Vaaler's Trigonometric Polynomial Approximation**: Optimal $L^1$ majorant/minorant trigonometric polynomials for the sawtooth function $\psi(x)$ supported on odd harmonics (Vaaler 1985, *Bull. AMS* 12, Theorem 18). Used in `ValuationParityVaaler.lean` and `VaalerMod.lean`.

## Section 3 Axioms (`GrasGreenbergBrocard/ExternalAxiomsSec3.lean`)
- `breusch_bertrand_mod4`: For $x \ge 7$, $\exists p$ prime with $x < p \le 2x$ and $p \equiv 3 \pmod 4$. Source: R. Breusch, *Math. Z.* 34 (1932), 505–526. Used in `PellFundamental.lean`.
- `rosser_schoenfeld_theta_diff`: $\vartheta(n) - \vartheta(n/2) > 0.4 n$ for all $n \ge 116$. Source: J. B. Rosser & L. Schoenfeld, *Illinois J. Math.* 6 (1962), Theorem 10. Used in `PellFundamental.lean`.
- `stirling_log_factorial_remainder`: $\log(n!) = n\log n - n + \frac{1}{2}\log(2\pi n) + O(n^{-1})$. Source: Classical Euler–Maclaurin / Stirling expansion. Used in `Thm1_1Collapse.lean`.
- `erdos_selfridge_consecutive_product_not_square`: Product of $\ge 2$ consecutive positive integers is never a square. Source: P. Erdős & J. L. Selfridge, *Illinois J. Math.* 19 (1975), 292–301. Used in `Thm1_1Collapse.lean`.
- `nagura_prime_in_interval`: For $x \ge 25$, $\exists p$ prime with $x < p < \frac{6}{5}x$. Source: J. Nagura, *Proc. Japan Acad.* 28 (1952), 177–181. Used in `Thm1_2Iwasawa.lean`.
- **Leopoldt / Coates / Taya / Iwasawa-Theoretic Package** (`RealQuadIwasawaInvariants` axioms): Leopoldt's $p$-adic class number formula (Washington 1997, Theorem 5.24), Coates's $p$-ramification torsion formula (Coates 1977, Appendix Lemma 8; Taya 1996, Prop. 1), and Iwasawa $\lambda_p^* / \lambda_p$ rank-order identities (Fukuda–Komatsu 1986; Taya 1996). Used in `Thm1_2Iwasawa.lean`.

## Section 4 Axioms (`GrasGreenbergBrocard/ExternalAxiomsSec4.lean`)
- **Chebyshev's Prime Number Theorem** ($\vartheta(x) \sim x$): Classical Prime Number Theorem (Hadamard / de la Vallée Poussin 1896). Used in `Thm4_2QuarticCores.lean`.
- `mertens_first_theorem_odd_primes`: Mertens's first theorem on odd primes with Euler–Mascheroni constant $\gamma \in (0.5772, 0.5773)$ (Mertens 1874; Rosser–Schoenfeld 1962). Used in `Thm4_2QuarticCores.lean` (`thm_4_2_part3_mertens_bound`).
