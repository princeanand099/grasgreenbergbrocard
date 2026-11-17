# External Axioms Inventory

All external axioms in this repository represent **established, peer-reviewed mathematical theorems** external to the manuscript's own contributions, where Mathlib v4.35.0 does not yet provide a formalization. **Zero** manuscript-owned lemmas, propositions, or theorems are axiomatized.

## Section 2 External Axioms (`GrasGreenbergBrocard/ExternalAxiomsAnalytic.lean`)

1. **`de_la_vallee_poussin_theta`**
   - **Statement**: $\vartheta(x) - x = O\bigl(x \exp(-c_1\sqrt{\log x})\bigr)$ for some absolute constant $c_1 > 0$.
   - **Source**: Ch.-J. de la Vallée Poussin (1899); H. Davenport, *Multiplicative Number Theory* (3rd ed., 2000), Ch. 18.

2. **Prime Exponential Sum Bounds (Vinogradov–Korobov / Vaughan Type)**
   - **Statement**: Bounds on $\sum_{p \sim P} e(\alpha n / p)$ and related prime exponential sums over dyadic intervals used in `ExpSumBounds.lean` and `ExpSumBoundsMod.lean`.
   - **Source**: I. M. Vinogradov / R. C. Vaughan identity and Weyl-type exponential sum estimates (Davenport 2000, Ch. 24–25; Iwaniec–Kowalski 2004, Ch. 8 & 13).

3. **Vaaler Trigonometric Polynomial Approximation**
   - **Statement**: Beurling–Selberg / Vaaler extremal trigonometric polynomial bounds for the sawtooth function $\psi(t) = \{t\} - 1/2$ and modular indicator functions.
   - **Source**: J. D. Vaaler, *Some extremal functions in Fourier analysis*, Bull. Amer. Math. Soc. (N.S.) 12 (1985), 183–216.

## Section 3 External Axioms (`GrasGreenbergBrocard/ExternalAxiomsSec3.lean`)

1. **`breusch_bertrand_mod4`**
   - **Statement**: For every real $x \ge 7$, there exists a prime $p$ with $x < p \le 2x$ and $p \equiv 3 \pmod 4$.
   - **Source**: R. Breusch, *Zur Verallgemeinerung des Bertrandschen Postulates, dass zwischen $x$ und $2x$ stets Primzahlen liegen*, Math. Z. 34 (1932), 505–526.

2. **`rosser_schoenfeld_theta_diff`**
   - **Statement**: For all $n \ge 116$, $\vartheta(n) - \vartheta(n/2) > 0.4\,n$.
   - **Source**: J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), Theorem 10.

3. **`stirling_log_factorial_remainder`**
   - **Statement**: $\log(n!) = n\log n - n + \frac{1}{2}\log(2\pi n) + O(n^{-1})$ as $n \to \infty$.
   - **Source**: Classical Euler–Maclaurin / Stirling asymptotic expansion.

4. **`erdos_selfridge_consecutive_product_not_square`**
   - **Statement**: For $a \ge 1$ and $k \ge 2$, $\prod_{j=0}^{k-1} (a + j)$ is never a square.
   - **Source**: P. Erdős and J. L. Selfridge, *The product of consecutive integers is never a power*, Illinois J. Math. 19 (1975), 292–301.

5. **`nagura_prime_in_interval`**
   - **Statement**: For every real $x \ge 25$, there exists a prime $p$ with $x < p < \frac{6}{5}x$.
   - **Source**: J. Nagura, *On the interval containing at least one prime number*, Proc. Japan Acad. 28 (1952), 177–181.

6. **`leopoldt_coates_valuation_law`** (using `RealQuadIwasawaInvariants`)
   - **Statement**: Leopoldt's $p$-adic class number formula and Coates's formula for $K = \mathbb{Q}(\sqrt{q})$ at $p \ge 5$ with $v_p(\widetilde{R}_p(K)) \ge 1$, giving exact formulas for $v_p(L_p(1, \chi_D))$ and $v_p(\#T_{K,p})$ in both unramified ($p \nmid q$) and ramified ($p \mid q$) cases.
   - **Source**: L. C. Washington, *Introduction to Cyclotomic Fields* (2nd ed., 1997), Theorem 5.24; J. Coates, *On $p$-adic $L$-functions and Iwasawa's theory*, Algebraic Number Fields (1977), Appendix Lemma 8; H. Taya, *On $p$-adic zeta functions and $\mathbb{Z}_p$-extensions of certain totally real number fields*, Tohoku Math. J. 48 (1996), Prop. 1.

7. **`iwasawa_main_conjecture_free_rank`**
   - **Statement**: For $K = \mathbb{Q}(\sqrt{q})$ at $p \ge 5$, $\mu_p(\chi_D) = 0$, $X_p(K_\infty)$ is free over $\mathbb{Z}_p$ of rank $\lambda_p^*(K) = \lambda_p(\chi_D)$, and $T_{K,p} \neq 0$ implies $\lambda_p^*(K) = \lambda_p(\chi_D) \ge 1$.
   - **Source**: B. Ferrero and L. C. Washington (1979); B. Mazur and A. Wiles (1984); R. Greenberg, *A note on $K_2$ and the theory of $\mathbb{Z}_p$-extensions*, Amer. J. Math. 100 (1978), Prop. 3.

8. **`ozaki_taya_split_prime_iwasawa`**
   - **Statement**: For a split prime $p \ge 5$ ($p \nmid q$) with $v_p(\widetilde{R}_p(K)) \ge 2$: $|X(K_\infty)_\Gamma| = |A_m^\Gamma| = |T_{K,p}|$ for $m \ge v_p(\widetilde{R}_p(K)) - 1$; $\lambda_p(K) + \nu_p(K) \ge v_p(\widetilde{R}_p(K)) - 1$; and $n_0^{(r)}(K) > r + 1$ for all $r \ge 0$ implies $\lambda_p(K) \ge 1$.
   - **Source**: M. Ozaki (1997), Prop. 1; S. Yanagisawa (2026), Lemmas 6.1–6.2; H. Taya (1996), Cor. 2–3, Thm. 4.

## Section 4 External Axioms (`GrasGreenbergBrocard/ExternalAxiomsSec4.lean`)

1. **`mertens_first_theorem_odd_primes`**
   - **Statement**: $\sum_{3 \le p \le x} \frac{\log p}{p - 1} = \log x - \gamma - \log 2 + o(1)$ as $x \to \infty$, with $0.5772 < \gamma < 0.5773$.
   - **Source**: F. Mertens (1874); H. Davenport, *Multiplicative Number Theory* (3rd ed., 2000), Ch. 7.

2. **`nth_prime_asymptotic`**
   - **Statement**: The $k$-th prime $p_k$ satisfies $p_k = (1 + o(1))\, k \log k$ as $k \to \infty$.
   - **Source**: Prime Number Theorem (Hadamard / de la Vallée Poussin 1896; Davenport 2000, Ch. 18).
