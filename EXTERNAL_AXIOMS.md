# External Axioms Inventory

All external axioms in this repository represent **established, peer-reviewed mathematical theorems** external to the manuscript's own contributions, where Mathlib v4.35.0 does not yet provide a formalization. **Zero** manuscript-owned lemmas, propositions, or theorems are axiomatized.

## Section 2 External Axioms (`GrasGreenbergBrocard/ExternalAxiomsAnalytic.lean`)
Classical analytic number theory bounds (Vaaler trigonometric polynomial approximation and exponential sum estimates) supporting the Section 2 valuation-parity distribution theorems.

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
