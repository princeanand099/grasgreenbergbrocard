# External Axioms Inventory

All **28 custom axioms** in `GrasGreenbergBrocard` are isolated in **six** dedicated files and audited across **78 public declarations** in `GrasGreenbergBrocard/AuditAxioms.lean` (zero `sorryAx`, zero `Lean.ofReduceBool`/`Lean.trustCompiler`).

For full transparency, this inventory explicitly distinguishes between:
- **Standard external theorems** not yet in Mathlib `v4.35.0` (e.g., PNT, Mertens, Vaaler, Vaughan–van der Corput, Breusch, Rosser–Schoenfeld, Stirling, Erdős–Selfridge, Nagura, Perron, Davenport, Tatuzawa), and
- **Scoped analytic/algebraic interface axioms** over opaque records or unformalized analytic objects (specifically `canonicalRealQuadIwasawa`, `canonicalRealQuadRedei`, `canonicalRealQuadClassGroup`, `canonicalMonomialTaylorFamily`, `canonicalSupportWronskian`, `bpz_cauchy_leibniz_pade_eval`, and the conductor/trace axioms on `WeierstrassCurve ℤ` in Section 8), where full Mathlib formalization of Iwasawa modules, Puiseux/ODE Wronskian analysis, or Tate's algorithm is not yet available.

## 1. `GrasGreenbergBrocard/ExternalAxiomsAnalytic.lean` (6 axioms)

| Axiom | Published Source | Role & Soundness Conditions |
| :--- | :--- | :--- |
| `de_la_vallee_poussin_theta` | de la Vallée Poussin (1899) | Classical zero-free region error term for $\vartheta(x) = x + O(x \exp(-c\sqrt{\log x}))$ |
| `chebyshev_pi_upper` | Chebyshev (1852) | Effective upper bound $\pi(x) \le C x / \log x$ |
| `pnt_pi_asymptotic` | Hadamard / de la Vallée Poussin (1896) | Prime Number Theorem $\pi(x) \sim x / \log x$ |
| `mertens_first_theorem` | Mertens (1874) | $\sum_{3 \le p \le x} \frac{\log p}{p - 1} = \log x + O(1)$ |
| `vaaler_extremal_polynomials` | Vaaler (1985), Thm. 18 | Extremal trigonometric polynomial majorants/minorants for sawtooth functions |
| `vaughan_van_der_corput_prime_sum` | Iwaniec & Kowalski (2004), Prop. 13.4, Cor. 8.11/8.13, Thm. 8.25 | Type I/II prime exponential sum bound; `c₁ c₂` are quantified before `∃ η' η C`, and `T₀ ≤ (n : ℝ) ^ 2` is enforced to prevent unbounded-$T_0$ inconsistency |

## 2. `GrasGreenbergBrocard/ExternalAxiomsSec3.lean` (10 axioms)

| Axiom | Published Source | Role & Soundness Conditions |
| :--- | :--- | :--- |
| `breusch_bertrand_mod4` | Breusch (1932), *Math. Z.* 34, 505–526 | Existence of prime $p \equiv 3 \pmod 4$ in $(x, 2x]$ for $x \ge 7$ |
| `rosser_schoenfeld_theta_diff` | Rosser–Schoenfeld (1962), Thm. 10 | Explicit $\vartheta(n) - \vartheta(n/2) > 0.4 n$ for $n \ge 116$ |
| `stirling_log_factorial_remainder` | Classical Euler–Maclaurin / Stirling | $\log(n!) = n \log n - n + \frac{1}{2}\log(2\pi n) + O(n^{-1})$ |
| `erdos_selfridge_consecutive_product_not_square` | Erdős–Selfridge (1975), *Illinois J. Math.* 19 | Product of $\ge 2$ consecutive positive integers is never a square |
| `nagura_prime_in_interval` | Nagura (1952), *Proc. Japan Acad.* 28 | Prime in $(x, \frac{6}{5}x)$ for $x \ge 25$ |
| `canonicalRealQuadIwasawa` | Standard algebraic/Iwasawa invariants of $\mathbb{Q}(\sqrt{q})$ | Opaque canonical invariant record for $\mathbb{Q}(\sqrt{q})$ at odd $p \ge 5$ |
| `padic_log_regulator_pell_power` | Washington (1997), §5.5, Lemma 5.3 & Thm. 5.24 | Requires `Squarefree q`; packages the ultrametric $p$-adic logarithm step $v_p(\tilde{R}_p(\mathbb{Q}(\sqrt{q}))) + v_p(k) = v_p(s)$ (manuscript eq. 3.6) over `canonicalRealQuadIwasawa q p` |
| `leopoldt_coates_valuation_law` | Leopoldt / Washington (1997), Thm. 5.24; Coates (1977), App. Lemma 8 | Requires `Squarefree q`; valuation identities relating $L_p(1, \chi_D)$, $\#T_{K,p}$, $h(q)$, and $\tilde{R}_p(K)$ |
| `iwasawa_main_conjecture_free_rank` | Ferrero–Washington (1979), Mazur–Wiles (1984), Greenberg (1978, Prop. 3) | $\mu_p(\chi_D) = 0$, freeness of $X_p(K_\infty)$, and $\lambda_p^*(K) = \lambda_p(\chi_D) \ge 1$ when $T_{K,p} \ne 0$ |
| `ozaki_taya_split_prime_iwasawa` | Ozaki (1997, Prop. 1), Taya (1996, Cor. 2–3, Thm. 4), Yanagisawa (2026) | Split-prime unramified Iwasawa module co-invariants and Taya's $\lambda_p(K) \ge 1$ criterion |

## 3. `GrasGreenbergBrocard/ExternalAxiomsSec4.lean` (1 axiom)

| Axiom | Published Source | Role |
| :--- | :--- | :--- |
| `mertens_first_theorem_odd_primes` | Mertens (1874) | $\sum_{3 \le p \le x} \frac{\log p}{p - 1} = \log x - \gamma - \log 2 + o(1)$ |

## 4. `GrasGreenbergBrocard/ExternalAxiomsSec5.lean` (4 axioms)

| Axiom | Published Source | Role & Soundness Conditions |
| :--- | :--- | :--- |
| `perron_cf_midpoint_symmetry` | Perron (1954), §25 | Continued-fraction midpoint symmetry for fundamental Pell unit $X_1 + Y_1\sqrt{q}$ |
| `davenport_real_char_half_band_upper` | Davenport (2000), Chapter 19 | Explicit formula for $\psi(x, \chi)$ and de la Vallée Poussin zero-free region on half-bands |
| `canonicalRealQuadRedei` | Rédei (1934) | Opaque canonical narrow 4-rank $\mathbb{F}_2$-vector space for $\mathrm{Cl}^+(\mathbb{Q}(\sqrt{q_n}))$ |
| `redei_reichardt_exact_sequence` | Gauss (1801); Hasse (1930); Rédei (1934) | Scoped to `canonicalRealQuadRedei n`, the repaired `ramPrimes n` (including $p = 2$ when $2 \mid D_n$), exact 2-adic Hilbert row `redeiRowTwo`, and the Lean-proved `yMidVec_mem_redeiKernel` and `yMidVec_ne_zero` |

## 5. `GrasGreenbergBrocard/ExternalAxiomsSec7.lean` (3 axioms)

All three Section 7 axioms use canonical-object scoping, enforce the exact $0 \in S \iff P_0 \not\equiv 0$ condition via `padeP0Coeff` (`hS_zero`), and use the corrected factorial-root bound $(2 n_0)^{M\nu/r} x_0^{-\nu}$ in `PadeEvaluationData.rho_le`. **Honest scope note**: while Siegel's Lemma, Lemma 7.1, the Pigeonhole cluster reduction (eq. 7.17), general polynomial depression (eq. 7.1), and the exponent elimination algebra (`dyadic_cluster_elimination_proved`) are proved from Mathlib, the analytic Puiseux/ODE Wronskian construction and Cauchy–Leibniz derivative estimates for general $(d, E, \nu)$ (packaging the analytic steps of Lemmas 7.2–7.4) are currently represented by these three scoped axioms.

| Axiom | Published Source | Role |
| :--- | :--- | :--- |
| `canonicalMonomialTaylorFamily` | Bui–Pratt–Zaharescu (2023), Lemma 4.2 | Canonical `AlgebraicTaylorFamily` for $\Omega_{\mathbf{e}}(x)$ |
| `canonicalSupportWronskian` | Siegel (1949), Ch. 2, Lemma 4; BPZ (2023), Lemmas 5.4, 5.6, 6.3 | Scoped to `canonicalMonomialTaylorFamily`, `P_coeff`, `hS_zero`, and `hS_eq`; yields `SupportWronskianData` |
| `bpz_cauchy_leibniz_pade_eval` | Bui–Pratt–Zaharescu (2023), Prop. 3.4 & Lemmas 5.6, 6.3 | Scoped to `canonicalSupportWronskian` with `hS_zero` and `hS_eq`; yields `PadeEvaluationData` with corrected `rho_le : ρ ≤ C_P * (2 * n₀)^(M * ν / r) * x₀^(-ν)` |

## 6. `GrasGreenbergBrocard/ExternalAxiomsSec8.lean` (4 axioms)

| Axiom | Published Source | Role & Soundness Conditions |
| :--- | :--- | :--- |
| `frey_E_modularity` | Tate's algorithm; Wiles (1995); Breuil–Conrad–Diamond–Taylor (2001) | Concrete conductor $N(\mathcal{E}_n)$ and Frobenius traces $a_p(\mathcal{E}_n) = (-m/p)$ bound to Mathlib `WeierstrassCurve ℤ` model `freyCurveE m` (no vacuous `Prop` fields) |
| `frey_F2_modularity_and_galois` | Tate's algorithm; Wiles (1995); BCDT (2001); Mazur (1978); Kenku (1982); Serre (1972) | Concrete slashed conductor $N(F_n^{(2)})$ bound to Mathlib `WeierstrassCurve ℤ` model `freyCurveF2 X₁` under `IsFundamentalPell` and `hk2` (no vacuous `Prop` fields) |
| `canonicalRealQuadClassGroup` | Davenport (2000), Ch. 6; Gauss (1801) | Opaque canonical narrow class group / regulator / $L(1, \chi_{D_n})$ record for $\mathbb{Q}(\sqrt{q_n})$ |
| `tatuzawa_effective_siegel` | Tatuzawa (1951), *Japan. J. Math.* 21, 163–178 | Effective Siegel lower bound $L(1, \chi_D) > \frac{0.655 \varepsilon}{D^\varepsilon}$ with at most one exceptional discriminant |
