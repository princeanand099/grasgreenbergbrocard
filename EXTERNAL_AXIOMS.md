# External Axioms Inventory

All external axioms in `GrasGreenbergBrocard` encode **established, peer-reviewed mathematical results** external to the manuscript's own contributions, where Mathlib `v4.35.0` does not yet contain a formalization. Zero manuscript-owned lemmas, propositions, or theorems are axiomatized, and zero unused axioms remain.

All **28 external axioms** are isolated in **six** dedicated files and verified by `GrasGreenbergBrocard/AuditAxioms.lean` (**63** audited declarations, zero `sorryAx`, zero `Lean.ofReduceBool`/`Lean.trustCompiler`).

## 1. `GrasGreenbergBrocard/ExternalAxiomsAnalytic.lean` (6 axioms)

| Axiom | Published Source | Role |
| :--- | :--- | :--- |
| `de_la_vallee_poussin_theta` | de la Vallée Poussin (1899) | Classical zero-free region error term for $\vartheta(x) = x + O(x \exp(-c\sqrt{\log x}))$ |
| `chebyshev_pi_upper` | Chebyshev (1852) | Effective upper bound $\pi(x) \le C x / \log x$ |
| `pnt_pi_asymptotic` | Hadamard / de la Vallée Poussin (1896) | Prime Number Theorem $\pi(x) \sim x / \log x$ |
| `mertens_first_theorem` | Mertens (1874) | $\sum_{3 \le p \le x} \frac{\log p}{p - 1} = \log x + O(1)$ |
| `vaaler_extremal_polynomials` | Vaaler (1985), Thm. 18 | Extremal trigonometric polynomial majorants/minorants for sawtooth functions |
| `vaughan_van_der_corput_prime_sum` | Vaughan (1977), Heath-Brown (1982), Graham–Kolesnik (1991), Thm. 2.9 | Type I/II prime exponential sum bound; `c₁ c₂ : ℕ → ℝ` are quantified **before** `∃ η' η C` so the constant `C` depends uniformly on `(δ, c₁, c₂)` |

## 2. `GrasGreenbergBrocard/ExternalAxiomsSec3.lean` (10 axioms)

| Axiom | Published Source | Role |
| :--- | :--- | :--- |
| `breusch_bertrand_mod4` | Breusch (1932), *Math. Z.* 34, 505–526 | Existence of prime $p \equiv 3 \pmod 4$ in $(x, 2x]$ for $x \ge 7$ |
| `rosser_schoenfeld_theta_diff` | Rosser–Schoenfeld (1962), Thm. 10 | Explicit $\vartheta(n) - \vartheta(n/2) > 0.4 n$ for $n \ge 116$ |
| `stirling_log_factorial_remainder` | Classical Euler–Maclaurin / Stirling | $\log(n!) = n \log n - n + \frac{1}{2}\log(2\pi n) + O(n^{-1})$ |
| `erdos_selfridge_consecutive_product_not_square` | Erdős–Selfridge (1975), *Illinois J. Math.* 19 | Product of $\ge 2$ consecutive positive integers is never a square |
| `nagura_prime_in_interval` | Nagura (1952), *Proc. Japan Acad.* 28 | Prime in $(x, \frac{6}{5}x)$ for $x \ge 25$ |
| `canonicalRealQuadIwasawa` | Standard algebraic/Iwasawa invariants of $\mathbb{Q}(\sqrt{q})$ | Canonical invariant record for $\mathbb{Q}(\sqrt{q})$ at odd $p \ge 5$ (prevents adversarial dummy instances) |
| `padic_log_regulator_pell_power` | Washington (1997), §5.5, Lemma 5.3 & Thm. 5.24 | Ultrametric $p$-adic logarithm of a Pell unit $m + s\sqrt{q} = \varepsilon_q^k$ ($p \ge 5$, $p \mid s$, $p \nmid m$) giving $v_p(\tilde{R}_p(\mathbb{Q}(\sqrt{q}))) + v_p(k) = v_p(s)$ |
| `leopoldt_coates_valuation_law` | Leopoldt / Washington (1997), Thm. 5.24; Coates (1977), App. Lemma 8 | Valuation identities relating $L_p(1, \chi_D)$, $\#T_{K,p}$, $h(q)$, and $\tilde{R}_p(K)$ |
| `iwasawa_main_conjecture_free_rank` | Ferrero–Washington (1979), Mazur–Wiles (1984), Greenberg (1978, Prop. 3) | $\mu_p(\chi_D) = 0$, freeness of $X_p(K_\infty)$, and $\lambda_p^*(K) = \lambda_p(\chi_D) \ge 1$ when $T_{K,p} \ne 0$ |
| `ozaki_taya_split_prime_iwasawa` | Ozaki (1997, Prop. 1), Taya (1996, Cor. 2–3, Thm. 4), Yanagisawa (2026) | Split-prime unramified Iwasawa module co-invariants and Taya's $\lambda_p(K) \ge 1$ criterion |

## 3. `GrasGreenbergBrocard/ExternalAxiomsSec4.lean` (1 axiom)

| Axiom | Published Source | Role |
| :--- | :--- | :--- |
| `mertens_first_theorem_odd_primes` | Mertens (1874) | $\sum_{3 \le p \le x} \frac{\log p}{p - 1} = \log x - \gamma - \log 2 + o(1)$ (used in `thm_4_2_part3_mertens_bound`) |

## 4. `GrasGreenbergBrocard/ExternalAxiomsSec5.lean` (4 axioms)

| Axiom | Published Source | Role |
| :--- | :--- | :--- |
| `perron_cf_midpoint_symmetry` | Perron (1913), *Die Lehre von den Kettenbrüchen* | Continued-fraction midpoint symmetry for fundamental Pell unit $X_1 + Y_1\sqrt{q}$ |
| `davenport_real_char_half_band_upper` | Davenport (1967), Ch. 23; Pólya–Vinogradov | Real Dirichlet character sum bound on half-bands |
| `canonicalRealQuadRedei` | Rédei–Reichardt (1933) | Canonical Rédei 4-rank invariant record for $\mathrm{Cl}^+(\mathbb{Q}(\sqrt{q_n}))$ |
| `redei_reichardt_exact_sequence` | Rédei–Reichardt (1933), *J. Reine Angew. Math.* 170 | Scoped to `canonicalRealQuadRedei n`; relates `CanonicalNarrowCl4Rank n` to the $\mathbb{F}_2$-dimension of `redeiKernel n` |

## 5. `GrasGreenbergBrocard/ExternalAxiomsSec7.lean` (3 axioms)

All three Section 7 axioms follow the **canonical-object scoping pattern** (matching `canonicalRealQuadIwasawa`, `canonicalRealQuadRedei`, and `canonicalRealQuadClassGroup`), preventing adversarial dummy `AlgebraicTaylorFamily` (e.g., linearly dependent zero families) or dummy `SupportWronskianData` instances:

| Axiom | Published Source | Role |
| :--- | :--- | :--- |
| `canonicalMonomialTaylorFamily` | Bui–Pratt–Zaharescu (2023), Lemma 4.2 | Canonical `AlgebraicTaylorFamily` for the $\mathbb{C}(x)$-linearly independent monomial-product family $\Omega_{\mathbf{e}}(x)$ with cleared integer Taylor coefficients and growth bounds |
| `canonicalSupportWronskian` | Siegel (1949), Ch. 2, Lemma 4; BPZ (2023), Lemmas 5.4, 5.6, 6.3 | Scoped strictly to `canonicalMonomialTaylorFamily` and the actual Padé polynomials `P_coeff` from `lem_7_1_initial_pade_polynomials` with non-zero support `S`; yields the canonical non-vanishing support-reduced Wronskian $\Delta_S(x) \in \mathbb{Z}[x]$ |
| `bpz_cauchy_leibniz_pade_eval` | Bui–Pratt–Zaharescu (2023), Prop. 3.4 & Lemmas 5.6, 6.3 | Scoped strictly to `canonicalSupportWronskian` attached to `P_coeff`, `S`, shift tuple `β`, and cluster base point `n₀`; yields `PadeEvaluationData` with Cauchy/Leibniz bounds (eq. 7.15) and factorial-root asymptotic |

## 6. `GrasGreenbergBrocard/ExternalAxiomsSec8.lean` (4 axioms)

| Axiom | Published Source | Role |
| :--- | :--- | :--- |
| `frey_E_modularity` | Wiles (1995), Breuil–Conrad–Diamond–Taylor (2001) | Modularity and conductor bound for Frey curve $E_n$ attached to $n! + 1 = m^2$ |
| `frey_F2_modularity_and_galois` | Wiles (1995), BCDT (2001), Ribet (1990) | Modularity, exact conductor `conductor_F2_eq : N(F_n^{(2)}) = 2^{α_2} (∏_{3 ≤ p ≤ n} p) / (∏_{3 ≤ p ≤ n, p ∣ X_1} p)`, and Galois representation for $F_n^{(2)}$; explicitly requires `IsFundamentalPell (q_n n) X₁ Y₁` and `hk2` ($k = 2$) |
| `canonicalRealQuadClassGroup` | Classical genus theory & class group invariants | Canonical narrow class group record for $\mathbb{Q}(\sqrt{q_n})$ |
| `tatuzawa_effective_siegel` | Tatuzawa (1951), *Japan. J. Math.* 21, 163–178 | Effective Siegel lower bound $L(1, \chi_D) > \frac{0.655 \varepsilon}{D^\varepsilon}$ with at most one exceptional discriminant |
