# Mathematical Corrections and Formal Audit Record

## Summary

Across Sections 2, 3, 4, 5, 6, 7, and 8 (the entire manuscript, including Theorems 1.1, 1.2, 1.3(i)–(ii), 2.5, 4.2, 5.2, 5.3, 6.4(a)–(b), 8.1(i)–(ii), and 8.2), all formalized statements and proofs in `GrasGreenbergBrocard/` match the mathematical content of `brocard_arithmetic_structure_and_counting_bounds.tex` with **zero** fatal mathematical flaws, **zero** `sorry` placeholders, **zero** kernel-bypass tactics, and **zero** silent weakenings.

Three surgical manuscript refinements (in Theorem 6.4(b), Theorem 8.1(ii), and Theorem 8.2) were identified during formalization and synchronized with the manuscript without altering any qualitative conclusions or asymptotic orders of magnitude. In addition, a two-stage adversarial audit ([PR #7](https://github.com/princeanand099/grasgreenbergbrocard/pull/7) and [PR #8](https://github.com/princeanand099/grasgreenbergbrocard/pull/8)) hardened all external literature axioms and replaced the Section 6.3 oscillatory argument with an honest collar-excised multi-digit Vaaler proof.

## Adversarial Formalization Audits (PR #7 & PR #8)

### Stage 1: External Axiom Soundness Hardening ([PR #7](https://github.com/princeanand099/grasgreenbergbrocard/pull/7), Merge SHA `d22839cc`)
An exhaustive audit of all `ExternalAxioms*.lean` files identified four under-constrained axiom signatures that were tightened to exclude unintended or vacuous instantiations:

1. **`bpz_dyadic_cluster_elimination` (`ExternalAxiomsSec7.lean`)**: Bound explicitly to `IsPolyFactSol` and `HasDepressedDegreeGap`, paired with an internal proof of `brocard_poly_depressed_gap` for $P(x) = x^2 - 1$.
2. **`siegel_bpz_support_wronskian` (`ExternalAxiomsSec7.lean`)**: Added the explicit Padé vanishing-order bound hypothesis `hO`.
3. **Iwasawa axioms (`ExternalAxiomsSec3.lean`)**: Scoped to `canonicalRealQuadIwasawa q p` instead of quantifying over arbitrary abstract `RealQuadIwasawaInvariants` tuples.
4. **`tatuzawa_effective_siegel` (`ExternalAxiomsSec8.lean`)**: Scoped to `canonicalRealQuadClassGroup` instead of arbitrary `RealQuadClassGroupData` records.
5. **Automated `#print axioms` audit (`AuditAxioms.lean`)**: Added kernel-level axiom verification for all 42 main theorems on every CI run.

### Stage 2: Analytic Axiom Tightening & Honest Section 6.3 Proof ([PR #8](https://github.com/princeanand099/grasgreenbergbrocard/pull/8), Merge SHA `0def862b`)
The final residual audit gap was closed completely:

1. **`vaughan_van_der_corput_prime_sum` (`ExternalAxiomsAnalytic.lean`)**: Tightened with explicit `IsPrimeSubinterval P I` (contiguous prime subinterval of $[P, 2P]$) and `AntitoneOn w (Set.Icc P (2 * P))` (monotone decreasing weight), preventing oscillatory functions from being absorbed into the weight $w$.
2. **Section 2 Propagation**: Updated `ExpSumBounds.lean`, `ExpSumBoundsMod.lean`, and all six `ValuationParity*` modules to discharge `IsPrimeSubinterval` and monotonicity at every invocation.
3. **Honest Section 6.3 Proof (`Lem6_3ParityFlipOsc.lean`, `Lem6_3ParityFlip.lean`, `Thm6_4CapacityDiamond.lean`)**: Replaced the prior oscillatory-weight argument with `lem_6_3_osc_bound_honest`, a collar-excised multi-digit Vaaler exponential-sum proof using exclusively the monotone weight $w(t) = 1/t$, genuine prime subintervals, and the non-resonance gap hypothesis. All public theorem statements in `Thm6_4CapacityDiamond.lean` and `Thm6_4PolarizationConcentration.lean` remain unchanged.

## Section-by-Section Mathematical Audit Notes

### Sections 2–5
- **Classification**: Sound (zero mathematical flaws).
- **Details**: All parity-layer asymptotics (Section 2), Pell collapse and Iwasawa valuation/finiteness theorems (Section 3), Picard $2$-torsion and quartic core locks (Section 4), and continued-fraction midpoint bias, Davenport effective core bounds, and Rédei–Reichardt cohomology (Section 5) are verified in Lean 4. `thm_5_2_part1_cross_symmetry` is proved purely from Lean's standard axioms.

### Section 6 (Capacity Diamond, $k=2$ Gap & Polarization Concentration)
- **Classification**: Sound, with one explicit low-prime error-term refinement in Theorem 6.4(b).
- **Details**:
  - **Proposition 6.1** (`Prop6_1FourGCD.lean`) and **Proposition 6.2(iii)** (`Prop6_2ConsecutiveSquareShift.lean`): Proved purely from Lean's standard axioms with zero external mathematical axioms. In Proposition 6.2(iii), both $u = t m_1 - m_2 = 1$ (yielding $t = 2 m_1$, contradiction) and $u \ge 2$ (yielding $2 m_1 < t$, contradiction) are handled cleanly for all $t < 2 m_1$, and consecutive-square $(k_{j^2}, k_{(j+1)^2}) \neq (2,2)$ exclusion is proved in `prop_6_2_part3_consecutive_squares_k2_exclusion`.
  - **Lemma 6.3** (`Lem6_3ParityFlipOsc.lean`, `Lem6_3ParityFlip.lean`): Verified via the tightened `vaughan_van_der_corput_prime_sum` and `lem_6_3_osc_bound_honest` (PR #8).
  - **Theorem 6.4(b) Polarization Concentration** (`Thm6_4PolarizationConcentration.lean`): The inner-product bound $|\langle \mathbf{u}_{n_1}, \mathbf{u}_{n_2} \rangle_w|$ includes an explicit $O(1/\log N')$ contribution from $v_2(N'!) \log 2 / W_{\mathrm{tot}}$ alongside the $O((N')^{-\varepsilon})$ error: $|\langle \mathbf{u}_{n_1}, \mathbf{u}_{n_2} \rangle_w| = O(1/\log N') + O((N')^{-\varepsilon}) = o(1)$. This vanishes as $N' \to \infty$ and preserves the exact Rankin interval bound $\lfloor (\eta^2 \varepsilon)^{-1} \rfloor + 1$ and dyadic counting bound $C_\varepsilon \eta^{-2} N^\varepsilon$.

### Section 7 (Support-Reduced Padé–Wronskian Method & Theorem 1.3(ii))
- **Classification**: Sound (zero mathematical flaws; all Table 1 and Table 2 exponents verified algebraically).
- **Details**:
  - Siegel's Lemma (`siegel_lemma_pigeonhole`), initial Padé polynomials (`lem_7_1_initial_pade_polynomials`), monomial-product Puiseux linear independence (`lem_7_2_monomial_product_puiseux_indep`), support-reduced Wronskian (`lem_7_3_support_reduced_wronskian`), and denominator clearing (`lem_7_4_denominator_clearing`) are proved completely from Mathlib with **zero external axioms**.
  - Every exponent in Table 1 ($\theta_2(2-\sqrt{2}) = 17 - 12\sqrt{2} > 1/34$, $\theta_3(3-\sqrt{3}) = 7 - 4\sqrt{3} > 0.07179$, $\theta_4(2) = 1/9$, $\theta_5(5-\sqrt{5}) = (7 - 3\sqrt{5})/2 > 1/7$) and Table 2 ($\nu = 3, 4, 5, \ge 6, \ge 25$) is verified by exact arithmetic in `Thm1_3Part2Counting.lean`.

### Section 8 (Elliptic Curve Realizations and Effective Class Group Bounds)
- **Classification**: Two surgical constant/base-conversion refinements synchronized with the manuscript (all qualitative conclusions and asymptotic rates preserved).
- **Details**:
  1. **Theorem 8.1(ii) $abc$-Quality Leading Constant** (`Thm8_1FreyCurves.lean`):
     - *Issue*: The original draft cited Theorem 4.2(i) for $\log \operatorname{rad}(2 q_n Y_1(q_n)) \le (\log 2 + o(1)) n$, which bounds $\log q_n$ but does not exclude primes in $\mathcal{P}_{\mathrm{even}}(n)$ dividing $Y_1(q_n)$. Since $2 q_n Y_1(q_n) \mid n!$, every prime dividing $A_n B_n C_n$ divides $n!$, giving $\log \operatorname{rad}(A_n B_n C_n) \le \vartheta(n) = (1 + o(1)) n$.
     - *Synchronized Fix*: Replaced $\bigl(\frac{1}{4\log 2} - o(1)\bigr)\log n$ with the unconditionally verified $\bigl(\frac{1}{4} - o(1)\bigr)\log n \to \infty$ (preserving $q(A_n, B_n, C_n) = \Omega(\log n) \to \infty$).
  2. **Theorem 8.2 Narrow $2^J$-Rank Exponent Base Conversion** (`Thm8_2TatuzawaClassGroup.lean`):
     - *Issue*: The proof derives $\log_2 \exp(\mathcal{A}_2(q_n)) \ge \bigl(\frac{1}{4\log 2} - \varepsilon\bigr)\log n$. Converting from base $2$ to base $e$ gives $2^{(\frac{1}{4\log 2} - \varepsilon)\log n} = e^{(\frac{1}{4} - \varepsilon \log 2)\log n} = n^{\frac{1}{4} - \varepsilon \log 2} \ge n^{\frac{1}{4} - \varepsilon}$, whereas the earlier theorem statement omitted the $\log 2$ factor and wrote $n^{\frac{1}{4\log 2} - \varepsilon}$.
     - *Synchronized Fix*: Corrected the exponent in the theorem statement to $\exp(\mathcal{A}_2(q_n)) \ge n^{\frac{1}{4} - \varepsilon}$ while explicitly retaining $\log_2 \exp(\mathcal{A}_2(q_n)) \ge \bigl(\frac{1}{4\log 2} - \varepsilon\bigr)\log n$ in both the manuscript and `thm_8_2_tatuzawa_and_narrow_2J_rank`.
