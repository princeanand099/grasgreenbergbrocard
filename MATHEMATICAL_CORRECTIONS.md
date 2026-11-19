# Mathematical Corrections and Audit Record

## Summary
Across Sections 2, 3, 4, 5, 6, 7, and 8 (the entire manuscript, including Theorems 1.1, 1.2, 1.3(i)–(ii), 2.5, 4.2, 5.2, 5.3, 6.4, 8.1, and 8.2), all formalized statements and proofs in `GrasGreenbergBrocard/` match the mathematical content of `brocard_arithmetic_structure_and_counting_bounds.tex` with **zero** fatal mathematical flaws and **zero** silent weakenings. Two surgical constant/base-conversion fixes were identified and corrected in Section 8 without altering any qualitative conclusions or asymptotic orders of magnitude.

## Section-by-Section Audit Notes

### Section 2 (Valuation-Parity Equidistribution)
- **Classification**: Sound (minor formalization refinements only).
- **Details**: Base-$p$ digit reduction and Vaaler odd-harmonic expansion with transition-collar excision (`ValuationParityThmCollar.lean`, `ValuationParityThmInterCollar.lean`, `ValuationParityModCollar.lean`, `ValuationParityModInterCollar.lean`) establish $\Delta_{\mathrm{parity}}(n) = o(n\log n)$ and multi-modulus power-band equidistribution faithfully.

### Section 3 (Chebyshev–Lucas Absorption, Theorems 1.1 & 1.2)
- **Classification**: Sound.
- **Details**: Chebyshev–Lucas $p$-adic Lifting-the-Exponent (`ChebyshevLucas.lean`) is proved completely without external axioms. The known small solutions $n = 4, 5, 7$ (`known_k4`, `known_k5`, `known_k7`) and asymptotic collapse $k \in \{1, 2\}$ (`pell_index_collapse_large`) are verified without weakening hypotheses.

### Section 4 (Critical Regime $k = 2$: Proposition 4.1 & Theorem 4.2)
- **Classification**: Sound (explicit constant & bound precision formalized).
- **Details**:
  - First-stage Euclidean division $A_n = B_n Q_n + R_n$ with $Q_n = Z^4$ and $R_n = Z^2$ (`thm_4_2_part1_quartic_law`) and second-stage consecutive splitting $B_+ R_n = B_- Z_-^4 + \dots$ (`thm_4_2_part2_dual_quartic`) hold unconditionally for $n \ge 8$ when $k = 2$.
  - In Theorem 4.2(iii), both the power-band stretched-exponential lower bound $\delta_i(n) \ge \exp(n^{1/2-\varepsilon})$ (`thm_4_2_part3_midpoint_core_bounds`) and the explicit Mertens $n^{1/4}$ lower bound (`thm_4_2_part3_mertens_bound`) are proved using `mertens_first_theorem_odd_primes` and `ValuationParityMod`.

### Section 5 (The Fundamental Regime $k = 1$ and Rédei–Reichardt Cohomology)
- **Classification**: Sound (all algebraic, analytic, and cohomological claims verified without weakening).
- **Details**:
  - **Midpoint Bias & Cross-Symmetry** (`Prop5_1MidpointBias.lean`): Perron §25 midpoint symmetry yields the exact $k=1$ factorization and upper-half Legendre symbol bias $\psi_{\mathrm{eval}}$ over $n/2 < p \le n$.
  - **Effective Cores & $\delta_2 \neq 2$** (`Thm5_2EffectiveCores.lean`): Combined Davenport Ch. 19 upper-half character sum bounds with `ValuationParityMod` to prove `thm_5_2_part2_effective_cores`; proved `delta2Mid_ne_two` and `thm_5_2_part2_pell_pm2_insoluble` elementarily via $2$-adic valuation parity without additional axioms.
  - **Rédei–Reichardt Cohomology & Inert Absorption** (`Thm5_3RedeiCohomology.lean`): Formalized the $\mathbb{F}_2$-cohomological 4-rank exact sequence (`thm_5_3_part1_cohomology_4rank`) and proved the inert-prime divisibility absorption `thm_5_3_part2_inert_absorption` using an elementary `Nat.Coprime` induction over `Finset.prod` for $W_1, W_2$.

### Section 6 (Pairwise $\mathrm{SL}_2(\mathbb{Z})$ Duality, Capacity Diamond, and Theorem 1.3(i))
- **Classification**: Sound (all algebraic, analytic, and counting claims verified without weakening and with zero new external axioms).
- **Details**:
  - **Proposition 6.2(iii) ($P = t^2 < 4(n_1! + 1)$)** (`Prop6_2ConsecutiveSquareShift.lean`): Handled both $u = t m_1 - m_2 = 1$ (yielding $t = 2 m_1$, contradiction) and $u \ge 2$ (yielding $2 m_1 < t$, contradiction) cleanly for all $t < 2 m_1$.
  - **Proposition 6.2(iii) Consecutive Squares $(k_{j^2}, k_{(j+1)^2}) \neq (2, 2)$** (`Thm6_4CapacityDiamond.lean`): Proved rigorously in `prop_6_2_part3_consecutive_squares_k2_exclusion` from `thm_1_3_part1_k2_gap_and_counting`.
  - **Theorem 6.4(b) Polarization Concentration** (`Thm6_4PolarizationConcentration.lean`): The inner product bound $|\langle u_{n_1}, u_{n_2}\rangle_w|$ includes an explicit $O(1/\log N')$ contribution from $v_2(N'!)\log 2 / W_{\mathrm{tot}}$ alongside the $(N')^{-\varepsilon}$ error; this vanishes as $N' \to \infty$ and preserves the exact Rankin interval bound $\lfloor(\eta^2\varepsilon)^{-1}\rfloor + 1$ and dyadic counting bound $C_\varepsilon \eta^{-2} N^\varepsilon$. Scaling $\tau_0 = (\eta^2\varepsilon)^2 / (1000(1+\eta^2\varepsilon))$ ensures the Rankin Cauchy–Schwarz contradiction holds unconditionally for all $\varepsilon \in (0, 1/4)$ and $\eta \in (0, 1/2]$.

### Section 7 (Support-Reduced Padé–Wronskian Method & Theorem 1.3(ii))
- **Classification**: Sound (zero mathematical flaws; all Table 1 and Table 2 exponents verified algebraically).
- **Details**:
  - Siegel's Lemma (`siegel_lemma_pigeonhole`), monomial-product Puiseux linear independence (`lem_7_2_monomial_product_puiseux_indep`), and Gauss leading-coefficient divisibility (`gauss_leading_coeff_dvd_of_linear_factors`) are proved completely from Mathlib without axioms.
  - Every exponent in Table 1 ($\theta_2(2-\sqrt{2}) = 17 - 12\sqrt{2} > 1/34$, $\theta_3(3-\sqrt{3}) = 7 - 4\sqrt{3} > 0.07179$, $\theta_4(2) = 1/9$, $\theta_5(5-\sqrt{5}) = (7 - 3\sqrt{5})/2 > 1/7$) and Table 2 ($\nu = 3, 4, 5, \ge 6, \ge 25$) is verified by exact arithmetic in `Thm1_3Part2Counting.lean`.

### Section 8 (Elliptic Curve Realizations and Effective Class Group Bounds)
- **Classification**: 2 surgical constant/base-conversion fixes (all qualitative conclusions and asymptotic rates preserved verbatim).
- **Details**:
  1. **Theorem 8.1(ii) $abc$-Quality Leading Constant** (`Thm8_1FreyCurves.lean`, manuscript lines 1121 & 1140):
     - *Issue*: In the proof of Theorem 8.1(ii), the original draft cited Theorem 4.2(i) for $\log\operatorname{rad}(2q_n Y_1(q_n)) \le (\log 2 + o(1))n$, which bounds $\log q_n$ but does not exclude primes in $\mathcal{P}_{\mathrm{even}}(n)$ dividing $Y_1(q_n)$ (since $2 q_n Y_1(q_n) \mid n!$, every prime dividing $A_n B_n C_n$ divides $n!$, giving $\log\operatorname{rad}(A_n B_n C_n) \le \vartheta(n) = (1 + o(1))n$).
     - *Fix*: Replace $\bigl(\frac{1}{4\log 2} - o(1)\bigr)\log n$ with the unconditionally verified $\bigl(\frac{1}{4} - o(1)\bigr)\log n \to \infty$ (preserving $q(A_n, B_n, C_n) = \Omega(\log n) \to \infty$).
  2. **Theorem 8.2 Narrow $2^J$-Rank Exponent Base Conversion** (`Thm8_2TatuzawaClassGroup.lean`, manuscript lines 1150 & 1154):
     - *Issue*: The proof correctly derives $\log_2 \exp(\mathcal{A}_2(q_n)) \ge \bigl(\frac{1}{4\log 2} - \varepsilon\bigr)\log n$. Exponentiating with base $2$ yields $2^{(\frac{1}{4\log 2} - \varepsilon)\log n} = e^{(\frac{1}{4} - \varepsilon\log 2)\log n} = n^{\frac{1}{4} - \varepsilon\log 2} \ge n^{\frac{1}{4} - \varepsilon}$, whereas the theorem statement omitted the $\log 2$ factor when converting from base $2$ to base $e$ and wrote $n^{\frac{1}{4\log 2} - \varepsilon}$.
     - *Fix*: Correct the exponent in the theorem statement to $\exp(\mathcal{A}_2(q_n)) \ge n^{\frac{1}{4} - \varepsilon}$ while explicitly retaining the exact base-2 bound $\log_2 \exp(\mathcal{A}_2(q_n)) \ge \bigl(\frac{1}{4\log 2} - \varepsilon\bigr)\log n$ in both the manuscript and `thm_8_2_tatuzawa_and_narrow_2J_rank`.
