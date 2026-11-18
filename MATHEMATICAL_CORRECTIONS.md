# Mathematical Corrections and Audit Record

## Summary
Across Sections 2, 3, 4, and 5, all formalized statements and proofs in `GrasGreenbergBrocard/` match the mathematical content of `brocard_arithmetic_structure_and_counting_bounds.tex` with **zero** fatal mathematical flaws and **zero** silent weakenings.

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
