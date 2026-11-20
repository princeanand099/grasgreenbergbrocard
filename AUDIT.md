# Formal Verification Audit Report

- **Repository**: `princeanand099/grasgreenbergbrocard`
- **Manuscript**: Prince Anand, *Arithmetic Structure and Counting Bounds for the Brocard–Ramanujan Equation* ([DOI: 10.5281/zenodo.24278751](https://doi.org/10.5281/zenodo.24278751))
- **Toolchain**: Lean `v4.35.0` / Mathlib `v4.35.0`
- **Audit Entry Point**: `lake build GrasGreenbergBrocard.AuditAxioms`

## Verification Summary

| Check | Status |
| :--- | :--- |
| `sorry` / `admit` / `opaque` / `unsafe` across all `.lean` files | **0** |
| `native_decide` / `Lean.ofReduceBool` / `Lean.trustCompiler` | **0** |
| Audited declarations in `AuditAxioms.lean` | **78** (all public theorems/lemmas across Sections 1–8) |
| External axiom files | **6** (`ExternalAxiomsAnalytic`, `Sec3`, `Sec4`, `Sec5`, `Sec7`, `Sec8`) |
| Total custom axioms | **28** (all soundness defects F1–F4, F7, F9 resolved; opaque/analytic scope boundaries documented honestly in `EXTERNAL_AXIOMS.md`) |

## Comprehensive Adversarial Audit Remediation Log (F1–F22)

1. **Tier 1 Soundness & Mathematical Correctness (F1–F4) — All Resolved**:
   - **F1**: Added `T₀ ≤ (n : ℝ) ^ 2` to `vaughan_van_der_corput_prime_sum` (`ExternalAxiomsAnalytic.lean`), closing the unbounded-$T_0$ inconsistency, and discharged it at every call site in `ExpSumBounds.lean`, `ExpSumBoundsMod.lean`, and `Lem6_3ParityFlipOsc.lean`.
   - **F2**: Defined `padeP0Coeff` explicitly in `ExternalAxiomsSec7.lean`, enforced `hS_zero : 0 ∈ S ↔ ∃ v, padeP0Coeff ... P_coeff v ≠ 0` in `canonicalSupportWronskian` and `bpz_cauchy_leibniz_pade_eval`, and constructed `S` in `Thm1_3Part2Counting.lean` by filtering `0` on `P₀ ≠ 0`.
   - **F3 & F8**: Repaired Theorem 5.3(i) in both the manuscript and Lean (`ExternalAxiomsSec5.lean`, `Thm5_3RedeiCohomology.lean`): augmented the ramified prime set to `ramPrimes n` (including `p = 2` whenever `2 ∣ D_n`), replaced the false `c₂(y) ≡ 1 (mod 8)` condition with the exact linear 2-adic Hilbert row `redeiRowTwo`, defined `yMidVec` from `coreNat (2 * (X₁ + 1))`, and **proved** `yMidVec_ne_zero` and `yMidVec_mem_redeiKernel` directly from the Pell equation (eliminating the unproved `hyMid_mem` and `hyMid_ne` hypotheses).
   - **F4**: Replaced the false $M^E x_0^{-\nu}$ bound with the true $(2N)^{M\nu/r} x_0^{-\nu}$ bound (and fixed the inverted $(x_i/x_0)^r \to (x_0/x_i)^r$ ratio) in manuscript eq. (7.16), `ExternalAxiomsSec7.lean` (`PadeEvaluationData.rho_le`), `Sec7PadeWronskian.lean` (`lem_7_4_denominator_clearing`), and `Thm1_3Part2Counting.lean` (`dyadic_cluster_elimination_proved`).
2. **Tier 2 & Tier 3 Repairs (F7, F9, F10–F12) — Resolved; Transparent Scope Boundaries (F5, F6)**:
   - **F7**: Added `Squarefree q` to `padic_log_regulator_pell_power` and `leopoldt_coates_valuation_law` (`ExternalAxiomsSec3.lean`) and discharged via `q_n_squarefree n` (`Thm1_2Iwasawa.lean`).
   - **F9**: Bound `FreyCurveArithmeticData` to Mathlib's `WeierstrassCurve ℤ` (`freyCurveE m`, `freyCurveF2 X₁`), verified `.c₄` and `.Δ` directly in `Thm8_1FreyCurves.lean`, and removed the vacuous unconstrained `Prop` fields (`isModular_E`, `isModular_F2`, `surj_mod_ell_F2`).
   - **F10–F12**: Weakened the unproved `= O(n)` in manuscript eq. (5.4) to `= o(n \log n)`, noted $d_n \in \{1, 3\}$ is odd in the proof of Theorem 5.3(i), and stated the $\nu \ge 25$ threshold explicitly in Table 2.
   - **F5–F6 (Honest Scope Boundary)**: Full Mathlib formalization of Puiseux series expansions of $\Omega_{\mathbf{e}}(x)$, differential Wronskian construction $\Delta_S(x)$, and Cauchy–Leibniz derivative estimates for general $(d, E, \nu)$ remains an open formalization frontier and is honestly documented as packaged in the 3 canonically scoped Section 7 axioms.
3. **Tier 4 & Tier 5 Repairs (F13, F14, F18, F19–F22)**:
   - **F13 & F18**: Strengthened `thm_1_2_part3_complete_finiteness` to assume a **single** prime `∃ p` (matching manuscript Theorem 1.2(iii)(a)) and added branches (b) and (c); added pure kernel-verified `thm_1_2_wieferich_congruence`.
   - **F14**: Proved `poly_has_depressed_gap_two` (eq. 7.1) for arbitrary `P : ℤ[X]` of degree `≥ 2`, generalized the global $N^{6/7+\varepsilon}$ bound to any `s_mult : ℤ` with `s_mult ≠ 0` (`thm_1_3_part2_global_6_7_general`), and added Table 1 counting bounds for $m = 2, 3, 4$ (`thm_1_3_part2_table1_bounds`).
   - **F19–F22**: Expanded `AuditAxioms.lean` from 63 to 78 declarations (adding all 9 omitted public theorems plus 6 new theorems), fixed all stale manuscript numbering in `THEOREM_CORRESPONDENCE.md`, fixed Davenport Ch. 19 and Mazur/Kenku/Serre citations in `EXTERNAL_AXIOMS.md`, and removed all overclaims.
