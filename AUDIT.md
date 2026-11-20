# Formal Verification Audit Report

- **Repository**: `princeanand099/grasgreenbergbrocard`
- **Manuscript**: Prince Anand, *Arithmetic Structure and Counting Bounds for the Brocard–Ramanujan Equation* ([DOI: 10.5281/zenodo.24278751](https://doi.org/10.5281/zenodo.24278751))
- **Toolchain**: Lean `v4.35.0` / Mathlib `v4.35.0`
- **Audit Entry Point**: `lake build GrasGreenbergBrocard.AuditAxioms`

## Verification Summary

| Check | Status |
| :--- | :--- |
| `sorry` / `admit` across all `.lean` files | **0** |
| `native_decide` / `Lean.ofReduceBool` / `Lean.trustCompiler` | **0** |
| Audited declarations in `AuditAxioms.lean` | **63** (complete coverage of Sections 1–8) |
| External axiom files | **6** (`ExternalAxiomsAnalytic`, `Sec3`, `Sec4`, `Sec5`, `Sec7`, `Sec8`) |
| Total external axioms | **28** (all strictly external peer-reviewed theorems; **0** unused, **0** circular) |
| Full GitHub Actions CI (`lake build` + `AuditAxioms`) | **PASS (`exit 0`, fail-fast enforced on build errors)** |

## Summary of 4-Tier Adversarial Audit Repairs & Polish

1. **Tier 1 (Analytic Quantifier Soundness)**: Promoted `c₁ c₂ : ℕ → ℝ` before `∃ η' η C` in `vaughan_van_der_corput_prime_sum` (`ExternalAxiomsAnalytic.lean`) and passed the explicit `c₁_low, c₂_high` bounds proved in `ExpSumBounds.lean` and `ExpSumBoundsMod.lean`.
2. **Tier 2 (Structural & Statement Fidelity)**:
   - Removed dead `nth_prime_asymptotic` in `ExternalAxiomsSec4.lean` and audited `thm_4_2_part3_mertens_bound`.
   - Derived `chebyshevU_eval` internally inside `pell_index_collapse_large` (`Thm1_1Collapse.lean`) via `pellUnit_pow_eq_lucas` and `irrational_sqrt_natCast_iff`.
   - Constructed concrete `yMidVec n X₁` from `coreNat (X₁ + 1)` and scoped `redei_reichardt_exact_sequence` to `canonicalRealQuadRedei n` (`ExternalAxiomsSec5.lean`, `Thm5_3RedeiCohomology.lean`).
   - Added `conductor_F2_eq` and required `IsFundamentalPell` + `hk2` for `frey_F2_modularity_and_galois` (`ExternalAxiomsSec8.lean`, `Thm8_1FreyCurves.lean`).
   - Expanded `AuditAxioms.lean` to cover every theorem in Sections 1–8.
3. **Tier 3 (Theorem 1.2 eq. (3.6) & Finite Verification)**:
   - Proved `thm_1_2_eq_3_6_regulator_valuation` ($v_p(\tilde{R}_p(K_n)) = \lfloor v_p(n!)/2 \rfloor$) directly from `Nat.factorial n + 1 = m ^ 2`, `p ∤ k`, `brocard_p_not_dvd_m`, `padicValNat_odd_series_strict_dom`, and `padic_log_regulator_pell_power` (`ExternalAxiomsSec3.lean`).
   - Removed `h_reg` from all three parts of Theorem 1.2 (`Thm1_2Iwasawa.lean`).
   - Added pure kernel-verified `brocard_small_solutions_lt_116` (112 modular non-residue witnesses, zero `native_decide`) and `thm_1_2_part3_complete_finiteness`.
4. **Tier 4 (Elimination of Section 7 Circularity & Canonical Scoping)**:
   - Deleted circular `bpz_dyadic_cluster_elimination` and unparameterized `siegel_bpz_support_wronskian` from `ExternalAxiomsSec7.lean`.
   - Kept only three tightly scoped, parameterized external axioms (`canonicalMonomialTaylorFamily`, `canonicalSupportWronskian`, `bpz_cauchy_leibniz_pade_eval`), canonically scoped to prevent adversarial dummy `AlgebraicTaylorFamily` (such as a linearly dependent zero family) or dummy `SupportWronskianData` instances.
   - Proved `pigeonhole_cluster_reduction` (eq. 7.17), `short_interval_pigeonhole` (`Sec7ClusterReduction.lean`), `depressed_poly_asymptotic_core`, `pade_chi_lt_ratio_iff_theta_lt` (`Sec7PadeWronskian.lean`), and `dyadic_cluster_elimination_proved` (`Thm1_3Part2Counting.lean`), genuinely wiring `lem_7_1`–`lem_7_4` into all Theorem 1.3(ii) bounds.
5. **Minor Polish & CI Hardening**:
   - Completed Lemma 3.1(i) on the finite range $8 \le n < 116$ (`log_q_n_gt_point4_ge8`, `log_fund_pell_gt_point2_ge8`, `pell_index_upper_bound_ge8` in `PellFundamental.lean`) with pure kernel `decide` (zero `native_decide`).
   - Added `prop_4_1_part1_asymptotic` (`Prop4_1SmoothBiquad.lean`) establishing the asymptotic eq. (4.4) bounds $(\log 2 + o(1))n$ and $(1 - \log 2 + o(1))n$.
   - Hardened `.github/workflows/lean_action_ci.yml` so exit codes are always captured before log publication and any `lake build` failure fails the CI job visibly.
   - Reconciled `THEOREM_CORRESPONDENCE.md`, `EXTERNAL_AXIOMS.md`, `AUDIT.md`, `PROGRESS.md`, `README.md`, and `formalization.yaml` line-for-line with the exact Lean kernel `#print axioms` output across all 63 audited declarations.
