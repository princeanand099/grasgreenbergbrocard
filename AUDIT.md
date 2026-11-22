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
| Audited declarations in `AuditAxioms.lean` | **92** (all public theorems/lemmas across Sections 1–8) |
| External axiom files | **6** (`ExternalAxiomsAnalytic`, `Sec3`, `Sec4`, `Sec5`, `Sec7`, `Sec8`) |
| Total custom axioms | **28** (all soundness defects F1–F4, F7, F9 and fidelity defects D1–D6 resolved; 4 opaque/unproved interface axioms and Section 8 trace axioms eliminated) |

## Fidelity Remediation Log (D1–D6)

1. **D1 [Critical] — Section 7 De-Axiomatization**:
   - Eliminated `axiom canonicalMonomialTaylorFamily` by constructing `def canonicalMonomialTaylorFamily` concretely in `PowerSeries ℤ` (`Sec7TaylorSeries.lean`).
   - Eliminated `axiom canonicalSupportWronskian` by proving the rational power-series ODEs, Concrete Lemma 7.2 (`monomial_series_linear_indep_poly`), Wronskian non-vanishing (`weighted_wronskian_ne_zero`), and the concrete support-reduced differential Wronskian `def canonicalSupportWronskian` directly in `ℤ[X]` via `Matrix.adjugate_mul` and Gauss's Lemma (`Sec7PowerSeriesODE.lean`, `Sec7WronskianConcrete.lean`).
   - Only `bpz_cauchy_leibniz_pade_eval` (BPZ Prop. 3.4 / Lemmas 5.6, 6.3 analytic evaluation bound, scoped to the concrete definitions) remains in `ExternalAxiomsSec7.lean`.
2. **D2 [Critical] — Section 3 Mathlib Anchoring & $p$-adic Regulator**:
   - Eliminated `axiom padic_log_regulator_pell_power` by proving eq. (3.6) directly in `ℚ_[p]` (`PadicRegulator.lean`: `realQuadPadicRegVal_pell_power`).
   - Anchored `ExternalAxiomsSec3.lean` to Mathlib `NumberField` (`RealQuadField.lean`: `realQuadClassNumber`, `realQuadPadicRegVal`, `realQuadSplits`).
3. **D3 [Moderate] — Section 8 Frey Curves**:
   - Proved concrete Frobenius traces (`frobeniusTrace_freyCurveE`, `frobeniusTrace_freyCurveE2`) and $p=2$ minimality scaling (`freyE_p2_minimal_scaling`) directly in Mathlib with 0 external axioms (`Thm8_1FreyCurves.lean`).
   - Replaced the 2 opaque bundled record axioms in `ExternalAxiomsSec8.lean` with explicit elliptic-curve predicates (`IsModular`, `conductor`, `HasSurjectiveModLGalRep`) and named literature theorems (`bcdt_modularity_theorem`, `tate_algorithm_semistable_conductor`, `mazur_kenku_serre_surjectivity`).
4. **D4 [Moderate] — Section 5 Rédei Cohomology**:
   - Eliminated opaque `axiom canonicalRealQuadRedei` in `ExternalAxiomsSec5.lean`, defining `narrow4Rank` directly on Mathlib's `Cl4RankVec` (`RealQuadField.lean`) and proving eq. (5.8) in `Thm5_3RedeiCohomology.lean`.
5. **D5 [Moderate] — Proposition 3.3 Genuine Picard Group**:
   - Lifted Proposition 3.3 in `Picard2Torsion.lean` into genuine `ClassGroup (Zsqrtd (-q_n))` and `CommRing.Pic (Zsqrtd (-q_n))` via `ClassGroup.equivPic` (`J_n_pic_sq_eq_one`, `J_n_pic_eq_one_iff_k_eq_2`, `k_eq_1_picard_class_eq`).
6. **D6 [Minor] — Unconditional Theorem 1.1, Class Group Anchoring, & Audit/Docs Sync**:
   - Proved Pell existence/uniqueness (`exists_unique_fundamentalPell`, `exists_unique_pell_index`) in `PellFundamental.lean` and `thm_1_1_unconditional` in `Thm1_1Collapse.lean`.
   - Anchored `RealQuadClassGroupData` (`ExternalAxiomsSec8.lean`) to Mathlib `realQuadClassNumber`, `narrowTwoSylow`, and `narrowOddPart`.
   - Synced `GrasGreenbergBrocard.lean`, `AuditAxioms.lean` (92 declarations), `EXTERNAL_AXIOMS.md`, `THEOREM_CORRESPONDENCE.md`, and `AUDIT.md`.

## Prior Adversarial Audit Remediation Log (F1–F22)

1. **Tier 1 Soundness & Mathematical Correctness (F1–F4) — All Resolved**:
   - **F1**: Added `T₀ ≤ (n : ℝ) ^ 2` to `vaughan_van_der_corput_prime_sum` (`ExternalAxiomsAnalytic.lean`).
   - **F2**: Defined `padeP0Coeff` explicitly and enforced `hS_zero : 0 ∈ S ↔ ∃ v, padeP0Coeff ... P_coeff v ≠ 0`.
   - **F3 & F8**: Repaired Theorem 5.3(i) with `ramPrimes n` (including $p=2$), exact 2-adic Hilbert row `redeiRowTwo`, and proved `yMidVec_ne_zero` and `yMidVec_mem_redeiKernel`.
   - **F4**: Replaced the false $M^E x_0^{-\nu}$ bound with the true $(2N)^{M\nu/r} x_0^{-\nu}$ bound and fixed $(x_i/x_0)^r \to (x_0/x_i)^r$.
2. **Tier 2–5 Repairs (F7, F9–F14, F18–F22) — All Resolved**:
   - Added `Squarefree q` in Section 3, bound Section 8 to `WeierstrassCurve ℤ`, strengthened `thm_1_2_part3_complete_finiteness` and `thm_1_3_part2_global_6_7_general`, and verified 0 `sorryAx` and 0 `native_decide`.
