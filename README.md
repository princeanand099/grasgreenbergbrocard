# GrasGreenbergBrocard — Lean 4 Formalization

Lean 4 formalization of the mathematical manuscript *Arithmetic Structure and Counting Bounds for the Brocard–Ramanujan Equation* (`brocard_arithmetic_structure_and_counting_bounds.tex`).

## Environment & Build Instructions
- **Lean Toolchain:** `leanprover/lean4:v4.35.0`
- **Mathlib Version:** `v4.35.0`
- **Build Command:**
  ```bash
  lake exe cache get
  lake build
  ```

## Module Organization (Section 2 Formalization)
- `GrasGreenbergBrocard/Basic.lean`: Core arithmetic definitions (`Podd`, `Peven`, `q_n`, `s_n`, `piPrime`, `thetaPrime`, `eExp`, `S_odd`, `S_even`, `Delta_parity`, `Sigma_star_parity`, `harmonicInterval`), `factorial_eq_q_mul_s_sq`, and `Delta_parity_eq_sum`.
- `GrasGreenbergBrocard/ExternalAxiomsAnalytic.lean`: Peer-reviewed external analytic axioms (de la Vallée Poussin PNT, Chebyshev, Mertens, Vaaler, Vaughan–van der Corput).
- `GrasGreenbergBrocard/ValuationParityLayer.lean`: Lemma 2.1 (harmonic layer stratification and asymptotics of `log q_n` and `|Podd(n)|`).
- `GrasGreenbergBrocard/ValuationParityDigits.lean`: Lemma 2.2 (exact Legendre base-`p` digit reduction below `√n`).
- `GrasGreenbergBrocard/ValuationParityVaaler.lean`: Lemma 2.3 (Vaaler's odd-harmonic trigonometric polynomial approximation `Ψ̃_H, B̃_H`).
- `GrasGreenbergBrocard/ExpSumBounds.lean`: Lemma 2.4 (collar decomposition and prime exponential sum bounds on `[n^δ, n / (log n)^12]`).
- `GrasGreenbergBrocard/ValuationParityThm.lean`: Theorem 2.5 (second-order discrepancy formula, 50–50 valuation-parity equidistribution, and multi-modulus power-band equidistribution).

## Protocol Records
- `THEOREM_CORRESPONDENCE.md`: Manuscript-to-Lean theorem correspondence record.
- `EXTERNAL_AXIOMS.md`: External-axiom register with published sources and justifications.
- `MATHEMATICAL_CORRECTIONS.md`: Mathematical correction and audit record.
- `PROGRESS.md`: Continuous formalization progress record.
