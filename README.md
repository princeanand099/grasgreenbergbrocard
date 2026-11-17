# Gras–Greenberg–Brocard: Lean 4 Formalization (Section 2)

Lean 4 + Mathlib formalization of **Section 2 ("Valuation-Parity Equidistribution of Factorials")** of the manuscript *Brocard's Problem: Arithmetic Structure and Counting Bounds* (`brocard_arithmetic_structure_and_counting_bounds.tex`).

## Scope

This milestone completely formalizes **entire Section 2** (Equations 2.1–2.18, Lemmas 2.1–2.4, and Theorem 2.5(i)–(iii)) with **zero `sorry`**, **zero `admit`**, and **zero manuscript-owned axioms**. Sections 3–8 of the manuscript are outside the scope of this milestone.

## Environment & Build Instructions

- **Lean toolchain**: `leanprover/lean4:v4.35.0` (see `lean-toolchain`)
- **Dependencies**: `mathlib` (see `lakefile.toml` / `lake-manifest.json`)

To build the project locally:

```bash
lake exe cache get
lake build
```

## Module Organization (17 Modules)

1. `GrasGreenbergBrocard/Basic.lean` — Core definitions for $q_n$, $P_{\text{odd}}(n)$, $P_{\text{even}}(n)$, $S_{\text{odd}}(n)$, $S_{\text{even}}(n)$, and $\Delta_{\text{parity}}(n)$ (Equations 2.1–2.3).
2. `GrasGreenbergBrocard/ExternalAxiomsAnalytic.lean` — External analytic number theory axioms (PNT/de la Vallée Poussin, Chebyshev, Mertens, Vaaler, Vaughan–van der Corput).
3. `GrasGreenbergBrocard/ValuationParityLayer.lean` — Harmonic layer decomposition, alternating harmonic sum, and **Lemma 2.1(i)–(ii)** (`log_q_n_asymptotic`, `card_Podd_asymptotic`).
4. `GrasGreenbergBrocard/ValuationParityDigits.lean` — Base-$p$ digit sum identity and Legendre/Kummer parity formulas (**Lemma 2.2**).
5. `GrasGreenbergBrocard/ValuationParityVaaler.lean` — Vaaler trigonometric polynomial parity approximation (**Lemma 2.3**, `vaaler_parity_approx`).
6. `GrasGreenbergBrocard/ExpSumBounds.lean` — Collar/inter-collar regions and Vaughan–van der Corput exponential sum bounds (**Lemma 2.4(i)–(ii)**, `prime_exp_sum_bounds`).
7. `GrasGreenbergBrocard/ValuationParityThmHelpers.lean` — Helper lemmas for Vaaler Fourier series and band decompositions.
8. `GrasGreenbergBrocard/ValuationParityThmPart1.lean` — **Theorem 2.5(i)** (`Delta_parity_second_order`, Equation 2.15).
9. `GrasGreenbergBrocard/ValuationParityThmInterCollar.lean` — Inter-collar $O(n)$ band bound (`interCollar_band_isBigO`).
10. `GrasGreenbergBrocard/ValuationParityThmCollar.lean` — Collar $O(n)$ band bound (`collar_band_isBigO`).
11. `GrasGreenbergBrocard/ValuationParityThm.lean` — Small-prime band bound (`small_prime_parity_band_bound`, eq. 2.16) and **Theorem 2.5(ii)** (`S_odd_asymptotic`, `S_even_asymptotic`, eq. 2.17).
12. `GrasGreenbergBrocard/ExpSumBoundsMod.lean` — Multi-modulus Vaughan–van der Corput exponential sum bounds (`prime_exp_sum_bounds_mod`).
13. `GrasGreenbergBrocard/VaalerMod.lean` — Multi-modulus Vaaler indicator approximation (`vaaler_mod_approx`).
14. `GrasGreenbergBrocard/ValuationParityModWeight.lean` — Prime-band weight asymptotics (`prefix_weight_isBigO`, `band_total_weight_isBigO`).
15. `GrasGreenbergBrocard/ValuationParityModInterCollar.lean` — Multi-modulus inter-collar bound (`interCollar_mod_isBigO`).
16. `GrasGreenbergBrocard/ValuationParityModCollar.lean` — Multi-modulus collar bound (`collar_mod_isBigO`).
17. `GrasGreenbergBrocard/ValuationParityMod.lean` — **Theorem 2.5(iii)** (`multi_modulus_power_band_equidistribution`, Equation 2.18).

## Documentation & Audit Records

- [`THEOREM_CORRESPONDENCE.md`](THEOREM_CORRESPONDENCE.md) — Manuscript-to-Lean theorem correspondence for Section 2.
- [`EXTERNAL_AXIOMS.md`](EXTERNAL_AXIOMS.md) — Register of external analytic number theory axioms.
- [`MATHEMATICAL_CORRECTIONS.md`](MATHEMATICAL_CORRECTIONS.md) — Mathematical refinements and clarifications recorded during formalization.
- [`PROGRESS.md`](PROGRESS.md) — Build, CI, and verification log.
