# Formalization Progress Log

## Section 2: Valuation-Parity Distribution — COMPLETED (`main` CI `exit 0`)
- Formalized `Basic.lean`, `ExternalAxiomsAnalytic.lean`, `ValuationParityLayer.lean`, `ValuationParityDigits.lean`, `ValuationParityVaaler.lean`, `ExpSumBounds.lean`, `ValuationParityThmHelpers.lean`, `ValuationParityThmPart1.lean`, `ValuationParityThmCollar.lean`, `ValuationParityThmInterCollar.lean`, `ValuationParityThm.lean`, `ExpSumBoundsMod.lean`, `VaalerMod.lean`, `ValuationParityModWeight.lean`, `ValuationParityModCollar.lean`, `ValuationParityModInterCollar.lean`, `ValuationParityMod.lean`.
- Verified Lemma 2.1(i)–(ii), Proposition 2.2, Lemmas 2.3–2.4, and Theorem 2.5(i)–(iii).

## Section 3: Chebyshev–Lucas Absorption, Theorems 1.1–1.2, Proposition 3.3 — COMPLETED (`main` CI `exit 0`, commit `af7e5e05`)
- `ExternalAxiomsSec3.lean`: External analytic & Iwasawa-theoretic axioms.
- `PellFundamental.lean`: Lemma 3.1(i)–(ii).
- `ChebyshevLucas.lean`: Lemma 3.2 (eqs. 3.1–3.3).
- `Thm1_1Collapse.lean`: Theorem 1.1 (known $n = 4, 5, 7$, eq. 1.6 collapse, eq. 1.7 regulator quantization, distinctness of $q_n$).
- `Picard2Torsion.lean`: Proposition 3.3 (eq. 3.8 Picard 2-torsion dichotomy & second-stage non-principality).
- `Thm1_2Iwasawa.lean`: Theorem 1.2(i)–(iii) (eqs. 1.8, 3.6–3.7).
- Full `lake build` passed (`9071/9071` jobs, `exit 0`, 0 errors, 0 `sorry`s, 0 `admit`s).

## Section 4: Arithmetic Structure of the Critical Regime $k = 2$ — IN PROGRESS (`sec4` branch)
- Repaired Section 2 + Section 3 documentation (`README.md`, `EXTERNAL_AXIOMS.md`, `THEOREM_CORRESPONDENCE.md`, `MATHEMATICAL_CORRECTIONS.md`, `PROGRESS.md`).
- Formalizing `ExternalAxiomsSec4.lean`, `Prop4_1SmoothBiquad.lean` (Proposition 4.1, eqs. 4.1–4.6), and `Thm4_2QuarticCores.lean` (Theorem 4.2, eqs. 4.7–4.16).
