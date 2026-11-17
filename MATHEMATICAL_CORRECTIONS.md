# Mathematical Corrections and Clarifications Audit

This file documents all substantive mathematical clarifications, boundary refinements, and proof completions made while formalizing Section 2 of `brocard_arithmetic_structure_and_counting_bounds.tex`. All original Section 2 conclusions (Equations 2.1–2.18, Lemmas 2.1–2.4, Theorem 2.5(i)–(iii)) are preserved at full logical strength.

## 1. Explicit Separation of $p = 2$ in Small-Prime Band Estimates
- **Affected Results**: Theorem 2.5(ii) (`small_prime_parity_band_bound`, `Delta_parity_isLittleO_mul_log`) and Theorem 2.5(iii) (`multi_modulus_power_band_equidistribution`).
- **Original Proof**: Treats primes $p \in (n^\delta, \sqrt{n}]$ uniformly when applying $(p-1)\log p$ and bounding $s_p(n) = O(p \log_p n)$.
- **Defect / Classification**: *Missing justification* — for $p = 2$ (which can lie in $(n^\delta, \sqrt{n}]$ for bounded $n$ or small $\delta$), $p - 1 = 1 < 2$ and $\log 2$ requires separate handling in inequalities assuming $3 \le p$ or $2 \le p - 1$.
- **Replacement Argument**: Split the mid-range prime set $S_{\text{mid}}$ explicitly into $S_{\text{mid},2} = \{p \in S_{\text{mid}} \mid p = 2\}$ and $S_{\text{mid},3} = \{p \in S_{\text{mid}} \mid 3 \le p\}$. The single prime $p = 2$ contributes at most $n \log 2 = o(n \log n)$, while $p \ge 3$ satisfies $2 \le p - 1$.
- **Hypothesis / Conclusion Impact**: Hypotheses and conclusions unchanged.
- **Lean Declarations**: `small_prime_parity_band_bound` (`ValuationParityThm.lean`), `multi_modulus_power_band_equidistribution` (`ValuationParityMod.lean`).

## 2. Explicit Discontinuity Guard in Sawtooth / Vaaler Approximation
- **Affected Results**: Lemma 2.3 (`neg_one_pow_floor_eq_sawtooth`, `vaaler_parity_approx`) and multi-modulus extension (`floor_mod_eq_sawtooth`, `vaaler_mod_approx`).
- **Original Proof**: Writes $(-1)^{\lfloor x \rfloor}$ and $\mathbf{1}_{v \equiv c \pmod h}$ in terms of $\psi(x)$ without explicitly excluding integer jump points $x \in \mathbb{Z}$ in the pointwise identity.
- **Defect / Classification**: *Missing justification* — the exact identity $(-1)^{\lfloor x \rfloor} = 2\psi(x/2) - 2\psi((x-1)/2)$ holds away from integers $x \in \mathbb{Z}$, whereas for $x = n/p^r$ with $p \nmid n$ (or $p \ge 2$ when $n/p^r \notin \mathbb{Z}$), integrality only occurs when $p^r \mid n$, which is handled by the Vaaler upper/lower majorants directly.
- **Replacement Argument**: State `neg_one_pow_floor_eq_sawtooth` with explicit hypothesis `∀ m : ℤ, x ≠ (m : ℝ)`, and use the Vaaler majorant/minorant inequalities `h_vaaler_pw` directly at all real points $t = n / p^r$.
- **Hypothesis / Conclusion Impact**: Hypotheses and conclusions of Lemma 2.3 and Theorem 2.5 unchanged.
- **Lean Declarations**: `ValuationParityVaaler.lean`, `VaalerMod.lean`.

## 3. Explicit Collar / Inter-Collar Partition and Asymptotic Thresholds
- **Affected Results**: Lemma 2.4 (`prime_exp_sum_bounds`), Theorem 2.5(ii)–(iii).
- **Original Proof**: Splits $p \in (\sqrt{n}, n]$ into collar neighborhoods of $n/m$ and inter-collar intervals implicitly for large $n$.
- **Defect / Classification**: *Incomplete proof* — Lean requires explicit disjointness, measurability/finset partitioning, and explicit lower bounds (e.g., $n \ge 16$ so $\log n \ge 2$) when converting `=O[atTop]` and `=o[atTop]` bounds into concrete $\varepsilon$-$\delta$ inequalities.
- **Replacement Argument**: Formalized `collar`, `collarSubinterval`, and `interCollar` explicitly in `ExpSumBounds.lean`, proved disjointness and coverage, and proved `collar_band_isBigO`, `interCollar_band_isBigO`, `collar_mod_isBigO`, and `interCollar_mod_isBigO` in dedicated modules.
- **Hypothesis / Conclusion Impact**: Hypotheses and conclusions unchanged.
- **Lean Declarations**: `ExpSumBounds.lean`, `ValuationParityThmCollar.lean`, `ValuationParityThmInterCollar.lean`, `ValuationParityModCollar.lean`, `ValuationParityModInterCollar.lean`.
