# Mathematical Correction and Audit Record

## Section 2 Audit

### 1. Lemma 2.3 (`vaaler_parity_approx`) — Integer-Point Bound
- **Affected Manuscript Result:** Lemma 2.3 (eq. 2.9), proof of $|(-1)^{\lfloor x \rfloor} - \widetilde{\Psi}_H(x)| \le \widetilde{B}_H(x)$ at integer points $x = m \in \mathbb{Z}$.
- **Original Proof:** States that at $x = m \in \mathbb{Z}$ (where $B_H(0) = \frac{1}{2}$ and $|\Psi_H(m)| = 0$), $\widetilde{B}_H(m) \ge 2(\frac{1}{2}) = 1 = |(-1)^m - \widetilde{\Psi}_H(m)|$.
- **Exact Defect:** When $m = 2k + 1$ is odd, $m/2 = k + 1/2 \notin \mathbb{Z}$, so $\Psi_{2H+1}(m/2)$ need not be $0$, and thus $\widetilde{\Psi}_H(m) = -4\Psi_{2H+1}(m/2)$ is not necessarily $0$.
- **Classification:** Missing justification (the inequality $|(-1)^m - \widetilde{\Psi}_H(m)| \le \widetilde{B}_H(m)$ remains true!).
- **Replacement Argument:** For $m = 2k$ even, $m/2 = k \in \mathbb{Z}$ so $\Psi_{2H+1}(m/2) = 0$ and $|(-1)^m - \widetilde{\Psi}_H(m)| = 1 = 2 B_H(m) \le 2 B_H(m) + 4 B_{2H+1}(m/2) = \widetilde{B}_H(m)$. For $m = 2k + 1$ odd, $\psi(m/2) = 0$, so $|\Psi_{2H+1}(m/2)| = |\psi(m/2) - \Psi_{2H+1}(m/2)| \le B_{2H+1}(m/2)$, giving $|(-1)^m - \widetilde{\Psi}_H(m)| = |-1 + 4\Psi_{2H+1}(m/2)| \le 1 + 4 B_{2H+1}(m/2) = 2 B_H(m) + 4 B_{2H+1}(m/2) = \widetilde{B}_H(m)$.
- **Hypotheses / Conclusion:** Unchanged.
- **Lean Declaration:** `GrasGreenbergBrocard.vaaler_parity_approx` in `GrasGreenbergBrocard/ValuationParityVaaler.lean`.
