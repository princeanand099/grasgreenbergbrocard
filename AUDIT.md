# Independent Verification and Audit Guide

This document describes how an independent referee or reader can reproduce the complete Lean 4 verification of *Arithmetic Structure and Counting Bounds for the Brocard–Ramanujan Equation* and audit its trust base from scratch.

## 1. Prerequisites

- [`elan`](https://github.com/leanprover/elan) (Lean version manager). The exact toolchain (`leanprover/lean4:v4.35.0`) is pinned in `lean-toolchain`, and all Mathlib/dependency revisions are pinned in `lake-manifest.json`.

## 2. Full Build and Kernel Axiom Audit

```bash
git clone https://github.com/princeanand099/grasgreenbergbrocard.git
cd grasgreenbergbrocard
lake exe cache get
lake build
lake build GrasGreenbergBrocard.AuditAxioms
```

A clean verification satisfies:
- `lake build` exits with status `0` across all `9,091` Lake targets.
- `lake build GrasGreenbergBrocard.AuditAxioms` prints the exact kernel axiom closure of all 42 main declarations across Sections 1–8.
- Zero occurrences of `sorryAx`, `Lean.ofReduceBool`, or `Lean.trustCompiler` appear in the output.

## 3. Optional External Kernel Re-Check (`leanchecker`)

To re-check the compiled `.olean` environment independently with Lean's external kernel verifier:

```bash
lake env leanchecker GrasGreenbergBrocard
```

## 4. Source-Level Anti-Cheating Checks

Run the following shell checks on `GrasGreenbergBrocard/` to verify absence of proof placeholders, compiler bypasses, and stray axiom declarations:

```bash
# 1. Zero sorry / admit placeholders
grep -rnE '\b(sorry|admit)\b' GrasGreenbergBrocard/

# 2. Zero native_decide / unsafe / implemented_by / partial / opaque escape hatches
grep -rnE '\b(native_decide|unsafe|implemented_by|extern|partial|opaque)\b' GrasGreenbergBrocard/

# 3. Every axiom declaration is strictly isolated inside ExternalAxioms*.lean
grep -rn '^axiom ' GrasGreenbergBrocard/
```

Expected results:
- Commands 1 and 2 return no matches (excluding comments/docstrings in `AuditAxioms.lean`).
- Command 3 returns declarations exclusively inside `ExternalAxiomsAnalytic.lean`, `ExternalAxiomsSec3.lean`, `ExternalAxiomsSec5.lean`, `ExternalAxiomsSec7.lean`, and `ExternalAxiomsSec8.lean`, matching [`EXTERNAL_AXIOMS.md`](EXTERNAL_AXIOMS.md).

## 5. Continuous Integration Verification Record

- **Latest Verified Full CI Run**: [GitHub Actions Run #44567866016](https://github.com/princeanand099/grasgreenbergbrocard/actions/runs/44567866016/job/135714460223) (`9,091/9,091` targets, `exit 0`).
- **Verbatim `#print axioms` CI Log**: [`ci-logs` commit `56e1d6d4`](https://github.com/princeanand099/grasgreenbergbrocard/commit/56e1d6d4bca09efcde64400ed0b5fb3fe1c5e309).
- **Adversarial Audit Hardening**: [PR #7](https://github.com/princeanand099/grasgreenbergbrocard/pull/7) (`d22839cc`) and [PR #8](https://github.com/princeanand099/grasgreenbergbrocard/pull/8) (`0def862b`).
