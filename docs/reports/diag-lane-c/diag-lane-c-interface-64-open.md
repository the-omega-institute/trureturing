# Diagonal Lane C: Interface 6.4 Open Report

Outcome: open, with no formalization deposit.

This is the third independent diagonal lane after the previous interface 2.4
duplicate and PZG 27.161 reports. The lane is
`harness/diag-lane-c` at `/Users/mstudio3/trureturing-diag-lane-c`.
`origin/dev` was fetched at `de32d6e060922d2d282c252cc90079f2901d8eca` and
merged with `git merge --no-edit origin/dev`; `git merge-base --is-ancestor
origin/dev HEAD` exited `0`. The worktree was clean before this report. No
files under `Meta/Digestion/**`, `Golden/Frozen/**`, or formalization receipts
were edited.

## Atom and authoritative statement

- Atom ID: `pzg-residual-c4dd0c241dbf2b9cb4e59dd55a1419404192fab2b6089fb1d3ee6ea020117a9a`
- CAS reference: `sha256:c4dd0c241dbf2b9cb4e59dd55a1419404192fab2b6089fb1d3ee6ea020117a9a`
- Source: `docs/develop/theory/INTERFACE_PAPER.md`, `theorem/6.4`
- `make show-atom ATOM_ID=pzg-residual-c4dd0c241dbf2b9cb4e59dd55a1419404192fab2b6089fb1d3ee6ea020117a9a` exited `0`.
- `show-atom` reported `status=match` for raw, normalized, and CAS SHA-256 values.

The authoritative text copied from `show-atom` is:

> **定理 6.4(新恰式两枚)。**
> $$ J(1/2) = \frac{5 - 12 \ln 2}{6}, \qquad J(-1/2) = \frac{1 - 2\ln 2}{2}, \tag{6.2} $$
> 并满足仿射关系 J(1/2) = (5/6)J(0) + (1/3)J(1),J(−1/2) = J(0)/2。
>
> *证明。* p = −1/2:2M = 2s²/(1+s),括号 = (1+s)/(2s²) − 1/s² = (s−1)/(2s²),恰为 p = 0 情形括号之半,故 J(−1/2) = J(0)/2(符号复核比值 ≡ 1/2)。p = 1/2:2M = (1+s)/2;经 Weierstrass 代换 t = 2u/(1+u²)、s = (1−u²)/(1+u²) 被积化为 u 之有理函数,符号积分得 J(1/2) = 5/6 − 2 ln 2(零差)。∎(机制:两参数处 M_p 为 s-圆锥之有理函数,故必初等且常数属 {1, ln 2} 类。)

## Clause echo and exact frozen coverage

The source clauses map one-to-one to declarations already frozen in the
repository:

1. `J(-1/2) = (1 - 2 log 2) / 2` is the combination of
   `D5.S3.Constants.MidslopeCurvatureValues.J_neg_half_eq_half_J_zero`,
   `J_zero_eq_one_sub_two_log_two`, and the definition of `J_neg_half`.
2. `J(1/2) = (5 - 12 log 2) / 6` is exactly
   `D5.S3.Constants.MidslopeCurvatureValues.J_half_eq`.
3. `J(1/2) = (5/6) J(0) + (1/3) J(1)` is exactly
   `D5.S3.Constants.MidslopeCurvatureValues.J_half_eq_affine`.
4. `J(-1/2) = J(0) / 2` is exactly
   `D5.S3.Constants.MidslopeCurvatureValues.J_neg_half_eq_half_J_zero`.
5. The source's mechanism clause is supported by the existing definitions and
   integral proofs in `D5/S3/Constants/MidslopeCurvature.lean` and
   `MidslopeCurvatureValues.lean`; no new analytic vocabulary is required.

The exact declarations are not merely similar numerical examples. They use
the same interval-integral definitions, the same arithmetic/geometric/
half-power mean specializations, and the same constants `J_zero`, `J_one`, and
`J_half`. Thus a new theorem or a curried wrapper would be a renamed duplicate.
The target modules are frozen, so adding a declaration to either module is
also prohibited by the frozen-ledger constraint.

## Library and receipt search trace

The following searches were run after the base synchronization:

```text
rg -n -i "\\bJ\\(|harmonic mean|M₀|M₁|ln 2|log 2|new.*closed|exact.*value" \
  D5 Blueprint --glob '*.lean' --glob '*.md' --glob '*.scribe.cs'
```

This found the exact declarations above and their Blueprint mirrors, including
the full integral proofs. Frozen records were then checked with:

```text
rg -n -i "MidslopeCurvatureValues|J_half_eq|J_neg_half_eq_half_J_zero|J_one_eq_neg_log_two" \
  Golden/Frozen/accepted Meta/Digestion/formalizations
```

The accepted frozen records are:

- `Golden/Frozen/accepted/963e27f8...json` for
  `D5/S3/Constants/MidslopeCurvature.lean`, including
  `J_neg_one_eq_zero` and `J_one_eq_neg_log_two`.
- `Golden/Frozen/accepted/5954ddd4...json` for
  `D5/S3/Constants/MidslopeCurvatureValues.lean`, including
  `J_half_eq`, `J_half_eq_affine`, `J_neg_half_eq_half_J_zero`, and
  `J_zero_eq_one_sub_two_log_two`.

The selected atom has no formalization receipt of its own, and the exact atom
ID does not occur in existing receipts or reports. This is an unbound residual
whose mathematical content is already covered by frozen declarations, not a
missing proof.

## Failed approaches and diagnostics

- **Write a new module with the four displayed equalities:** rejected as a
  duplicate. Each equality is already named and frozen, and the mechanism
  clause is already represented by the existing integral definitions/proofs.
- **Add a wrapper theorem to `MidslopeCurvatureValues`:** rejected because
  that module is frozen; the wrapper would also add no independently
  addressable content.
- **Reprove the integrals in a new namespace:** rejected by the library-before-
  proof rule and the duplicate trap. It would create a second source of truth
  for exactly the same integral identities.
- **`make dotnet`:** exited `0`, with zero warnings and zero errors.
- **`lake build D5.S3.Constants.MidslopeCurvature`:** exited `0` (`2685 jobs`).
- **`lake build D5.S3.Constants.MidslopeCurvatureValues`:** exited `0`
  (`2686 jobs`).
- `make deposit`, `make preflight`, `make cover`, `make emit`, and full
  `make lean` were not run. The workflow requires stopping before deposit when
  the exact residue is already covered by frozen machinery; these are
  unreached classes, not claimed successes or failures.

## Fidelity gate and lane state

- **Conclusion substance:** supplied by the existing named integral theorems;
  no new conclusion is introduced.
- **Hypothesis satisfiability/domain inhabitance:** already witnessed by the
  compiled definitions and integral proofs in the frozen modules.
- **Proof substance:** independently nontrivial; the values are derived by
  interval-integral transformations and the Weierstrass substitution, not by
  definitions equated to their conclusions.
- **Deposit substance:** blocked for a new module because the exact source
  clauses are already earned and frozen by the existing modules.
- **Duplicate search:** complete; commands and frozen records are listed above.
- **Clause fidelity:** complete for the bind decision; all four equations and
  the mechanism clause map without weakening to the named frozen declarations.
- **Rendered-statement fidelity:** existing Blueprint mirrors were inspected;
  no new Scribe artifact was created.
- **Grader traps:** no witness/general or conditional/unconditional weakening
  occurs. A new wrapper would trigger the stronger-variant/renamed-duplicate
  trap and would violate the frozen-module declaration boundary.

`make deposit`, ledger rebinding, and coverage alignment are dispatcher-owned
and were not run. The selected residual remains untouched in its ledger shard.
The only intended worktree change is this evidence-complete report.
