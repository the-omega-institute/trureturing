---
name: omega-math-migration
description: Port existing trureturing Lean formalizations to Omega mathematics, migrate their D5 callers, and check strict replay and correspondence with the default Mathlib publication.
---

# Strict Omega Math migration

Work in a linked worktree on a coherent group of existing declarations. Read `CLAUDE.md` §3.2 and the library guide before choosing where to put a proof. Read the frozen-state rules in spec A14 before changing a frozen declaration. [Library guide](../../src/README.md) · [Repository specification](../../docs/develop/spec/golden-ledger-repo-spec.md)

1. Fix a baseline commit. Read the old statements, hypotheses, types, definitions and consumers. Record the target declarations and their correspondence in the PR. Prefer a group whose prerequisites and callers can migrate together.
2. OmegaMath can publish theorems, proofs and references to verified objects. Freeze new project objects and observable legacy representations in D5. Reuse strict library declarations. Put a pinned Lean Init port under `strict/OmegaInit/`, a pinned Mathlib port under `strict/OmegaMathlib/`, and project mathematics in its D5 domain with a canonical freeze. Use `module` and `prelude`. A port follows the upstream declaration name and defining module. Run `python3 src/OmegaChecks/portable.py --regenerate-facades` to derive its official imports and aliases. Keep D5 identifiers, paths, GIDs, links and migration notes on the consumer side, including all prose and comments.
3. For a claimed Mathlib counterpart, name the pinned declaration. Commit a Lean correspondence proof in a mixed check or with an existing mixed consumer. Use pointwise equality for operations, iff for predicates, and inverses or explicit image hypotheses for carrier changes. Transport the original hypotheses and conclusion, including side conditions, when the statement changes. For an original construction, name the intended specification and prove the laws used by the consumer. Record the exact gaps and scope of each correspondence. [Mixed natural-number example](../../src/OmegaChecks/NatCorrespondence.lean)
4. Edit the original D5 owners to use the strict types and proofs. Update callers, Scribe and Reg where their Lean-facing interfaces change. Keep any compatibility adapters with their mixed consumers. Record partial ports and exact missing prerequisites in the PR.
5. Replay the strict library closure with `lake test -- <strict-modules>` and require zero axioms. Compile the affected D5 consumers on both backends and compare their exports with `python3 src/OmegaChecks/portable.py --backend both <consumer-modules>`. Take the scoped D5 report on the default official build. For frozen consumers, verify the official dependencies and the paired `strict_omega` measurement in the same declaration record. Use the canonical `ledger-align --selector` writer for changed frozen pins, then use `--refresh-annotations` with the same selector and report to record the dependency measurement. For an unchanged pin, apply the refresh directly. Build affected callers and run applicable repository checks.
6. Check the library source and its guide for D5 references. Report the exact audited scope, semantic comparison, frozen state changes and outstanding work in a focused PR to `dev`. Use PR checks at the published head as the integration result.

```sh
make lean LEAN_TARGETS="D5.Owner"
make lean-report-scoped LEAN_TARGETS="D5.Owner"
lake test -- OmegaMathlib
rg -n '\bD5\b' strict src/OmegaInit src/OmegaMathlib
```

The search should produce no matches. Record the Lean correspondence declarations and build targets alongside kernel replay and the scoped dependency report.
