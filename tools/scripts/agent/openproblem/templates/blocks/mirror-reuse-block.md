
## Reuse spot-check before the freeze (binding; review rounds reject these)
Before approving, check reuse for every helper `lemma` or `theorem` of the delivery, public and private, and for **every closed local `have`** (every local-fact row of the reuse table): run `exact?` or the candidate owner application on each, not a sample. A spot check of the longest helpers is not this check. A helper that reproves an available result blocks approval. Report each hit as a blocking finding with the exact owner application.
- **Same delivery.** A helper whose conclusion is a specialization of another declaration in the delivery, or one that reconstructs a formula an imported module already proves. Private visibility does not excuse it: the owner must be published and applied.
- **Pinned Mathlib.** Search by conclusion shape (`exact?` in scratch, `rg` in `.lake/packages/mathlib`), for small facts as much as large ones, for example `Nat.pow_self_pos`, `Finset.sum_comm`, `Real.sq_sqrt`.
- **Frozen D5 owners, private ones included.** `git grep -n -P '<conclusion shape>' origin/dev -- D5`.
  - For each hit in a frozen module, count that module's transitive D5 importers.
  - For more than 20 transitive importers, search for an equal public owner and report the importer count and any remaining publication constraint before editing the owner.
  - A `private` owner in an `I` module that a `G` consumer needs is extracted into a shared `G` module (CLAUDE.md §4.3), not imported directly (SL-010).
  - Search the general shape as well: a stronger owner (for example an analytic null-set theorem for a polynomial one) also dominates.

Report the number of helpers checked and the hits, each with its command.

- **Definitions too, by body.** For EVERY `def`, `abbrev` and `instance` of the delivery, public and private, search `origin/dev` `D5` (private included) and pinned Mathlib by its defining expression, with `git grep -n -P` on the body's head symbols (for example `decide \(.*\.val <` for a threshold vector), not by its name. Check each plausible hit with a scratch `example : mine = candidate := rfl` (or `funext` + `simp`). A definition equal to an owner blocks approval, unless it is a preregistered convention stated literally in `claim` with the owner used in the proofs. Include **generic** owners over typeclass carriers (`[LE R]`, `[Zero R]`, …) that specialize to the definition under the carrier's pinned instance (for example `IsEffect E := 0 ≤ E ∧ E ≤ 1` under `MatrixOrder` is `E.PosSemidef ∧ (1 - E).PosSemidef`). Report the number of definitions checked and the hits.

- **Touched owners carry no diagnostics.** Any frozen owner that the delivery edits (publication, move or re-pin) must leave the delivery with no `#print`, `#check` or `#eval` line, including lines that predate the edit. Take such readings in scratch files.

- **Report every defect in one round.** Finish the whole checklist, and list every blocking finding before returning. Never stop at the first one: each extra pre-freeze round costs a full seat cycle.

- **Applications are not reproofs.** A consumed helper whose whole proof is a direct application of an owner (for example a `@[simp]` normal-form lemma proved by `owner ..`) is a consumed bind-only helper (CLAUDE.md §3.2), not a duplicate. Flag only helpers that re-derive an owner's conclusion by their own argument, and require only that each kept helper is labelled `bind-only` with its consumers.

- **Canonical handles.** A Scribe `DeclarationHandle` and every utility GID is `<module GID>.<selector>` with no second dot. A nested Lean name (`Foo.bar`) cannot be a handle: make the declaration private if no public statement uses it, or give it a flat name. Never propose a nested selector as a fix.

- **Concrete data is not a duplicate.** A definition whose body is concrete data (a matrix, vector, polynomial or number given by explicit literal entries, such as a counterexample's witness state) does not duplicate a generic owner solely on the grounds that an owner applied to chosen constants reproduces it. Only a body that rebuilds a *construction* (an operation on its arguments, such as a product, a sum over an index, a reindexing or a sandwich `P * U * P`) can duplicate an owner. Do not report, and do not apply, an "owner" rewrite of literal witness data.

- **Pre-existing owner code is out of scope.** The sweep covers the declarations, imports and local facts that the delivery adds or changes. Edits to a frozen owner are limited to the required publication, move or re-pin and removal of diagnostic commands. Do not report, and do not apply, a reuse, import or style change to the owner's pre-existing code. Imports named by the owner's `anchors:` header stay in any case (SL-017).

- **A compiled inlined route is not by itself a bind-only verdict.** To call a declaration `bind-only` (CLAUDE.md §3.2), show that the conclusion of every inlined helper is itself obtained from frozen or pinned premises by instantiation, projection or normalization. A route that requires inlining a helper establishing a new proposition (an estimate by a positive/negative-part or other non-normalization argument, an explicit construction of a witness, an extension of an owner to a case it does not cover) leaves that helper, and every declaration whose live path uses it, `content`.
