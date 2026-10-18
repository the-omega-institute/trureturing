
## Definition fidelity before the door (binding; review seats reject this after freezing)
Every new public definition is the literal source expression.
- If the source defines acyclicity as "no directed cycle", the public predicate says that. It does not say "there is a strictly increasing rank".
- Likewise "is a sum of products" is not replaced by "has a certificate of the form …".
- An equivalent formulation that is easier to prove with stays `private`. Link it to the public definition by a private lemma that the proof actually uses.
- No additional public identity theorem.

Before the door, list each public definition next to the source sentence it mirrors, quoted verbatim. Report the list as `definition_fidelity` in your conclusion. A reused frozen definition is exempt only when the source's notion is literally that definition.

**Scribe shows each definition's body.** Every public definition's Scribe node displays its full right-hand side, symbol for symbol against the Lean source: recursion cases, quantifiers and every conjunct. A bare call such as `bwt(o, w)` or `propLongWord(d)` is not a mirror. A displayed formula names no `private` declaration: inline its expression, or make it public with its own node. Every formula renders under KaTeX; use the function-arrow token for function types, never an implication macro.

**Every helper is really consumed.** A helper counts as consumed only if deleting it breaks its named consumer. A name in a `simp` argument list that the proof does not need is not a use: drop the argument, and either delete the helper or make the consumer's proof genuinely use it. Before Stage A ends, check each helper by deleting it in a scratch copy and recompiling; report the result per helper.

**Provenance and visibility per node.** A Scribe node whose definition or statement quotes a published source uses `FromLiterature(<that source's note>)`; `FromRepo` is only for repository-derived nodes, so a shared node factory must take the provenance as an argument. A declaration that no public statement mentions and that only private proofs use is `private`, with no mirror node. Scribe prose states mathematics and provenance only: no retirement conditions, admission bases or audit status.

**Compiled bypass test for every claimed witness.** For each declaration you label `content`, and for each module's escape witness, write a scratch file that tries to prove its exact statement from frozen owners and pinned Mathlib by instantiation, projection, fold/product identities (`List.foldr_hom`, `Nat.ofDigits_eq_foldr`, `Finset.prod` and `Finset.sum` lemmas) and normalization only. If the bypass compiles, the declaration is `bind-only`, and a supporting module left without a surviving witness must be merged into a content module or the settling module. Report each attempt (file, exit code, the missing step).

**No diagnostics in delivered modules.** A ported probe keeps no `#print`, `#check`, `#eval`, `#reduce` or `#guard_msgs` command. Before Stage A ends, `rg -n '^#(print|check|eval|reduce)' <every delivered .lean>` must find nothing. Axiom readings belong in a scratch file.

**Owner publications get full Scribe nodes.** Each declaration whose `private` is removed at a frozen owner gets a `Describe` node in that owner's Scribe. The node carries its exact `DeclarationHandle` (for `X.add`, the handle is `X.add`, not `X`) and its complete statement or defining expression with every binder and hypothesis. It never displays only the declaration's name.
