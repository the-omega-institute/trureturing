
## Delivery shape for open-problem-resolution (pre-freeze judgement form)
CLAUDE.md §3.2 "有消费的辅助声明": a bind-only helper declaration, public or private, is allowed when another declaration of this delivery actually uses it on its live proof path. Report it with `proof_shape: bind-only` and name its consumer. A bind-only declaration with no consumer, existing only for an import, coverage, API convenience or a future user, is rejected. A consumed bind-only helper never supplies the module's escape witness or admission basis. The mirror and judgement-form seat compiles an upstream-only route (pinned Mathlib or frozen D5 lemmas with instantiation and normalisation) for each helper. If the route uses only instantiation, projection and normalization, the helper is bind-only: it must then have a live consumer and be labelled bind-only; it must never be labelled content.


**An open-problem-resolution module does not require an escape witness for admission.** Its admission basis is `open-problem-resolution`, which admits a bind-only settling proof (CLAUDE.md §3.2 condition (a)–(d)). So do not label a helper `content` or call it an escape witness to justify the module; reviewers reject every such overstatement. Classify each declaration with the inlining rule: inline the same-delivery helpers and stop at frozen owners and pinned Mathlib. Unfolding plus `field_simp`/`ring`/`simp`/`linarith`/`norm_num`, finite-sum distribution, character or parity rewriting, and divisibility bookkeeping are bind-only. Label `content` only for a step that builds a proposition none of these produces. Typical cases are a new construction, an estimate or an induction carrying a non-trivial invariant. An unverified classification remains explicitly unverified until checked.

Shape the delivery accordingly:
- the public surface is the source's definitions, `claim`, `result`, and only those helpers that `result` (or another delivered declaration) uses on its live proof path;
- do not inline a consumed helper just to avoid the bind-only label when inlining would raise compile cost (heartbeats per declaration, memory); keep it separate and label it truthfully;
- private **definitions** for implementation carriers are fine;
- a helper is labelled content only when it is a non-binding construction or estimate that no upstream-only route reproduces; its escape witness is named in the second comment block.

Before you return, try to prove each helper's statement in a scratch file that imports only pinned Mathlib and the frozen owners. If that succeeds, label it `bind-only` with its consumer, or delete it if nothing uses it.

**No type or notation aliases.** Write existing types directly, for example `Sites → Local`, `Matrix n n ℂ` or `Matrix (Fin 3) (Fin 3) ℂ`. A new `def`, `abbrev` or `local notation` that only renames an existing type is judged a duplicate of whatever frozen owner happens to define the same type, and is rejected. A new `def` is justified only when it introduces genuinely new structure from the source.

**Scribe names.** Formulas display the actual Lean objects. Use their real names (`Matrix`, `EuclideanSpace`, `conjTranspose`, `IsHermitian`), or the landed `Qualified(owner, name)` helper for a qualified name. Never use a display abbreviation such as `Op`, `Ket`, `adjoint`, `toMatrix`/`fromMatrix` or `emptyList`, even one explained in prose; mirror checks reject display aliases.

**Reuse before defining.** Before adding any public definition, search frozen D5 for the same object by its defining expression; include private declarations and equivalent constructions. Check pinned Mathlib and compile the correspondence.

## Source notation with no literal Lean counterpart
Some source definitions use notation that Lean cannot state literally, such as a scalar raised to an operator power (`(−1)^{N̂}`) or a function of an operator. For each one, check the preregistration issue for its recorded convention and use exactly that construction, citing the issue. If the issue records no convention, stop and report the notation; do not choose one yourself.

## Scribe namespace
Each new `.scribe.cs` declares exactly `namespace StrataLint.Scribe.Blueprint.<path>;`, where `<path>` is its directory under `Blueprint/` with `/` replaced by `.`. Copy the line from a sibling file in the same directory. `make gate` reports `blueprint-namespace` if it is missing or different.

## Scribe formulas use real Lean names
**Forbidden tokens in emitted formulas.** The mandatory token check rejects `==`, `!=`, `&&` and `||` in the emitted `.md`. Render Lean's Boolean operators by name: `BEq.beq a b` (the landed `App(Q("BEq", "beq"), a, b)`), `bne a b`, `Bool.and`, `Bool.or`. For example `w.splitBy (· == ·)` renders as `splitBy (fun a b ↦ BEq.beq a b) w`. Check with `rg -n -e '==|!=|&&|\|\|' <emitted .md>` before Stage A ends.
Every operation a Scribe formula displays is a bound variable, a public declaration of this delivery, or the actual Lean/Mathlib operation under its real name or notation. Never invent display aliases such as `getElemOption`, `andBool`, `headOption`, `OptionElim`, `NFAmk`, `PathCons` or `upd`, even with a prose definition. Render dotted constants (`List.head?`, `NFA.Path.cons`, `Option.elim`) with one private helper that uses `Operatorname` and `Dot`, and Bool and indexing operations with their Lean notation. Keep every formula small enough for KaTeX: show `let` bindings as named intermediate values rather than expanding them.
**No underscore names in rendered formulas.** Scribe formula identifiers are `[A-Za-z][A-Za-z0-9]*` (`FormulaIdentifier`), and there is no literal-underscore token, so a constant whose name contains `_` (for example `Nat.fast_choose`) cannot be rendered faithfully. Keep such constants out of the public definitions and statements that Scribe displays: use an underscore-free Mathlib operation with the same value (for example `Nat.descFactorial n 4 / 24` with `Nat.choose_eq_descFactorial_div_factorial`), or move the use into a private helper's proof.

## Certificate theorems are bind-only on their own
A theorem whose proof is only "instantiate upstream positivity facts (for example: the trace of a product of PSD matrices is nonnegative), then verify a certificate identity by `ring`/`norm_num`/`decide`" is **bind-only** under CLAUDE.md §3.2, whatever the size of the certificate. Keep it as a separate declaration only if a delivered declaration uses it on its live proof path (a consumed bind-only helper, labelled `bind-only` with its consumer). It cannot be the module's escape witness: in an `escape-witness` lane the content must come from another declaration on the live path, for example a spectral reduction from the literal object. Before labelling any certificate-based theorem content, try an upstream-only route (Mathlib and already-frozen modules only); if it compiles, the theorem is bind-only.

## Every module needs its own admission basis (CLAUDE.md §3.2)
Each module is first-frozen on its own, so each module must carry its own admission basis: an `escape-witness` theorem whose content lives in that module (a non-bind-only theorem on the live path), or the settling `result` under `open-problem-resolution`. A consumed bind-only helper never supplies its host module's basis. So:
- a module whose declarations are only definitions, or only consumed bind-only helpers, must not be delivered as a separate module: move its declarations into the content-bearing module that consumes them (respecting the import order), and delete the empty module with its Scribe;
- before you return, list every module with its admission basis and the named content theorem (or "settling result"); any module with none is merged as above.

## Per-declaration table in the PR body (binding; reviewers reject its absence)
The PR body has one row per delivered declaration (public and private, every lane module), with these columns:
- module;
- name;
- `proof_shape` (`content` or `bind-only`, by the inlining rule of CLAUDE.md §3.2);
- direct frozen dependencies;
- `escape_witness` (the declaration's own, or `none`);
- consumer(s);
- the module's `admission_basis`.

**Direct frozen dependencies.** List each frozen D5 declaration used on the declaration's live proof path, with every same-delivery helper inlined, as declaration `GID` + declaration `statement_id`, or write `none`.
- Generate the column by script from the elaborated proof terms (`Lean.Expr.getUsedConstants` on each declaration's value, followed through same-delivery helpers).
- Map the constants to their declaration `statement_id`s in the Lean report (`.lake/build/stratalint/raw-lean-report.json`) built at the merged dev base, keeping only constants of modules that have a state record `Golden/Frozen/state/<module>.lean.json`.
- Never use a module pin for a declaration identity.
- Pinned Mathlib declarations are not frozen dependencies. Name the decisive ones in the `proof_shape` reason instead.

The Lean comment block's labels agree with the table row by row.

**`mirror-E` header form (SL-004 Block in `current`).** The header line is never a bare `mirror-E: none`. Use `mirror-E: none(waiver:external-open-problem-resolution)` for a settling module, or `mirror-E: none(waiver:kernel-checked-refutation)` for a refutation module whose `utility:` is `kind=certified-instance; basis=refutes=…`. A supporting module uses `none(waiver:evidence-not-specified-by-formal-manifest)`. Check with `rg -n '^   mirror-E: ' <the lane's modules>` before mirror-ready.
