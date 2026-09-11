# RewThree admission and mirror evidence

This is evidence for the retained first-order rewriting API and its Scribe
selectors. It adds no mathematical declaration, escape witness, atom coverage,
ZFC conservativity result, model-existence result, or complete CSA construction.

The inspected input HEAD is `61900643d4451a784e4e1801baeca5c38d06b6ba`.
The enclosing Git commit binds this evidence and the corrected Scribe source;
the immutable PR link supplies the delivery HEAD without a self-referential
commit hash inside the file. The canonical raw Lean report SHA-256 is
`3872f6538b16ed92226d98c1199c46cb2d91aa5104b0bb95467a034292eb287b`.
Its two source bindings are:

| Module | Source SHA-256 |
| --- | --- |
| `D5.S3.ConceptDynamics.ZfcTermRewriting.RewThree` | `5b780be1e2900eca589caa86bf19ba20debb1253f048d784c08c96c114fd6fe9` |
| `D5.S3.ConceptDynamics.ZfcTermRewriting.RewThreeCompat` | `0c1f9951f83b9aa86d0c521c97558ca008b315c0a8f29ec1d804b33f88ca20bf` |

## Per-declaration assessment

[declaration-shapes.md](declaration-shapes.md) lists all 40 authored source
commands with exact local and upstream line ranges.
[declaration-audit.json](declaration-audit.json) contains all 94 public
kernel-report records: 84 from RewThree and 10 from Compat. Every record has
`proof_shape`, direct frozen dependencies with module GID and module/declaration
`statement_id`, `escape_witness`, `admission_basis`, and concrete API purpose.
All 34 theorem records have captured kernel dependency evidence. The two
captured edge files are [RewThree](proof-edges-rewthree.json) and
[Compat](proof-edges-compat.json).

Authored theorem assessments are `proof_shape: bind-only` and
`admission_basis: rule-11-upstream-wrapper`. Definitions, classes and syntax
commands are identified as such, not counted as content theorems. Every row
records `escape_witness: none`: retained upstream proofs, forwarding selectors,
class projections and compiler companions receive no new escape credit. This
follows the source-retention basis recorded in
`Library/ConceptDynamics/foundation2026firstorder.md`; it does not claim that an
upstream induction proof was authored as new content in this repository.

The exact Rule-11 upstream source is
[Foundation/Syntax/Predicate/Rew.lean at 30a16ffa](https://github.com/FormalizedFormalLogic/Foundation/blob/30a16ffa93d79d73ab4d02427fa00f50e039bf29/Foundation/Syntax/Predicate/Rew.lean).
The complete original file SHA-256 is
`8df8681a12ebf5ef8700d9710c88fc39bfc35df47ef387e2893df3caf3b69873`.
Each authored JSON row names its exact upstream declaration. The original
capacity span 638-953 contains selected command excerpts; it is not a claim
that the entire span was copied.

The current API/coverage requirement is the addressable rewriting interface:
term support and language-map laws, the dependent `toEmpty` conversion, indexed
formula rewriting and its quantifier lift, formula substitution/shift/free,
and the lawful rewriting classes. The actual document consumer is
`Blueprint/D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree.scribe.cs`, whose 26
Describe entries use these declarations or the nine explicit Compat selectors.
The JSON records each operation's concrete purpose. No `Meta/Digestion`
coverage edge for RewThree was found by the recorded query. This report does
not infer a live downstream mathematical consumer or indispensability for
every historical source command merely from its inclusion or documentation.

## Direct frozen prerequisite identities

The four direct imports of RewThree are the four prerequisite nodes recorded
in its accepted Freeze event
`e270d8418042f0f91072c2cfa1152d86bbcc879b98c633ba7a2613e07b2d53a4`.
They are read as existing ledger facts; no event or state fragment was edited.

| Direct imported GID | Module statement_id | Accepted prerequisite node |
| --- | --- | --- |
| `D5/S3/ConceptDynamics/ZfcPredicate/Term` | `sha256:7f065f3ed5bcc99287a955e54e96d33a1face52845baf0ecfd5859153ed9907c` | `097514630677c3d2f2a5f0316dc110efc9400bcc8ee02419e9b2ecadffff38df` |
| `D5/S3/ConceptDynamics/ZfcPredicate/Quantifier` | `sha256:9d8e54a9610f83fba0cfb38fa3ddfdf9f4a84aa3a146c400070e209e989650e7` | `2051c8de39c88b531fa2aae51b9657f8b96279375c684dae3697fa45d7a20acb` |
| `D5/S3/ConceptDynamics/ZfcSupport/Function` | `sha256:1d760c225a226c7296c0d54f4d4539c6f35c5109a48683ddbaf422b19d30a1f1` | `55bbcbb2773464cfafe900fb3802d5ada2886dc409217af7dab8e15d6ffa7fde` |
| `D5/S3/ConceptDynamics/ZfcTermRewriting/RewTwo` | `sha256:dc2255a003ca5bfd6e68302a108db2b1ab2bccbf1a06801eead01148d051f492` | `c3e203c2ecac05cfb4234f0780a479650b450e73f3d1321d1ba6516df335a0a0` |

This import table is not substituted for proof dependencies. The JSON's
per-declaration edges come from `Expr.getUsedConstants` on value and type with
auxiliary expansion, so they also name directly used constants whose owner is
reached through a transitive import. Pinned Mathlib constants are not mislabeled
as frozen repository prerequisites.

The formula law at RewThree lines 234-235 directly uses
`LO.FirstOrder.Rew.subst_mbar_zero_comp_shift_eq_free`, owned by RewTwo, with
declaration `statement_id`
`sha256:5ed74e5c8d05802c23336020e979feca394e69c22b4a7925f31e8419c1eb7630`.
Compat directly imports frozen RewThree, whose module `statement_id` is
`sha256:bf5cbe594ecb8f58bd3db7db4ecf5c5f8e2cccd0d56af5d865d7b9173fa4bc77`;
each forwarding theorem's exact source declaration identity is listed in JSON.
Compat itself has no frozen-state fragment in this tree, and this report does
not call it frozen.

## Search and worker capability receipts

[search-receipts.json](search-receipts.json) stores exact commands, stdout,
stderr and exit codes. These are a current-HEAD re-query in the required order,
not a reconstructed record of the original pre-implementation search.

| Stage | Command/capability | Exit | Observed result |
| --- | --- | --- | --- |
| Worker | `rg --version`, `curl --version`, `lake --version` | 0, 0, 0 | Local text search, network retrieval and Lean tooling are available. |
| D5 | `rg -n 'fixitr_bvar\|fixitr_fvar\|rew_eq_of_funEqOn\|class Rewriting\|def toEmpty\|app_subst_fbar_zero_comp_shift_eq_free' D5` | 0 | Exact retained declarations and the current forwarding consumer are present. |
| Pinned Mathlib | Exact-name/type query in `.lake/packages/mathlib/Mathlib` | 1 | No exact queried Foundation names or `SyntacticSemiterm`/`ClosedSemiterm` types. |
| Pinned Mathlib | Related `relabel`/`subst`/`Term`/`BoundedFormula` query in `Mathlib/ModelTheory/Syntax.lean` | 0 | Related Mathlib syntax APIs exist; this is not a proof that their carriers/interfaces are definitionally equal to Foundation's. |
| Third party | `curl --location --fail --silent --show-error` for the immutable Foundation source, followed by exact declaration query | 0, 0 | Source retrieved; SHA-256 and exact source line matches recorded. |

The Mathlib pin is `db584cd6d46c92f209a44c0f1c829460d327499d` (`v4.33.0`).
No proved-equivalent bridge from its syntax carrier to the retained Foundation
`Rew`/`Semiterm`/`LCWQ` interface is supplied by this evidence. The exact D5
hits are reused by the Compat wrappers; no alternative proofs were added.
The network probe did not read or modify host Codex configuration.

## Compat substNotation boundary

`LO.FirstOrder.RewThreeCompat.substNotation` is a parser/macro selector, not a
substitution theorem. Its source at Compat lines 76-79 repeats the upstream
grammar and expansion at 872-878: `phi/[terms]` expands to `phi ⇜ ![terms]`.
The one-entry vector in the displayed formula is explicitly
`Matrix.vecCons(fvar(0), Matrix.vecEmpty)`; the macro does not turn a single term
into a substitution function without that vector construction.

The parser kind has a separate namespace, while the token grammar is shared
with the imported source notation. The claim is limited to the current pinned
imports and the identical expansion. No parser-equivalence theorem for future
notation extensions or global absence of parser overlap is claimed.

## Generation failure and remaining limits

The earlier `declaration-shapes.md` was empty because `shapes.sh` compared
short authored names such as `fixitr_bvar` with full event names such as
`LO.FirstOrder.Rew.fixitr_bvar`. Its prefix removal assumed the Lean namespace
equaled the D5 module path. That assumption is false for this source transplant.
[generate-audit.py](generate-audit.py) uses explicit full Lean names, asserts
all 40 authored joins resolve, and fails if a name is absent. It creates the
corrected table and JSON without modifying the repository's agent/harness tools.

All 34 public theorem records have kernel dependency capture. Seventeen
non-theorem generated records are outside the nonauxiliary edge extractor;
their JSON entries say so and do not claim an empty dependency set. Generated
constructors, projections, recursion helpers and macro companions have no
independent named upstream declaration. JSON associates their parent source-command
range when a declaration prefix identifies it; otherwise it leaves the source
association explicitly absent. All 40 authored commands have exact source ranges.
Three directly used private Term
simplifier helpers (`fvar?_bvar._simp_1`, `fvar?_func._simp_1`,
`fvar?_fvar._simp_1`) have module identities but no independent public
declaration identity; JSON records `declaration_statement_id: null` for that narrower
field. No missing identity is fabricated.

The original pre-implementation worker/search receipt is not reconstructed
here. Current source identity, current capability, source-location evidence,
and current kernel dependency evidence are available. This documentation
repair does not modify `RewThree.lean`, the accepted Freeze event, or
`Golden/Frozen/state`.

## Validation receipts

[validation.json](validation.json) records the exact commands, exit codes,
selected output and log hashes, including failures and their resolutions.
`make lean`, `make lean-report`, `make emit`, deterministic selftest and the
header check passed. The Scribe project ran 466 tests successfully; its first
wrapper invocation omitted a filter and was rejected as an incomplete full
suite, then the explicit Scribe-filter invocation was accepted.

The initial candidate gate rejected two evidence files under the 1000-line
artifact limit. Compact JSON serialization retained every record and reduced
those files to 106 and 431 lines. The compact-evidence rerun of
`make gate GATE_ARGS=--skip-engineering` passed with exit 0 in 132 seconds;
SL-022 reported the two Scribe protected-surface changes with content checks
passed. The full engineering suite is not claimed by that invocation, and the
separate Scribe/selftest results above remain explicit.
