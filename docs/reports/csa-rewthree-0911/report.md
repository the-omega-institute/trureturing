# RewThree admission and mirror evidence

This is a bounded implementation repair for the source-required rewriting API,
not independent approval, admission, PR delivery, CSA coverage or whole-goal
completion. The implementation carrier is one codex-cli worker under the supplied
consensus-rnd:sshx contract; no delegation or same-round peer output is used.
The supplied three rejects are prior-round findings against the input HEAD.

The input HEAD is `a21038f1e0aa38f27fd8fb8ebf4818292be4d104`; the protected BASE is
`514067737ff46ac3afd2220beed72f5726a179a3`. The repair remains uncommitted.
The current canonical raw report SHA-256 is
`d14ccd8d627578d05cf137071e7109b439cd53b71c96a8f74f020ed3e4bfdd2a`.
The published report evidence includes its adjacent materials archive, input
attestation and provenance; their hashes and paths are in the repair result.

| Module | Current source SHA-256 | Reported / included / public included |
| --- | --- | --- |
| RewThree | `5b780be1e2900eca589caa86bf19ba20debb1253f048d784c08c96c114fd6fe9` | 103 / 85 / 84 |
| RewThreeCompat | `3234ec076b9b86c09dddb0fb636a0cf9c9718b90ef0d5f593d77f2c6b74e685a` | 10 / 9 / 9 |

## Current declaration accounting

[declaration-audit.json](declaration-audit.json) accounts for **all 94 current
included records: 93 public and one private**, with canonical report identities,
per-declaration proof shape, admission basis, utility, source-command association,
raw dependencies, auxiliary paths and prerequisite identities.
[declaration-shapes.md](declaration-shapes.md) lists the **40 authored source
commands** (31 retained commands and nine selectors). These are not 40 new results.
All 34 included theorem records remain `bind-only`, with `escape_witness: none`.
Definitions, classes, recursors, constructors, syntax artifacts and generated
companions receive no independent content or novelty credit.

The proposed basis is `rule-11-upstream-wrapper`: exact retained upstream laws
and the expressly requested addressable API. A generated companion has only its
parent/module basis, never an independent deposit claim. Every included record
has `utility: none`: these are general syntax operations/laws or their compiler
companions, not bounded enumeration, checkers, numeric reductions or certified
finite instances. No escape witness, future consumer or preimplementation
chronology is fabricated. The Scribe consumer is documentation, not a live
mathematical consumer or an atom-required-bridge basis.

The private included definition is
`_private.D5.S3.ConceptDynamics.ZfcTermRewriting.RewThree.0.LO.FirstOrder.Semiterm.toEmpty.match_1.splitter`,
with declaration statement identity
`sha256:608c6d7e4d1ab9741207a552435d4412960a0ab64bb6be8059a2dc268756e8b6`.
It is a generated companion of `Semiterm.toEmpty` (local 112-120; upstream
776-784); `toEmpty.eq_def` points to it. The audit now joins its exact kernel name
to the historical displayed private name, retaining its captured edges and
standard-three axiom closure. No invented downstream consumer is needed.

## Historical captures and current prerequisite scope

The historical [RewThree capture](proof-edges-rewthree.json) and
[Compat capture](proof-edges-compat.json) remain byte-for-byte unchanged, including
their original source labels. Those labels are overbroad: **internal edges expand
auxiliaries, but historical `external_deps` are raw direct D5 constants**.
[historical-capture-bindings.json](historical-capture-bindings.json) records their
hashes, source/report provenance and the complete historical included identities.
It preserves the old **94-public-authored-audit / 95-included** distinction:
RewThree 85 included, old Compat 10 included. The old audit omitted the private
splitter; the historical report and capture did not omit it. Seventeen old public
non-theorem rows were not enumerated by the historical nonauxiliary extractor;
missing capture never means verified empty dependencies.

[current-prerequisites.lean](current-prerequisites.lean) is a bounded review probe,
not a change to the repository extractor or harness. It reads exact kernel
`ConstantInfo` type/value constants with `Expr.getUsedConstants` and records
all 113 constants in the two current modules (103 + 10), plus 14 reached external
auxiliaries: **127 captured constants** in
[current-prerequisites.json](current-prerequisites.json). Its exit code and
probe/source/log hashes bind the capture. All 94 included rows are captured.

The authored audit traverses only auxiliaries, using the existing extractor's
`privateToUserName.isInternalDetail` criterion, retaining a witness path to each
boundary constant. It expands internal and external auxiliaries and stops at
nonauxiliary constants, including public definitions/theorems. It does not
claim complete transitive proof closure, beta/zeta/iota reduction, live-path
necessity, semantic proof-shape classification or exhaustive carrier equivalence.
Raw direct edges, expanded prerequisites, module-internal boundaries and
external nonfrozen boundaries are separate fields. Mathlib/core constants are
not called frozen D5 prerequisites.

| Public declaration | Distinct raw direct frozen constants | Frozen boundaries after auxiliary traversal | Auxiliaries traversed |
| --- | --- | --- | --- |
| `Semiterm.fvar?_rew` | 12 | 13 | 3 |
| `Semiterm.toEmpty` | 5 | 18 | 7 |
| `Semiterm.emb_toEmpty` | 13 | 20 | 6 |

These columns are different sets, not monotonically accumulating counts: raw
auxiliary constants are replaced by their boundary prerequisites. In particular:

`LO.FirstOrder.Semiterm.fvar?_rew` →
`_private.D5.S3.ConceptDynamics.ZfcTermRewriting.RewThree.0.LO.FirstOrder.Semiterm.fvar?_rew._simp_1_2` →
`LO.FirstOrder.Semiterm.fvar?_func`.

The final endpoint belongs to `D5/S3/ConceptDynamics/ZfcPredicate/Term`, whose
stored module statement identity is
`sha256:7f065f3ed5bcc99287a955e54e96d33a1face52845baf0ecfd5859153ed9907c`;
the declaration identity is
`sha256:b7f7ba729436926c957302478b8a4128ad5b4ae42956e8407a5a75eb71ae0e5d`.
`toEmpty` reaches it through `toEmpty._f`, `toEmpty._proof_4` and
`fvar?_func._simp_1`; `emb_toEmpty` reaches it through the latter two helpers.
Their additional Term and AdjunctiveSet prerequisites and exact identities are
listed in the per-declaration JSON, with paths.

Across included roots, 23 distinct auxiliaries are traversed; 21 have no included
canonical declaration identity and retain explicit nulls. The two remaining
auxiliaries have actual included report identities. No name-based identity is
invented. The historical Term simplifier-helper null identities also remain
explicit in the historical dependency fields. Every current frozen nonauxiliary
boundary in this bounded traversal resolves to an included report identity.
Stored frozen module identities are read, not regenerated or rewritten.

## Selector and displayed-formula repairs

`LO.FirstOrder.RewThreeCompat.substNotation` now has the typed interface
`F n₁ → (Fin n₁ → Semiterm L ξ n₂) → F n₂`, under `LCWQ F` and
`Rewriting L ξ F ξ F`, and directly abbreviates `Rewriting.subst` (upstream 840).
The frozen slash grammar (upstream 872-878) still expands `φ/[terms]` to
`φ ⇜ ![terms]`. Compat registers no second active slash grammar. Its old parser
artifact and macro companion are historical records; the current included
selector is a definition with a new canonical statement identity, and no old
capture is silently rebound to it.

The ordinary singleton and two-term client expressions, without a special
parser-kind choice, failed `Ambiguous term` before repair (exit 1) and pass with
Compat imported after repair (exit 0). Separate addressed-selector examples also
pass (exit 0). The displayed singleton is the explicit vector
`Matrix.vecCons(fvar(0), Matrix.vecEmpty)`.

Scribe now quantifies `n,m:Nat` separately from `x:Fin n` for `fixitr_bvar`.
The exact source instance `n=1,m=2,x=0` passes the focused Lean probe.
The conjunction-shift display passes the function symbol `shift` to `map`,
with `Γ:List(S n)`, `LCWQ S` and `SyntacticRewriting L S S` explicit; its map
form passes a Lean probe without an extra lawful-class hypothesis.
Every display in the affected RewThree mirror was read against the retained
source; the three changed displays were inspected after canonical emission.
The Scribe checker establishes address/provenance and KaTeX acceptance, not
mathematical type equivalence of author-written formulas.

## Source, frozen state and validation limits

The selected Foundation source commands and pin remain
`30a16ffa93d79d73ab4d02427fa00f50e039bf29`; the full Rew.lean SHA-256 is
`8df8681a12ebf5ef8700d9710c88fc39bfc35df47ef387e2893df3caf3b69873`.
The 638-953 span is a locator for selected commands, not a claim that every
command in that span was copied. RewThree Lean and all Golden/Frozen and
Meta/Digestion bytes are protected and preserved. RewThree's stored Freeze
contains 85 included rows and module identity
`sha256:bf5cbe594ecb8f58bd3db7db4ecf5c5f8e2cccd0d56af5d865d7b9173fa4bc77`.
Compat remains unfrozen. No deposit, freeze, cover, commit, push or PR mutation
is part of this repair.

[search-receipts.json](search-receipts.json) and [validation.json](validation.json)
remain historical receipts, not new executions or retrospective proof of original
search ordering. D5's exact substitution owner is reused. The pinned Mathlib
search found related syntax, without an established faithful representation
bridge. The immutable Foundation source is retrieved for this repair; no host
configuration, toolchain or pin changes are made.
[repair-validation.json](repair-validation.json) records current commands, exact
exit codes, source/report/material bindings, regression dispositions and limits.
Passing unchanged Scribe full-suite/selftest history is not rerun or promoted to
current independent semantic approval; current focused checks are separate.

No CSA atom coverage, arithmetic projection completion, pair interpretation,
concrete ZFC coding, definition elimination, conservativity, model existence or
relative consistency follows. The complete CSA source through Proposition 68
remains the overall goal; the initial 15 propositions and 117 entries are not a
completion denominator. Independent review, caller-owned admission and MERGED
delivery remain outstanding.
