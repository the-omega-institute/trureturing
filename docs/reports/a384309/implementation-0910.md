# A384309 implementation, 2026-09-10

Provenance: `lean4` skill; Codex implementation worker in the orchestrator's
implementation stage. The proof and local checks are produced by this worker.
No independent review is claimed. The 300,000-term data in the brief are user
observations, not worker observations.

## Target and preregistration

First tier. Base: `f838f20236e5a723d0c025ef53a80a07483008fa`.
Branch: `lane/math/a384309`. Lean 4.33.0; mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.
The recurrence includes the current term before producing the next term.
The target counts only positions starting at 1 and asks for a finite set with
cardinality `9 + (if k = 1 then 1 else 0)` for every positive `k`.

Proposed escape witness, registered before proof probes: every leading-digit
counter is unbounded. Proposed route: some counter is unbounded by finite
pigeonhole; its successive emissions cover all positive integers; every
leading-digit fiber contains infinitely many positive integers, forcing all
nine counters to be unbounded. The occurrence at a successor position is
uniquely identified by its predecessor's digit and that counter's new value.
This gives exactly one occurrence per counter and one extra initial 1.

Success requires a complete kernel proof without `sorry` or private axioms,
the specified build and Scribe checks, freezing through the existing no-atom
writer, and an opened PR. Refutation requires a kernel counterexample.
Otherwise report `blocked`, with attempted routes and the sharp remaining lemma.

## Search receipts

1. Repository D5, at the base above:
   `rg -n -i 'a384309|a248034|leading.?digit|leading.?counter|首位|first.?digit' D5`.
   No matching recurrence or multiplicity theorem. Hits concerned positional
   numeration, admissible words, and a different digit-gas counting process.
2. Pinned mathlib: pending cache readiness and source inspection.
3. Third-party Lean ecosystem, arXiv, and OEIS: pending. The brief's claim that
   the 2025 paper states only a conjecture is currently `ASSUMED-UNVERIFIED`.

## Public theorem accounting

No public Lean theorem has yet been added. Final declaration-by-declaration
`proof_shape`, direct frozen dependencies (GID and `statement_id`),
`escape_witness`, and `admission_basis` will be recorded here.

## Build receipts

Not run yet. Cache, make exits, measured times, and log paths will be appended.

## Not claimed

No proof, counterexample, novelty beyond the searched scope, frozen node,
atom coverage, independent review, or PR is claimed at this checkpoint.
No theory volume or atom is being created for this task.

## Search batch 2

- Read all 779 lines of CLAUDE.md in chunks, including truncated intervals;
  read agents/CONTEXT.md and spec A5.1. `utility: none` is the exact grammar
  for this general, unbounded theorem (not a finite certified instance).
- This worktree initially had no `.lake`; started `make lean-cache-ensure`
  before any Lake invocation. Inspected the existing main checkout's mathlib
  sources read-only; `git rev-parse HEAD` there equals the requested pin.
- Pinned mathlib search `rg -n -i 'a384309|leading.?digit|leading.?counter'`
  over Mathlib: zero hits. Read `Data/Nat/Count.lean` and the Count section of
  `Data/Nat/Nth.lean`: reuse `Nat.count_injective`,
  `Nat.count_nth_succ_of_infinite`, and `Nat.nth_mem_of_infinite`.
  Located `Finite.exists_infinite_fiber` in Data/Fintype/Pigeonhole.
- `curl https://oeis.org/A384309/internal` succeeded and was read in full:
  revision 32, 2025-07-21; David James Sycamore, 2025-05-25. Its comment
  explicitly calls the exact multiplicity a conjecture. Its examples and
  Python generator include the current term before reading the counter.
  This page does not cite a research paper; no unidentified 2025 paper is claimed read.
- A later Python urllib attempt at the same OEIS page and its two xrefs got
  HTTP 403. These failures are not negative search evidence; curl fallback pending.
- arXiv web search, all fields, query `A384309`: HTTP 200, explicitly
  "produced no results". Saved page and extracted text in runner attempt directory.
- GitHub Lean code search is in flight. No globally exhaustive novelty claim.

## Search completion and cache

- GitHub authenticated code search `A384309 language:Lean`: total_count=0.
  Broader `"leading digit" "counter" language:Lean` returned one file,
  YijunYuan/TrustworthyKedlaya/Kedlaya/SabcOrderType.lean; source inspection
  concerns Hahn-series supports and ordinal order types, not this recurrence.
- curl fallback fetched all three OEIS internal pages successfully; complete
  extracted texts and HTML are in the runner attempt directory. A000030 gives
  only the initial digit definition. A248034 counts all digit occurrences and
  selects the last-digit counter; it is a different process. Its external
  SeqFan link and A000030's Cobham paper were not opened, ASSUMED-UNVERIFIED.
- No dominating theorem found in the searched D5, pinned mathlib, GitHub Lean,
  arXiv identifier, and OEIS scope; retain first-tier classification.
- make lean-cache-ensure EXIT=0, 19.529 seconds, macOS ARM: status=seeded,
  method=clonefile, donor=/Users/chronoai/trureturing, clonefile_attempts=1,
  stamp_miss=null, project_olean_state=warm, mathlib_olean_state=warm,
  archive_status=not_attempted. Full receipt: attempt-1/lean-cache-ensure.log.
- Capacity readings before Lean/Scribe/note creation: Arith has 33 immediate
  Lean files, its Blueprint mirror 56; choose a new CounterSequences subbucket
  (currently absent, 0 files). Library/Words recursively has 26 files.
  Report subbucket now contains 1 file (it was absent before creation).

## Lean fragment 1: all digit classes occur infinitely

- Canonical route returns D5/S3/Arith/CounterSequences/LeadingCounter.lean,
  S3, generality I. Initial route calls rejected absolute manifest paths,
  JSON nulls, missing required fields, and artifact="". After reading the
  loader and using repository-relative JSON with artifact="lean" and empty
  selector/tag, route EXIT=0. No routing rule was changed.
- leading10 is literally `(Nat.digits 10 n).getLastD 0`; its positive-input
  bounds come from Mathlib's last-digit and digit-bound theorems.
- The orbit state contains the current term and nine counters. The proved
  orbit_count identity identifies each counter with Nat.count over earlier
  terms. term_recurrence includes the current term.
- The planned all_digits_infinite argument is now checked by Lean: pigeonhole
  gives one infinite fiber; emit_nth gives every positive integer in the term
  range; powers 10^m*(d+1) supply infinitely many positive inputs per digit.
- Hot-tree `lake env lean D5/S3/Arith/CounterSequences/LeadingCounter.lean`
  EXIT=0. Initial errors were explicit argument order and negated-equality
  syntax; corrected against pinned source signatures. No sorry or new axiom.
  This file check is not the final project build or multiplicity proof.

## Lean fragment 2: exact finite multiplicity

- Hot-tree file check EXIT=0, no warnings. The target is now proved as
  `leading_counter_multiplicity (k : ℕ) (hk : 0 < k)` with both Set.Finite
  and ncard = 9 + (if k = 1 then 1 else 0).
- successor_bijOn sends a predecessor index to the leading-digit counter
  used there. Nat.count_injective proves injectivity; emit_nth and
  all_digits_infinite prove surjectivity onto Fin 9. This proves both
  finiteness and nine successor occurrences, without finite enumeration.
- The public a function has a 0 = 0, a 1 = 1. Translating predecessor n
  to sequence position n+2 isolates position 1, which contributes only for
  k=1; positive k excludes the unused position 0.
- a_recurrence verifies the actual one-based definition against counter,
  whose Nat.count predicate uses a(i+1) for i<t, precisely positions 1..t.
- Proof repair addressed dependent DecidablePred rewriting with simp,
  explicit beta reduction for index arithmetic, and equality orientation.
  No target was weakened. Full make lean and semantic axiom audit still pending.

## Full Lean build

- `make lean` EXIT=0, 46.477 seconds, 12828 jobs; the new LeadingCounter
  module was built in 3.9 seconds. Log: attempt-1/make-lean.log.
- LEAN_CACHE: status=present, method=none, stamp_miss=null,
  project_olean_state=warm, mathlib_olean_state=warm,
  archive_status=not_attempted. This is macOS ARM local timing, not CI timing.
- Source length 181 lines; no sorry, axiom declaration, or native_decide.
  Existing project warnings were replayed by Lake; the new module's file
  check has no warnings. Canonical Lean report and semantic audit are running.

## Canonical report and semantic audit

- `make lean-report` EXIT=0, 63.159 seconds. Report SHA256:
  297cbbf4190e4df0a08eb356a334c6b731cb3c135d47b2fbf951527b28812aea.
  Log: attempt-1/make-lean-report.log; canonical output:
  .lake/build/stratalint/raw-lean-report.json.
- Existing proof-edges.sh, using Lean Expr.getUsedConstants on elaborated
  values/types and expanding auxiliary constants, returned EDGES_OK,
  24 nonauxiliary constants, 9 nonprivate constants (including the generated
  orbit.eq_def equation). All external D5 dependencies are empty; all axiom
  sets are subsets of propext, Classical.choice, Quot.sound.
- The live chain is leading_counter_multiplicity -> successor_multiplicity
  -> successor_bijOn -> all_digits_infinite / emit_nth / term_recurrence.
  a_recurrence uses digit_eq_iff, term_pos, and term_recurrence -> orbit_count.
- The compiler eliminates the reflexive a_one use in the main proof; it is
  not claimed as a surviving constant edge. Its named companion purpose is
  the initial-condition API required by the brief. KernelAudit.recurrence_echo
  is the registered semantic consumer of a_one and a_recurrence, bundling
  the two source conditions. It is not an additional frozen result.
- KernelAudit initially timed out reducing the 21-entry private sequence
  echo at 200000 heartbeats. The general proof and axiom queries passed;
  replace that oversized smoke test with the first six actual terms, enough
  to distinguish the update order, plus leading10(1234)=1 and zero behavior.
- Library note includes Verified locator with literal url and doi lines.
  Source inspection found production Describe rejects suspected-novel nodes;
  the proved multiplicity is accurately marked repo-derived, with the OEIS
  conjecture acknowledged. No global novelty assertion is needed or made.

## Public theorem accounting

All GIDs below have prefix D5/S3/Arith/CounterSequences/LeadingCounter.
Direct frozen dependencies for every declaration: [] (no GID/statement_id pairs).
The Lean semantic audit found no external D5 dependency anywhere in this module.

| Public theorem | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| a_one | bind-only | null | companion in escape-witness module; source initial-condition API, named consumer KernelAudit.recurrence_echo -> a_one |
| a_recurrence | content | orbit_count | escape-witness |
| leading_counter_multiplicity | content | all_digits_infinite | escape-witness |

The generated orbit.eq_def is not an authored mathematical result; it is
bind-only, escape_witness=null, and a companion equation for the orbit definition.
Definitions leading10, digit, orbit, a, and counter define the actual process.
No declaration is primarily bounded enumeration, a checker, numeric reduction,
or a certified finite instance: computational_content.kind=none throughout.
Other utility fields: not-applicable(kind=none).

For a_recurrence, the four CLAUDE.md 3.2 conditions are:

1. In the dependency closure: a_recurrence -> term_recurrence -> orbit_count,
   as read from the elaborated Lean environment.
2. Not obtained by projection: orbit_count proves a new state invariant by
   induction over the recursive update, for every time and all nine counters.
   The imported count lemmas alone do not identify this orbit's counters.
3. Not definitionally equivalent: orbit_count concerns the complete stored
   counter function before each step; a_recurrence is a scalar next-term
   identity expressed using one-based positions and leading10.
4. On a live path: the next state's current value is a stored counter plus
   one; orbit_count replaces that stored value by the required prefix count.
   Removing that invariant leaves no justified equality to the prefix count.

For leading_counter_multiplicity, the four conditions are:

1. In the dependency closure: main -> successor_multiplicity -> successor_bijOn
   -> all_digits_infinite; the semantic edge audit confirms this chain.
2. Not obtained by projection: the proof combines a recurrent color, the
   recurrence's count enumeration, and distinct decimal-power witnesses to
   force all digit classes to recur. No imported theorem states that dynamic
   conclusion, and the direct frozen premise set is empty.
3. Not definitionally equivalent: all_digits_infinite says each digit class
   has infinitely many visits; the target says each fixed value has finitely
   many positions with an exact cardinality. Neither is a restatement of the other.
4. On a live path: all_digits_infinite supplies the k-th visit used for the
   surjectivity component of successor_bijOn. Without that visit, injectivity
   only gives an upper bound, not nine occurrences. Finiteness and cardinality
   then use this actual bijection; no unused conjunction supplies the witness.

These four judgments describe the actual proof; the dependency audit alone
is not claimed to decide all proof-shape semantics.

question_answered: Does the one-based A384309 recurrence have exact finite
multiplicity nine for every positive k, with the initial exception for 1?
Preregistration: Target and preregistration section above, committed before probes.
dominating_theorem_search: not-found-in-searched-scope; D5 -> pinned mathlib
-> GitHub Lean / arXiv / OEIS, with failed and unopened requests distinguished above.

## Kernel semantic echo

KernelAudit.lean final file check EXIT=0. Both private decidable echoes pass:
leading10(0)=0, leading10(1234)=1, leading10(999)=9; and a at positions 0..6
is [0,1,1,2,1,3,1]. recurrence_echo combines the public initial condition and
recurrence for all positive times. These are smoke tests, not evidence of the
unbounded multiplicity statement, and they are not frozen as finite instances.
#print axioms for all three public theorems returns only
[propext, Classical.choice, Quot.sound]. Log: attempt-1/kernel-audit.log.

## Canonical public statement identities

| Declaration | statement_id |
| --- | --- |
| a_recurrence | sha256:a1dcd1d2f687cf5665701eabddafa3829482cd7bcb1ff7669251866654f650e0 |
| leading_counter_multiplicity | sha256:80db245f1604b878987fe5451c2ebdde412b1ab9e9efe3f73f727923c8ed850e |
| a_one | sha256:bd0b2ea1cf0ce25271bda8c4e3597b1271a3985e8e01ae1aaa6db196f8fadd05 |
| eq_def | sha256:9521ff731d924a2fb48f4d5928018457a62765969a508717b46fa5eacc7a8f89 |

## Scribe emission and duplicate recheck

- make emit EXIT=0, 63.397 seconds, one changed Blueprint. Log:
  attempt-1/make-emit.log. The emitted Markdown was read in full; all three
  formulas agree with the Lean statements, including positive times,
  positive values, the finite occurrence set, and the indicator at k=1.
- Fetched origin/dev, then git merge-tree --write-tree HEAD origin/dev
  returned tree e10c7367844d3eb4de618aeb373c9d5bc3e7e2d6 without conflicts.
  git grep -P for A384309 and both multiplicity spellings over origin/dev
  D5/Blueprint returned no matches (grep exit 1 means no match).
- Started the required scribe-content-checks script using immutable base
  f838f20236e5a723d0c025ef53a80a07483008fa. Also run projections --check
  explicitly, because this content-only change does not awaken that branch
  of the script. The remaining Describe and real KaTeX checks are not skipped.

## Scribe content checks and freeze precheck

- Explicit projections --check EXIT=0, 12.125 seconds.
- Required scribe-content-checks.sh with the canonical report and immutable
  base EXIT=0, 24.421 seconds. Describe and Library locator checks pass.
  Real KaTeX result: markdown: judged=1 formula(s)=3 red=0.
  Existing online-doi-title-check lines are nonblocking offline-gate
  observations, not claims of online DOI verification.
- deposit-header-check EXIT=0, 9.312 seconds;
  DEPOSIT_HEADER_CHECKED SL-012 D5/S3/Arith/CounterSequences/LeadingCounter.lean.
- make deposit requires a real ATOM_ID and performs coverage after freezing.
  This task has no atom. As authorized in the brief, use its same canonical
  deposit-header-check and ledger-align --add writer, after make lean,
  make lean-report, and make emit. No fake atom or theory ingestion is used.

## No-atom freeze

- Canonical ledger-align --add EXIT=0, 8.798 seconds.
- LEDGER_ALIGN selectors_considered=3941 changed=0 added=1 unchanged=3940 conflicts=0.
- event_hash: sha256:18cbdd8c7c9bee9f2957abccab179dd0f8ca2b3073b13cd5adfa76fdbab6f4d2
- module statement_id: sha256:2f0847709ba6564002b9f86e10c77ca2d0ce224ceade476ce3ec137e8f0d2b85
- Included declarations: 28; prerequisite_frozen_node_ids: [].
- State: Golden/Frozen/state/D5/S3/Arith/CounterSequences/LeadingCounter.lean.json.
- This freezes the module only; no source_id, atom_id, or coverage transition is claimed.
- Freeze log: attempt-1/freeze.log. All identity values above are read from
  the canonical writer output, not manually invented or recomputed historical data.

## Delivery checkpoint

- Outcome under this task's stopping criterion: **成**. The full requested
  theorem is proved, make lean exited zero, the public theorem axiom audit
  contains no sorry or private axiom, the module is frozen, and the PR is open.
- PR: https://github.com/the-omega-institute/trureturing/pull/6716, base dev.
  Implementation commit: 8d3fddd79647c9fac3d8752a37224f5191f2f7c0, pushed to
  lane/math/a384309. This final report update is committed separately.
- Actual GitHub snapshot at that implementation commit: state OPEN,
  autoMergeRequest=null; Candidate harness engineering checks and Canonical
  Lean report production IN_PROGRESS; the downstream admission check has
  not appeared yet. This is not a claim that remote checks have passed.
- make pr-open created the PR successfully and is synchronously watching
  required checks. Its terminal exit, the final pushed HEAD and the checks
  for that exact HEAD will be recorded in the runner-owned result.json and
  accompanying report, avoiding a further report-only CI cycle.

## Final unclaimed scope / 未主张

The earlier sections preserve their checkpoint-time observations; this section
supersedes their then-pending completion status. No finite probe is offered as
proof of the universal result. No globally exhaustive literature search,
discovery priority, independent review, atom ingestion or coverage, or proof
of the separate last-k-digit-position conjecture is claimed. The external
Cobham paper and SeqFan page remain ASSUMED-UNVERIFIED. Local build timings
are macOS ARM measurements, not CI predictions. The PR has not been merged.
