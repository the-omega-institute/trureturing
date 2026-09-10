# CRIM Conjecture 3: implementation report

## Provenance and scope

No skill was used. One Codex implementation worker performed the source review,
two algorithm implementations, Lean proof and local checks. No independent review
agents were commissioned; two algorithms do not constitute two independent model
sources. This is an implementation handoff, not an independent admission verdict.
The supplied worktree and branch were clean at base
`6ec605909ca7c64b117bc8bdecc8a62988dfebb4`.

Target: only the r ≥ 7 formula of printed Conjecture 3 in Bašić, Gottlieb and
Krnc, *CRIM: A Natural Game on Integer Partitions*, arXiv:2606.16828v1.
No statement about the rest of the paper, an intended assertion or any corrected
formula is made. No priority for the counterexample is claimed.

## Preregistration and bind-only attempt

Before any mathematical probe, preregistration v1 was written to the runner
attempt directory as `preregistration-v1.md`; the corresponding timestamp is in
`worker-notes.log`. The repository copy is [preregistration.md](preregistration.md).
`question_answered`: whether that previously printed formula holds.
Research tier: first-tier recent small conjecture, with an explicitly unverified
prior posting; the user's instruction authorizes implementation on that basis.

The first route attempted was existing Mathlib instantiation, frozen projections
and normalization. No exact CRIM move graph or SG evaluation was found in the
ordered scopes below. Finite minima, list arithmetic and well-founded recursion
alone do not supply any of the CRIM descendant values. Consequently this route
cannot close the claim and the module is not bind-only. The counterfactual test
is concrete: removing the checked graph recurrence leaves no premise from which
the root SG value can be inferred. A mex computation on twelve assumed constants
was never used as the target or a premise.

Proposed `escape_witness`: paper-specific moves, descent by cell count, SG/mex
evaluation, and a correct finite certificate for the reachable graph. Observed:
`conjugate_sum`, `move_decreases`, `grundy`, `mex_spec`, `mex_unique` and
`certificate_correct` implement exactly this; `result.checked` verifies the
complete 377-entry certificate using `decide +kernel`. The observed witness
matches preregistration v1. No replacement witness or retrospective relabelling
was needed. The predicted counts and numerical values all agree with observation.

## Rendered source audit

The worker downloaded and rendered the PDF, then visually inspected printed
pages 4, 5, 8 and 18 (physical PDF pages have the same numbers). The rendering
files are `pdf-page-04.png`, `pdf-page-05.png`, `pdf-page-08.png`, and
`pdf-page-18.png` in the attempt directory. The brief's text-layer P17 corresponds
to the zero-based index of physical page 18. PDF SHA-256:
`67a8151c78c73da470aae28cc5f1f7657a9de9367aa4f77e6a4dda325cd12cb3`.

| Item | Rendered text / finding |
| --- | --- |
| Rectair definition, p. 5 | R^k_{r,c} = [c^(r−k), c−1, …, c−k] |
| Valid parameters, p. 5 | r,c positive; 0 ≤ k < min(r,c) |
| Conjecture subscript, p. 18 | R^k_{r,r−1}, not R^k_{r,r} |
| Exceptional condition | k = r−2 and r odd |
| Exceptional / other values | 3 / 1 |
| Large-r range | “For r ≥ 7 we have” |
| Row move, p. 8 | Delete the ith part for any 1 ≤ i ≤ r |
| Column move, p. 8 | Take the conjugate of the partition resulting from a row move on λ′ |
| Empty/zero convention, p. 4 | Parts are positive; the only partition of zero is [] |

All task-critical characters match the brief. The Lean rectair uses r−k copies
and k descending entries through c−k. Natural parameters and `k < min r (r−1)`
express exactly the valid domain for this large-r formula. The evaluator's
`moves` function is a list union of row deletions and conjugate-row-conjugate
deletions. Multiple choices yielding the same position are harmless: SG uses
the finite set of option values. `height p j` counts rows with length greater
than zero-based column j. The scan through `p.sum` covers every column because
each part is at most that sum, and it filters zero heights. Zero rows cannot be
selected. This is a total extension to natural lists; on paper partitions it is
exactly CRIM, with no fallback move, artificial terminal state or depth cutoff.

## Two fresh computations

[recompute.py](recompute.py) has no supplied SG value table as input. Its only
root input is `(6,6,5,4,3,2,1)`. Method A constructs columns by conjugation,
recursively evaluates all legal successors with memoization, and increments a
candidate until absent. Method B directly deletes a column by shortening each
row reaching that column, explicitly constructs the graph, orders by area, and
finds mex using a membership vector. The implementations share neither the move
routine nor the mex routine. Both start at terminal values through their own
algorithm. The script compares all states, all move sets and every computed
value, not just the root.

| Successor | Recursive A | DAG bottom-up B |
| --- | --- | --- |
| [6, 6, 5, 4, 3, 2] | 0 | 0 |
| [6, 6, 5, 4, 3, 1] | 2 | 2 |
| [6, 6, 5, 4, 2, 1] | 0 | 0 |
| [6, 6, 5, 3, 2, 1] | 4 | 4 |
| [6, 6, 4, 3, 2, 1] | 0 | 0 |
| [6, 5, 4, 3, 2, 1] | 0 | 0 |
| [5, 5, 5, 4, 3, 2, 1] | 2 | 2 |
| [5, 5, 4, 4, 3, 2, 1] | 4 | 4 |
| [5, 5, 4, 3, 3, 2, 1] | 0 | 0 |
| [5, 5, 4, 3, 2, 2, 1] | 4 | 4 |
| [5, 5, 4, 3, 2, 1, 1] | 0 | 0 |
| [5, 5, 4, 3, 2, 1] | 5 | 5 |

Both visit 377 distinct partitions including the empty position and the root;
their move graphs are identical. The explicit DAG has 2190 distinct directed
edges and 12 distinct root options. Method B measures its longest descending
chain as 12 edges (13 vertices). The root has 27 cells;
its option-value set is exactly {0,2,4,5}, hence both root values are 1. There
are no discrepancies with the task's table. The full independently computed DAG
is preserved as `computation.json` in the attempt directory. Counts and depth
are algorithmic observations; the kernel proof's obligation is recurrence and
closure on all certificate entries, not a separate theorem about graph size.

## Formal proof and per-declaration classification

The only included public theorem is
`D5/S0/Certificates/Games/CrimGrundyRefutation.result`; its type is literally
`¬ claim`. The only included closed Prop definition is the matching `.claim`.
It directly uses `grundy (rectair ...)`, and `grundy` recursively uses `moves`.
No successor values are constants in the claim.

| Field for result | Value |
| --- | --- |
| proof_shape | content |
| Direct frozen dependencies (GID + statement_id) | Empty set: there are no D5 imports, hence no such GID or statement_id |
| escape_witness | Complete CRIM graph recurrence certificate, its soundness by cell-count induction, and well-founded SG evaluation |
| admission_basis | escape-witness (one of the three allowed values) |
| utility | kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Games/CrimGrundyRefutation.claim; result=D5/S0/Certificates/Games/CrimGrundyRefutation.result; claim=D5/S0/Certificates/Games/CrimGrundyRefutation.claim |

All internal proofs are parameterized private proof definitions; no additional
included theorem remains in the final design. The initial semantic report
included private theorem helpers despite their visibility, so those helpers
were converted to proof definitions. The next count also exposed three
generated `eq_def` theorems. Explicit `List.rec` definitions and
`WellFounded.fix` remove those generated declarations while retaining exactly
the same graph and cell-count recurrence. This is an implementation refinement
of the registered witness, not a different witness.
`refutes` is a utility basis, not a fourth admission_basis.

The finite certificate contains candidate numbers generated by the fresh
computation. The proof does not trust these numbers: for every listed position
it checks closure under **all actual moves**, absence of its assigned value
among option values, and presence of every smaller number. `certificate_correct`
then proves the assigned value equals `grundy` by induction on cell count. The
empty position is included with value zero, so this validates the recursion all
the way from terminals. Its proof is on the live path
`checked → certificate_correct → actual → result`; no irrelevant fact was added
only to inflate the dependency closure. The value-1 root equality and the
conjecture's value-3 equality produce the contradiction.

`mex` uses Mathlib's `Finset.min'` on the complement within `range(card+1)`;
cardinality proves this set nonempty. `mex_spec` proves the least-excluded
property, and `mex_unique` is consumed in certificate soundness. `grundy` uses
`WellFounded.fix` with the well-founded measure `List.sum`; row deletion strictly
reduces area and conjugation preserves it. There is no `native_decide`, `sorry`,
new axiom, trusted external numerical oracle or SG table assumption. The first
`make lean` kernel build reported only `[propext, Classical.choice, Quot.sound]`
for both claim and result.

## Ordered library receipts

Pinned environment: Lean v4.33.0; Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.

1. Repository first: `git grep -n -P '\b(Grundy|mex|Sprague|PGame|CRIM)\b' -- 'D5/**/*.lean'`
   returned four comment hits at the starting tree: three in
   `ComplementaryGoldenRatioLimit.lean`, one in
   `Games/VersionBTwelvePileRefutation.lean`. Positive control with the same
   boundary syntax, `\b(Mathlib|theorem)\b`, found the imports and theorem in
   `TripodNimPeriodRefutation.lean`. Receipts: `repository-search.txt` and
   `positive-control.txt`. Follow-up reading found public `mexScan`/`mexPos`
   in the former (CamelCase names are outside the word-boundary query), but
   no SG semantics and no least-excluded correctness theorem there. The latter
   has a normal-play losing-state certificate for a different pile game,
   not a CRIM/SG evaluator. Thus the broad “zero game pieces” description in the
   brief is too strong for this tree; no directly reusable CRIM/SG result exists
   among these hits. Neither module is imported or re-proved.
2. Pinned Mathlib: filename inventory for Game/Mex/Partition/WellFounded;
   `rg -n -P '\b(grundy|Grundy|mex|PGame|sprague|Sprague)\b' .lake/packages/mathlib/Mathlib`.
   Three comment hits concern ordinal/cardinal least omissions. No
   `SetTheory.Game.PGame`, `SetTheory.Game.Nim`, `Nat.mex` or `Ordinal.mex`
   declarations/files were present. `Order.GameAdd` is about relations.
   Positive control `\b(theorem|def)\b` there produced 24 lines.
   `Nat.Partition` has positive multiset parts and sums; `Multiset` has erase
   and sum infrastructure; `YoungDiagram.transpose` is available.
   `Finset.wellFoundedLT` is present in `Data/Finset/Defs.lean`, and
   `WellFounded.min`/induction are present in `Order/WellFounded.lean`.
   These supply general tools, not a move graph or evaluated CRIM instance.
   We directly reuse Mathlib list sums, finite minima, cardinal bounds and
   measure induction. Receipts: `mathlib-games.txt`, `mathlib-positive.txt`,
   `mathlib-finset-wf.txt`, `multiset.txt`; exact helper signatures were also
   checked by Lean elaboration in a warm environment.
3. Third-party Lean ecosystem: GitHub repository query
   `combinatorial games language:Lean` found `vihdzp/combinatorial-games`,
   `sinhp/Combinatorial-Games`, `t4ccer/misere-games`, `Happyves/Lean_Games`.
   The relevant general SG file in the first repository was read at current
   revision `a087fede837fa7f4ee6a2ffb2c6560a3112d4d6d`.
   `IGame.grundyAux` and `Impartial.grundy`/`nim_grundy_equiv` are available,
   noncomputable nimber theory. Its toolchain is v4.34.0-rc2 and Mathlib pin
   `156b4fb3500549c5983e06348faca9d6ee499841`, incompatible with this tree.
   There is no exact finite CRIM evaluation to import or port. The present
   proof does not re-prove the general Sprague–Grundy equivalence theorem.
   GitHub code queries `"CRIM" "Grundy" language:Lean`,
   `"rectair" language:Lean`, and `"2606.16828" language:Lean` each returned
   total_count 0 with incomplete_results=false; JSON receipts are saved.
   A preliminary unquoted `CRIM` query produced substring false positives and
   is not treated as a game result. Network search capability was exercised.
4. Only after these stages was the local verified finite evaluator implemented.

`dominating_theorem_search`: not-found-in-searched-scope; the scopes and
positive controls above delimit that conclusion. No universal absence claim.

## Version and prior-work review

On 2026-09-10 the arXiv abstract/history page still listed only v1, submitted
2026-06-15T15:09:22Z. DataCite independently listed version 1, type Preprint and
no related publication identifiers. No author v2 or formal correction was
identified. Crossref's bounded title query (top three returns) produced no
matching journal publication. Google returned a challenge/browser requirement,
DuckDuckGo returned a bot challenge, and Bing RSS returned unrelated results;
none is counted as a successful literature search. These limits are recorded,
not converted into a claim that the entire literature lacks a proof. The
arXiv history and DataCite checks directly resolve the required v2 stop test.

The MathDB page was fetched and read. It explicitly labels the 2026-08-20
Shivam Patel posting “Claimed solved” while stating “An unverified posted
calculation claims the conjecture is false in both parity cases, but no
independent confirmation was found.” The timestamp in page data is
2026-08-20T14:33:05.996768Z. URL:
https://mathdb.com/p/375372/the-sprague-grundy-conjecture-for-near-square-rectairs.
The separately recomputed r=7 data coincide with that post. We make no verdict
about its r=8 assertion or the post as a whole and no first-discovery claim.

Provenance for the printed claim and rules is `literature-attested`, with
`Library/Certificates/basic2026crim.md` as the canonical note. The checked
formal result has `repo-derived` provenance relative to that source. The note,
Lean prose and this report explicitly record the prior unverified posting.

## Validation and handoff

The canonical router returned
`D5/S0/Certificates/Games/CrimGrundyRefutation.lean`. An initial absolute-path
manifest invocation was rejected; rerunning with repository-relative
`.lake/crim-manifest.json` succeeded. Exploratory Lean signature/proof probes
used `lake env lean` only after `make lean-cache-ensure` reported both caches
warm with stamp present. All project builds use `make lean`/`make lean-report`;
no bare `lake build` was invoked. The temporary proof probes initially exposed
ordinary syntax/lemma-name errors, all corrected before the module was built.

The first `make lean` exited 0 in 173.633 seconds on this macOS ARM worktree,
with warm Mathlib/project caches; the new module's reported build time was
131 seconds. This is a local measurement, not a CI timing prediction. The
heartbeat comment warning was then fixed and the digest shortened; the
required single-line utility header exceeds Mathlib's style line length.
The intermediate `make lean` after the helper conversion exited 0 in 117.999 seconds
(module: 108 seconds). Its eleven `linter.defProp` warnings reflect the
intentional private proof definitions used for the single-theorem contract;
no linter was disabled. Both printed axiom closures still contain only
`propext`, `Classical.choice` and `Quot.sound`.

The Scribe governance regex was run with `rg -n -i -P`, including the full
GovernanceProcessReference alternatives plus `\bsearch(?:es)?\b` and
`\bduplicate\b`: zero matches (exit 1). The same file gave a positive
`\bMathlib\b` match (exit 0). `scribe-scan.txt` records the exact command.
The non-null metadata locator is present **inside** `## Verified locator`:
DOI `https://doi.org/10.48550/arXiv.2606.16828`. The section also retains URL
`https://arxiv.org/abs/2606.16828` and the versioned PDF scope;
`locator-check.txt` records the section body. The first `make emit` rejected
metadata containing both DOI and URL (`invalid-doi`), so the metadata now
selects DOI only, following `hennessey2024tree.md`. The four dangling-reference
findings came from that rejected note, not from its canonical Library address.
No loader or governance rule was changed.

Final validation on the explicit-recursion source completed successfully:

| Command | Exit | Elapsed seconds | Receipt |
| --- | --- | --- | --- |
| `make lean` | 0 | 144.213 | `lean-explicit.log` / `.json` |
| `make lean-report` | 0 | 243.615 | `lean-report-explicit.log` / `.json` |
| `make emit` | 0 | 79.468 | `emit-explicit.log` / `.json` |
| `make gate BASE=6ec605909ca7c64b117bc8bdecc8a62988dfebb4` | 0 | 889 (gate clock) | `gate.log` / `.json` |

The gate checked implementation commit `99716a79cd` against the immutable
starting base. The final commit only records these results in this report.
The gate's engineering build, full engineering tests (749 seconds), selftest,
Lean report consumption, admission, and FILEMAP conformity all passed.
This is a local gate result; no remote CI result is asserted.

The gate also reports `SL-022` for the added Scribe source: one protected-surface
change. The inner admission flow returns 3 for this marker; the canonical
`make gate` wrapper normalizes it to 0 after content checks pass. Thus the
reported zero exit is not an assertion that there were no markers. `SL-031`
records the typed refutation utility while leaving semantic classification to
review; `SL-034` records the intentionally absent frozen state. The requested
Scribe edit was already authorized, and no merge or freeze was performed.

The final source SHA-256 is
`d9a30262dc7f9c76838aee89b9c850b1b126c58c47f3b8344490e409e5333cbb`.
The final raw report has exactly **one included theorem**, `.result`, and
exactly **one included definition with the checked closed Prop type**, `.claim`.
It reports `utility_refutation.is_closed_negation = true`. All declaration
axiom closures lie in the standard three-axiom set.
`semantic-summary.json` preserves this extracted evidence, including:

- claim statement_id: `sha256:aaf0f9032fdbb04a70e0b69fb3b6e7a04a5df98542b19bf8093d268ae0245c5a`;
- result statement_id: `sha256:8b9fba2c790bd44c5cd9d262760b7344f35e51c1b008d6a4b02321dd25bcbff5`.

The canonical generated Blueprint mirror is
`Blueprint/D5/S0/Certificates/Games/CrimGrundyRefutation.md`; the final emitter
confirmed it without any hand edit. The final source build retains the eleven
intentional `defProp` style warnings and the long utility-header warning
recorded above; no warning was suppressed.

Worker receipts and source snapshots are in
`/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/crim-grundy-0910/attempt-2`,
with the snapshots under `delivery/`. The result envelope and completion
sentinel are published there by temporary-file write and atomic rename, after
the final report commit is pushed. No production deposit, cover or PR was
performed; no frozen state file was added.
