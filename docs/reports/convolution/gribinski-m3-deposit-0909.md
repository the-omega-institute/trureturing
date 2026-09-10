# Gribinski m=3 freeze deposit, 2026-09-09

## Provenance and Scope

- Skill context: no skill invoked by this worker; direct Codex implementation in the runner-owned `consensus-rnd/sshx/gribinski-m3-deposit-0909/attempt-1` attempt.
- Carrier: one Codex worker executes the freeze commands and verifies their artifacts. No new review seats are invoked here. The user reports an earlier independent admission review with `approve` and zero blocking findings; the reviewer identity/model family and original ballot are not supplied to this worker.
- Mixing: serial landing-form verification by this worker, using the already approved `escape-witness` basis. Prior mathematical classifications are attributed to the supplied review, not claimed as a new independent review.
- Form: `deposit`. The mathematical implementation and both Blueprint mirrors already landed through PR #6525. This lane adds only canonical freeze artifacts and its report.
- Chain: no m=3 atom is supplied or created. Both modules are **frozen, uncovered**, with the uncovered boundary recorded against #4996.
- Nonclaims: no new mathematics, no arbitrary-m theorem, no coverage, no new atom or source volume, no `.lean` edits, no budget or domain changes, no auto-merge.

## Step 1: Baseline and Precedent

`git fetch origin dev` exited 0. Initial worktree was clean on `lane/math/gribinski-m3-deposit-0909`.
Both `HEAD` and `origin/dev` resolved to `b9ad72010f6473b22e7616958a7e78db6fe0d2e2`, the stated PR #6525 merge.

`git ls-tree -r origin/dev -- <six target paths>` returned all six regular blobs:

| Path relative to the relevant Convolution directory | Git blob OID |
| --- | --- |
| `D5/.../GribinskiDegreeThree.lean` | `5fcfb4fa8c60b68725cbb26fdc4357297cba1bd4` |
| `D5/.../GribinskiDegreeThreeDiscriminant.lean` | `0b8477fdec8a1d0ff29c6beae9c264645b00b790` |
| `Blueprint/D5/.../GribinskiDegreeThree.scribe.cs` | `75083f06c6cf842076e64822b02d35e21b43d729` |
| `Blueprint/D5/.../GribinskiDegreeThree.md` | `f38e657e456629fad7ef5c1025be9a03ce044917` |
| `Blueprint/D5/.../GribinskiDegreeThreeDiscriminant.scribe.cs` | `1872e08a03dd736592acf70e4fa6bb2f527e6d36` |
| `Blueprint/D5/.../GribinskiDegreeThreeDiscriminant.md` | `35b7cfaa233ecb061c34bab0620ec8e3de4b597d` |

Each `git cat-file -e origin/dev:Golden/Frozen/state/D5/S3/Zeros/Convolution/<target>.lean.json` exited 128 with `fatal: path '...' does not exist in 'origin/dev'`.

The required precedent command
`git cat-file -e origin/dev:Golden/Frozen/state/D5/S3/Zeros/Convolution/GribinskiDegreeTwo.lean.json`
exited 0. Its state is:

```json
{"statement_id":"sha256:184c298cb6b3a6b32640e84511f41eede52d8d0d29ae2b24a68f14ef5722487e"}
```

Its Lean header has `anchors: []` and `utility: none`. Both m=3 modules also have line 5 `anchors: []`, line 6 `utility: none`, and line 7 `digest:`. This matches spec A5.1's literal `none` grammar and required position. Generality is I for the main module and G for Discriminant.

## Execution Record

Expected cover-leg result, registered before execution: placeholder `ATOM_ID` has no ledger entry, so `COVER_INVALID` and nonzero exit are expected after canonical freezing. No retry or anchor fabrication will be used to disguise that result.

Raw command logs and final runner artifacts reside in `/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/gribinski-m3-deposit-0909/attempt-1`.

## Step 2: Directory Capacity

Step 1 commit `373dbf00bf` was pushed successfully.
Source read: `tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs:68`
sets `DirectoryFileLimit = 48`; line 87 sets repository tolerance 96.
`IsCapacityExcluded` at lines 100-110 excludes both accepted events and
`FrozenStatePath.IsUnderRoot(path)`. `CapacityPathsByDirectory` groups
nonexcluded files by immediate parent, not recursively.

Direct regular-file enumeration of
`Golden/Frozen/state/D5/S3/Zeros/Convolution/` gives **12 before + 2 = 14 after**,
with arithmetic headroom **34** against 48. Its actual SL-003 counted occupancy
is **0 before and after**, because state pins are excluded. Thus the arithmetic
comparison is not misrepresented as a binding state-directory cap.
The report directory has 10 direct files including this new report, below 48.
Collection: Ruby `Dir.children`, filtered with `File.file?` at the immediate
parent; no directory or budget change was made.

Both modules already contain their `#print axioms`
commands (12 main-module theorems and 14 discriminant-module theorems), so the
make build can expose these readings without editing a Lean file.

## Admission Record (Inherited Review, Landing Form Rechecked)

Let A be `D5/S3/Zeros/Convolution/GribinskiDegreeThree`, B be
`D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant`.
`F` below is the direct protected-base frozen declaration
`D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeSix.cubic_nonnegative_factorization`,
statement_id `sha256:984112c0a61e8d34b039bb6d01a1e73d4e1f57b7fb36b42fbd569cc818100618`.
This identity was read from accepted event
`07b22eef3e97f44d5239919946fe29c4fd7c178181c8c8931583f91c704c1d77.json`;
the module pin is separately `sha256:c432340052440ba09b56af8739b2dee5b23e520877aa3593410b92b1dbad9daf`.
Pinned Mathlib declarations are not counted as frozen GIDs.
Classification is for this joint first-freeze delivery relative to immutable
base `b9ad72010f6473b22e7616958a7e78db6fe0d2e2`, where A and B are both unfrozen.
The mechanical order will freeze B before A to place its dependency first;
this does not reopen the supplied mathematical admission assessment.

`W` denotes B's `ordered_coeff2_nonneg` / `ordered_coeff3_nonneg`, using the
weighted-square construction (20 squares and 767 positive monomials across
the four coefficient decompositions). The supplied independent review passed
all four clause 3.2 witness conditions: elaborated dependency closure,
non-bind-only content, non-equivalence to the final statement, and live use
after reduction. This worker does not rerun that mathematical review.

| Public theorem | proof_shape | Direct frozen dependencies at protected base | escape_witness | admission_basis |
| --- | --- | --- | --- | --- |
| A.definition_consistency | bind-only | none | none | escape-witness (named companion) |
| A.convolution_coefficients | bind-only | none | none | escape-witness (named companion) |
| A.m3_explicit_coefficients | bind-only | none | none | escape-witness (preregistered Step 2 companion) |
| A.weight_pos | bind-only | none | none | escape-witness (preregistered Step 3 companion) |
| A.m3_nonnegative_coefficients | bind-only | none | none | escape-witness (named companion) |
| A.nonnegative_rootTriple_coordinates | bind-only | none | none | escape-witness (named companion) |
| A.m3_discriminant_nonneg | content | none | W through B.ordered_numerator_nonneg | escape-witness |
| A.m3_nonnegative_roots | content | F (GID and declaration identity above) | W through A.m3_discriminant_nonneg | escape-witness |
| B.ordered_numerator_nonneg | content | none | W on the four-coefficient construction path | escape-witness |

Companion obligations and consumer -> prerequisite edges are inherited from
`docs/reports/convolution/gribinski-m3-0909.md`: A.m3_nonnegative_roots ->
A.m3_nonnegative_coefficients and A.m3_discriminant_nonneg;
A.m3_nonnegative_coefficients -> A.definition_consistency and
A.convolution_coefficients; A.m3_discriminant_nonneg ->
A.nonnegative_rootTriple_coordinates and the ordered discriminant bridge ->
B.ordered_numerator_nonneg. A.m3_explicit_coefficients ->
A.convolution_coefficients fulfills preregistered Step 2; A.weight_pos fulfills
preregistered Step 3's weight-domain obligation. Those two are not claimed
as live escape prerequisites. There is no corresponding atom to cite.

`question_answered`: freeze the already merged fixed m=3 result, with every
real alpha > -1 and six nonnegative real roots. The earlier mathematical
preregistration is the report's "Preregistered Attempt" section under
#6494 / #6160; this lane's scope is the user-supplied deposit brief.
`dominating_theorem_search`: reused the committed prior search record per the
brief; the prior scope was D5, pinned Mathlib, Loogle and the quoted literature.
`found`: F as the factorization consumer; `not-found-in-searched-scope`: a
dominating full m=3 result. No fresh global literature or priority claim.

## Utility: none

The supplied independent review found `utility: none` valid. The declaration
statements below range over arbitrary real parameters or polynomial inputs.
Fixed degree, finite expressions, and proof normalization do not turn their
delivery semantics into bounded enumeration, a checker, numerical reduction,
or a certified finite input instance. Each reason below is statement-level;
none relies on an unrelated theorem elsewhere in the module.
All other utility fields are `not-applicable(kind=none)` in this prose only.

| Declaration | Reason for kind=none |
| --- | --- |
| A.elementaryCoeff | Symbolic signed coefficient for arbitrary polynomial and index. |
| A.weight | Symbolic falling-factorial weight with real alpha. |
| A.normalizedCoeff | Symbolic normalized coefficient for arbitrary polynomial. |
| A.convolutionCoeff | Defines the coefficient operation for arbitrary polynomial inputs. |
| A.boxplus3 | Defines a polynomial from arbitrary input coefficients. |
| A.rootTriple | Product of factors at three arbitrary real roots. |
| A.definition_consistency | Coefficient identity for every polynomial pair and allowed index. |
| A.kappa | Rational expression in an arbitrary real parameter. |
| A.rho | Rational expression in an arbitrary real parameter. |
| A.weight_values (private) | Symbolic weight identities, not numerical input certificates. |
| A.rootTriple_coefficients (private) | Elementary symmetric identities for arbitrary roots. |
| A.convolution_coefficients | Coefficient identities for arbitrary real root triples. |
| A.m3_explicit_coefficients | Symbolic polynomial identity, fulfilling the defining-formula obligation. |
| A.weight_pos | Universal parameter inequality for each allowed coefficient index. |
| A.m3_nonnegative_coefficients | Signs for every nonnegative root tuple and alpha > -1. |
| A.discriminant | Symbolic coefficient expression for an arbitrary polynomial. |
| A.nonnegative_rootTriple_coordinates | Existential coordinate representation of every nonnegative real triple. |
| A.discriminant_numerator (private) | Symbolic denominator-clearing identity for arbitrary real data. |
| A.ordered_output_discriminant (private) | Universal discriminant sign on nonnegative gap coordinates. |
| A.m3_discriminant_nonneg | Universal discriminant sign on the complete six-root real domain. |
| A.m3_nonnegative_roots | Existential root factorization uniformly over the real-parameter domain. |
| B.numerator | Symbolic cleared cubic discriminant expression. |
| B.coeff0 (private) | Symbolic constant coefficient of the parameter polynomial. |
| B.coeff1 (private) | Symbolic linear coefficient of the parameter polynomial. |
| B.coeff2 (private) | Symbolic quadratic coefficient of the parameter polynomial. |
| B.coeff3 (private) | Symbolic cubic coefficient of the parameter polynomial. |
| B.numerator_expansion (private) | Polynomial identity for arbitrary real arguments. |
| B.sumRoots (private) | Sum of an arbitrary ordered-gap triple. |
| B.pairRoots (private) | Pairwise-product sum of an arbitrary ordered-gap triple. |
| B.prodRoots (private) | Product of an arbitrary ordered-gap triple. |
| B.sos0 (private) | Symbolic weighted-square polynomial, not a concrete input certificate. |
| B.sos0_nonneg (private) | Universal real-tuple inequality for sos0. |
| B.coeff0_identity (private) | Exact symbolic identity connecting coefficient 0 and sos0. |
| B.ordered_coeff0_nonneg (private) | Coefficient 0 sign for every nonnegative real gap tuple. |
| B.sos1 (private) | Symbolic weighted-square polynomial in real variables. |
| B.sos1_nonneg (private) | Universal real-tuple inequality for sos1. |
| B.coeff1_identity (private) | Exact symbolic identity connecting coefficient 1 and sos1. |
| B.ordered_coeff1_nonneg (private) | Coefficient 1 sign for every nonnegative real gap tuple. |
| B.sos2 (private) | Symbolic weighted-square polynomial in real variables. |
| B.sos2_nonneg (private) | Universal real-tuple inequality for sos2. |
| B.coeff2_identity (private) | Exact symbolic identity connecting coefficient 2 and sos2. |
| B.ordered_coeff2_nonneg (private) | Coefficient 2 sign for every nonnegative real gap tuple. |
| B.sos3 (private) | Symbolic weighted-square polynomial in real variables. |
| B.sos3_nonneg (private) | Universal real-tuple inequality for sos3. |
| B.coeff3_identity (private) | Exact symbolic identity connecting coefficient 3 and sos3. |
| B.ordered_coeff3_nonneg (private) | Coefficient 3 sign for every nonnegative real gap tuple. |
| B.ordered_numerator_nonneg | Universal seven-real-variable inequality, with no input enumeration. |

## Step 3: Lean and Semantic Report

Step 2 commit `173b3116b0` was pushed successfully.
`make lean` exited **0** (`03-lean.log`), 12694 jobs. Cache receipt:
`status=seeded`, `method=clonefile`, project and Mathlib both warm.
Both targets actually built: B reported 91s and A 3.0s (per-target build
messages, not isolated benchmarks). `build_seconds=null`: total wall time
was not separately measured. No budget was changed.

All **26** target-module `#print axioms` outputs were read from that build log:
12 in A (8 public, 4 private), 14 in B (1 public, 13 private). Every output is
exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or additional
axiom occurs in any target declaration's report closure.

`make lean-report` exited **0** (`03-lean-report.log`),
`mode=delta changed=0 added=13 removed=0 recheck=13` (inspector cache delta,
not this PR's source delta). It includes 21 declarations in A and 26 in B,
with public counts 17 and 2 respectively. All 47 authored included
declarations appear in the utility table above; compiler-generated auxiliary
records are not additional authored declarations.

- Report SHA-256: `d27126d2d1dfa95d83ed955cb06431c801606b9870d542e2d4a6470c56789cf6`.
- Input address: `sha256:4a95dc087810d456e5530e0235258829621ff1d20a4e97a6103298b841524c7d`.
- A source SHA-256: `2394ad41b6f9f5cf3e7c25a77ee6386ba25cc0e0857fac45312bb14397fc8b7f`.
- B source SHA-256: `bcbd16debca04f7147021418b09cc0c4cbd34fc33bfd6e02db505d13cbb341b6`.

The source hashes were checked against the report's bound `source_sha256`.
This source-binding check does not recompute any previously accepted
statement identity.

The requested atom search `rg -l -P '(?:\\boxplus|Conjecture\s*3\.13)'
Meta/Digestion/atoms/sha256/` returned 16 candidates. Their headings and the
three contextual Conjecture-3.13 passages were read: the Gribinski items are
m=2 G1/G3/G4 and m=2 context; the remaining symbols belong to other topics.
No m=3 atom was found in that searched scope. GitHub #4996 was read and is
currently CLOSED; it is cited for the historical freeze/coverage discovery
gap, not represented as an open blocker or as a rule authorizing fake anchors.

Landing-form checks found no discrepancy with the supplied admission record.

## Step 4a: Discriminant Deposit

Step 3 commit `ecb9de8d8f` was pushed successfully. One invocation only:

```text
make deposit BASE=b9ad72010f6473b22e7616958a7e78db6fe0d2e2 ATOM_ID=0000000000000000000000000000000000000000000000000000000000000000 GID=D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.ordered_numerator_nonneg
```

`04-deposit-discriminant.log`: overall make **EXIT=2**, cover recipe exit **2**.
Header check passed (`DEPOSIT_HEADER_CHECKED SL-012`); emit changed 0 Blueprints.
Ledger result: `LEDGER_ALIGN selectors_considered=3818 changed=0 added=1 unchanged=3817 conflicts=0`.

```text
COVER_INVALID cover atom 0000000000000000000000000000000000000000000000000000000000000000 is absent from the ledger
PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED atom_id=0000000000000000000000000000000000000000000000000000000000000000 gid=D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.ordered_numerator_nonneg reason=COVER_INVALID cover atom 0000000000000000000000000000000000000000000000000000000000000000 is absent from the ledger
make: *** [deposit] Error 2
```

The all-zero string is only an absent placeholder argument, not an atom or
anchor claim. Canonical artifacts are retained as **frozen, uncovered** (#4996):

- State: `Golden/Frozen/state/D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.lean.json`.
- Module statement_id: `sha256:807caeaa011a567f358eeb34c99a6b586d4980176ef5f8d9a2d9352a1e5ada73`.
- Event: `Golden/Frozen/accepted/3b9fcb14bd41d3e63ec26849c419e12890e7f76ffa6b4d973a8c4bb0710f556f.json`.
- event_hash: `sha256:3b9fcb14bd41d3e63ec26849c419e12890e7f76ffa6b4d973a8c4bb0710f556f`.

Only these two canonical paths appeared in the worktree.

## Step 4b: Main Module Deposit

Discriminant commit `1faa5ec155` was pushed before starting the main deposit.
One invocation only:

```text
make deposit BASE=b9ad72010f6473b22e7616958a7e78db6fe0d2e2 ATOM_ID=0000000000000000000000000000000000000000000000000000000000000000 GID=D5/S3/Zeros/Convolution/GribinskiDegreeThree.m3_nonnegative_roots
```

`04-deposit-main.log`: overall make **EXIT=2**, cover recipe exit **2**.
Header check passed (`DEPOSIT_HEADER_CHECKED SL-012`); emit changed 0 Blueprints.
Ledger result: `LEDGER_ALIGN selectors_considered=3819 changed=0 added=1 unchanged=3818 conflicts=0`.

```text
COVER_INVALID cover atom 0000000000000000000000000000000000000000000000000000000000000000 is absent from the ledger
PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED atom_id=0000000000000000000000000000000000000000000000000000000000000000 gid=D5/S3/Zeros/Convolution/GribinskiDegreeThree.m3_nonnegative_roots reason=COVER_INVALID cover atom 0000000000000000000000000000000000000000000000000000000000000000 is absent from the ledger
make: *** [deposit] Error 2
```

Canonical artifacts retained as **frozen, uncovered** (#4996):

- State: `Golden/Frozen/state/D5/S3/Zeros/Convolution/GribinskiDegreeThree.lean.json`.
- Module statement_id: `sha256:c098e8105cd437ddf8df749c21cf1d4725ca6b74faa16e28a5a9f63fbb292c38`.
- Event: `Golden/Frozen/accepted/d1a1b810284a94bff6f773404f15c33ab1e380e438529ac99b94879b2841d6a5.json`.
- event_hash: `sha256:d1a1b810284a94bff6f773404f15c33ab1e380e438529ac99b94879b2841d6a5`.

Only these two further canonical paths appeared. No retry was performed on
either deposit.

## Step 5: Canonical Artifact Audit

Main freeze commit `c156d6afd2` was pushed successfully.
JSON parsing and state/event pairing check exited **0**; receipt:
`05-freeze-receipt.json` in the attempt directory. Each state object has exactly
the `statement_id` key and matches its event payload. Both events are schema 5
`Freeze`; A includes 21 declarations and B includes 26. Event hashes were read
from canonical artifacts, not regenerated.

The A event directly names these prerequisite event hashes:

- `sha256:07b22eef3e97f44d5239919946fe29c4fd7c178181c8c8931583f91c704c1d77` (FiniteFreeCommutatorDegreeSix, already frozen at base).
- `sha256:3b9fcb14bd41d3e63ec26849c419e12890e7f76ffa6b4d973a8c4bb0710f556f` (B, first frozen in this delivery).

B has an empty frozen prerequisite list. The newly frozen direct declaration
used by A's ordered discriminant bridge is
`D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.ordered_numerator_nonneg`,
statement_id `sha256:07b164a52c7dd72c0c5fd9ecbbf41304d9a841710d5166e612a4c5968bb012a5`.
This additional candidate dependency is distinguished from the protected-base
dependency column of the inherited admission table.

Post-deposit direct file count is **14**, arithmetic headroom **34** against
the source limit 48; capacity-counted state occupancy remains 0 (excluded).
`git diff --check b9ad72010f6473b22e7616958a7e78db6fe0d2e2 HEAD` exited **0**.
`git merge-tree --write-tree origin/dev HEAD` exited **0**, tree
`df7303f1c9dc1ed67daa9c4f11cf874bf4613d59`, at HEAD `c156d6afd2` and the original
unchanged `origin/dev`. The five added paths are exactly two state pins,
two accepted events and this report. All Lean, Blueprint, Digestion,
domain and budget paths have zero diff from baseline.

## Step 6: Preflight (One Run)

Artifact-audit commit `cf7d253a8c` was pushed before preflight.
`make preflight BASE=$(git rev-parse origin/dev)` resolved BASE to
`b9ad72010f6473b22e7616958a7e78db6fe0d2e2` and ran at HEAD
`cf7d253a8c7e7a4cc4099c93d103648b17cf1e4b`. **EXIT=0** (`06-preflight.log`).
No rerun, deadline override, budget edit or reduced test configuration.

Engineering selected 7 projects and all **4878 tests passed**, zero failures
and zero skips, with TRX execution evidence for every project. Counts by
project: Scribe.Documents 1, Truth 88, Engine 26, Scribe 465,
EngineeringScope 26, Architecture 230, StrataLint.Tests 4042.
Selftest and expected compile-failure proofs passed. Compiler diagnostics
from those deliberately failing proof projects are expected negative tests,
not rejected content rules. The final local gate, admission and
filemap-conform all passed; the gate summary reports `exit_code=0`.

Rejected rules: **[]**. Content-attributable rejection: **none**.
Host-noise rejection: **none observed in this run**. No Perl-locale,
`ENGINEERING_TEST_EVIDENCE_FAILED`, or SL-022 rejection was reported.
The two relevant nonblocking observations are retained verbatim:

```text
OBSERVED SL-031 D5/S3/Zeros/Convolution/GribinskiDegreeThree.lean: UTILITY-OBSERVED module=D5/S3/Zeros/Convolution/GribinskiDegreeThree.lean kind=none basis=none target=none semantics=unverified-by-machine
OBSERVED SL-031 D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.lean: UTILITY-OBSERVED module=D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.lean kind=none basis=none target=none semantics=unverified-by-machine
```

This preserves the boundary between machine admission and the supplied
independent utility/proof-shape review. The utility table was also checked
against the 47 included semantic-report declaration names: missing rows **[]**.
Remote required-CI results are not inferred from local PASS.

## Step 7: Pull Request

Preflight checkpoint `9081184815` was pushed successfully. The required command
was invoked once, with no `AUTO_MERGE` argument and no watch-budget override:

```text
make pr-open HEAD=lane/math/gribinski-m3-deposit-0909 MESSAGE=/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/gribinski-m3-deposit-0909/attempt-1/pr-message.md
```

PR **#6533**: https://github.com/the-omega-institute/trureturing/pull/6533
Base `dev`, head `lane/math/gribinski-m3-deposit-0909`, state **OPEN**.
GitHub's creation API returned **exit_code=0**. `autoMergeRequest=null` and
`isDraft=false` were read back. The full provenance, escape/utility tables,
freeze identities, cover failures and preflight result are in its body.

This checkpoint is committed and pushed immediately after PR creation, while
the same `make pr-open` process continues its native required-CI wait. At the
creation checkpoint the three checks were not yet reported (`missing=3`).
Its eventual overall EXIT and CI observation are written into the worker-owned
`result.json` and appended to the PR body after the wait returns. No local PASS
is substituted for remote CI, and no merge is requested or claimed.

Delivery scope: both canonical state/event pairs are on the pushed branch,
**frozen, uncovered**, and the PR is open for integration. The two modules
are not claimed frozen on dev until that PR is actually merged.
