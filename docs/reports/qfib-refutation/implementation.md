# Conjecture 5.4 necessity refutation: implementation record

Skill context: `lean4`; Codex implementation worker, single implementation source,
no independent reviewer in this worker. The user supplied the candidate; this worker
independently checks the source, arithmetic, formalization and build.

## Preregistered target

Tier 1, arXiv:2605.12822v1, Conjecture 5.4, **necessity only**. The proposed
closed `claim` quantifies over all natural r, k, positive entries and b, assumes
r ≥ 2, k ≥ 1, and (k ≤ 3 OR r ≤ 3), and says unimodality implies
(some r ∣ aᵢ OR b ≤ 1 + Σ aᵢ/r). The proposed closed `result` has type `¬ claim`.
The source and literature status remain unverified at this checkpoint.

Proposed escape witness: the exact polynomial (1+q)^6(1+q^3) is unimodal,
while its parameters violate both alternatives of the stated condition.
This new numerical fact is to be used on the live path of the refutation;
positive finite instances will not be exposed as separate public theorems.
Proposed admission basis: `escape-witness`; computational use: `certified-instance`
with `refutes=gid:<claim>`, typed `claim` and `result` (spec A5.1).

Controls, before computation: k=1,2,3,4,5 must be non-unimodal; k=6,7,9 must
be unimodal. k=6 is the selected witness. No claim of a general k ≥ 6 theorem.

Success: kernel refutation, requested make/Scribe gates, no prohibited proof
devices, and PR opened. Reversal: the source or computation invalidates the
candidate. Blocked: actual Lean attempt with its exact remaining goal/error.
No theory volume, ingest, atom creation, or coverage backfill is planned.

## Workspace and first search

Base: `248a800843acf89ed184074d66a8d577fc028f99`.
Worktree: `/Users/chronoai/trureturing-qfib-unimodal`.
Branch: `lane/math/qfib-unimodal`; initially clean and based on origin/dev.
Read the complete CLAUDE.md, agents/CONTEXT.md, Lean skill and spec A5.1.

Ordered search step 1: `rg -n -i 'fibonomial|unimodal|q.?analog|log.?concav'
D5 Problems` found BoundedTimeSlice, DebSokalConjectureFourRefutation,
KarpQuadraticTruncations, and an unrelated Vatter problem. Their public APIs
are being examined; keyword hits alone are not a semantic non-reuse verdict.
`D5/S0/Certificates` has 36 files (recursive `find ... -type f | wc -l`).
The registered Certificates domain is S0 and includes kernel refutation certificates.
The existing DebSokal module confirms the seven-line `refutes=gid` header syntax.
`make help` exposes `deposit-uncovered`, the canonical no-atom entry point.

## Unclaimed

No sufficiency result, no universal family classification, no global minimality
among all parameter tuples, no exhaustive world-literature priority claim, no
independent review or successful build is claimed at this checkpoint.

## Source and arithmetic checkpoint

The fetched source agrees with the brief verbatim, including the two following
sentences. Corollary 4.3 explicitly says **"r divides a_i for some"** and the
sentence introducing Conjecture 5.4 calls it a generalization of that corollary.
Proposition 4.5 also says "a or b is even". Therefore "for any" in the conjecture
means existence of an index here. The hypothesis is explicitly an **OR**.
The abstract page lists only [v1], submitted 12 May 2026 23:44:53 UTC.
The paper's own example has k=4,r=4 and misses both smallness alternatives;
our k=6,r=3 example satisfies r ≤ 3 and lies beyond the stated k ≤ 5 search.

Independent Python exact binomial convolution, testing every possible peak:

```text
1: [1, 1, 0, 1, 1]; unimodal=False
2: [1, 2, 1, 1, 2, 1]; unimodal=False
3: [1, 3, 3, 2, 3, 3, 1]; unimodal=False
4: [1, 4, 6, 5, 5, 6, 4, 1]; unimodal=False
5: [1, 5, 10, 11, 10, 11, 10, 5, 1]; unimodal=False
6: [1, 6, 15, 21, 21, 21, 21, 15, 6, 1]; unimodal=True
7: [1, 7, 21, 36, 42, 42, 42, 36, 21, 7, 1]; unimodal=True
9: [1, 9, 36, 85, 135, 162, 168, 162, 135, 85, 36, 9, 1]; unimodal=True
```

The contrast check passed; this is an arithmetic probe, not a kernel theorem.
The first HTML text extraction failed because bs4 is not installed; the standard
library HTMLParser then extracted the math alttext and surrounding prose.

Source receipts (response-body hashes, successful readable source pages):
- https://arxiv.org/html/2605.12822v1 — HTTP 200; 578338 bytes; SHA256 `af2f74c6b8f6e21d71f9dd3698e5a37ddea3c9a2eb27d428b9f133777b82e5f9`.
- https://arxiv.org/abs/2605.12822 — HTTP 200; 40130 bytes; SHA256 `5ced24fe5b1c27d59bf14df271c2b048a26aecc74a168426b9b56e91bf6da739`.

## Library search checkpoint

Step 1 completed by reading the full public surfaces of all three D5 hits.
BoundedTimeSlice has a general ordinary-product coefficient/cardinality bridge,
but no unimodality theorem; its head/tail fibers have unit exponent weights,
whereas this problem has a stride-r factor. KarpQuadraticTruncations has general
real-shift Turan coefficient inequalities, not a q-product unimodality theorem.
DebSokal supplies a refutation pattern, not a relevant polynomial lemma.
No exact applicable D5 result was found in this searched scope.

Step 2: pinned mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`
(v4.33.0), full Mathlib tree keyword search unimodal/q-analog/log-concav:
only the Quasiconvex module mentions unimodality, as background. No polynomial
unimodality predicate was found. Polynomial coefficient identities are available,
including `coeff_one_add_X_pow`, `coeff_mul_X_pow`, `coeff_add`, and finite-sum
and finite-product identities, to be reused directly.

External queries below distinguish transport success from usable search results.
The three Google HTTP-200 responses are **INVALID queries**: redirect/JavaScript
shells with no results, hence no negative evidence. Reservoir returned the default
829-package listing, not a demonstrably filtered query: **INVALID as a search**.
Loogle returned a genuine JSON result, zero declarations named "unimodal";
this is a name-search result, not a proof of absence under arbitrary names.
- https://www.google.com/search?q=%222605.12822%22%20counterexample — HTTP 200; 91283 bytes; SHA256 `7989cecd9fdfa892a8b88de1af9d5762a0d33dc980f228a34de6a78e7e25272c`.
- https://www.google.com/search?q=%22Unimodality%20of%20q-Fibonomial%22%20conjecture — HTTP 200; 91307 bytes; SHA256 `7be0352d801b105d71e908d104b1487e75c94b45624f4c8379e75cb1417bf0f9`.
- https://www.google.com/search?q=Lean%20theorem%20polynomial%20unimodal%20q%20integer — HTTP 200; 91345 bytes; SHA256 `306bb83803caa7f03fc5023fe535746a53aaadc5c3465ba2395dd6fa85c01570`.
- https://loogle.lean-lang.org/json?q=%22unimodal%22 — HTTP 200; 111 bytes; SHA256 `0c4efbad26d15f22a78816a29798f175204dd3194db777ec0653021366268564`.
- https://reservoir.lean-lang.org/packages?q=unimodal — HTTP 200; 128624 bytes; SHA256 `e38e8ce7de151a0f01e6f414174f282c21feb4ce08ee5022482ac9594e0f81cc`.

Cache preheat: `make lean-cache-ensure` EXIT=0; `status=seeded`,
`method=clonefile`, donor `/Users/chronoai/trureturing`, clonefile_attempts=1,
mathlib/project olean states both warm, missing mathlib olean files=0.

## External search completion within the stated scope

GitHub authenticated API code search `unimodal language:Lean` returned 40 hits.
Read the retrieved source of six mathematical/program-verification candidates:
Lean's permutation benchmark uses strict array unimodality and contains sorry;
Numina's Anderson theorem concerns integrable functions and contains sorry;
automath's fiber result assumes its own unimodality implication;
vericoding's input-conditional strict list property is unsuitable;
IndepPoly supplies a Boolean list checker but no Polynomial soundness theorem;
NegativeBinomial supplies infinite probability-mass ratio lemmas, whose
coefficient `(j+i-1).choose (i-1) * p^i * (1-p)^j` is a different function.
None supplies a q-product theorem or a Polynomial coefficient unimodality API.
Mathlib Quasiconvex copies and finance/option-boundary paths were coarse-search
hits only, not opened: ASSUMED-UNVERIFIED; no non-reuse claim depends on them.
No upstream proof is transplanted. Local definitions use Polynomial ℕ and weak
adjacent coefficient inequalities with an existential peak, including the zero
tail. The binomial coefficient and shift identities are reused from Mathlib.

Literature checks: arXiv API `all:fibonomial` returned all 35 entries. Titles,
dates and abstracts were searched for counterexample/refutation/correction;
no report of this counterexample was identified. The only later-dated entry
in that query is 2605.14342, Fibonomial determinants; its abstract describes
integer determinant evaluations. Its full text is ASSUMED-UNVERIFIED.
GitHub issues query `"2605.12822"` returned zero. These are bounded indexed
searches, not a claim that no unindexed report exists. Tier-1 status is supported
by the original explicit conjecture and no proof/refutation found in this scope.

Second engine batch: DuckDuckGo is an INVALID captcha response (202).
Bing returned unrelated Poki/Windows/manufacturing results even for quoted
identifiers, so these queries are INVALID for negative evidence. Google's
basic fallback is again an INVALID redirect shell. Semantic Scholar returned
429 and is INVALID. No failed query contributes negative evidence.

Additional HTTP receipt ledger:
- https://www.bing.com/search?q=%222605.12822%22%20counterexample — HTTP 200; 116797 bytes; SHA256 `5678a09a4a4d8f9c795a5cedc85ac432d962ef2d13de6fa48543d7456283c069`.
- https://html.duckduckgo.com/html/?q=%222605.12822%22 — HTTP 202; 14218 bytes; SHA256 `cf951416656791885baf82fff3d38ff9f599a1913086a0deeeeb085567a4d3f6`.
- https://www.bing.com/search?q=%22Fibonomial%22%20%22Conjecture%205.4%22 — HTTP 200; 116246 bytes; SHA256 `17ede12be54d01f76b533ae82c92f492450ac6f486a00dfc259855d52c1a6f0f`.
- https://www.bing.com/search?q=Lean%20unimodal%20polynomial%20formalization — HTTP 200; 117035 bytes; SHA256 `80261cf698fe849e0a2bc384b453b49feb7304c6e88ba6bbd7e48d8f9a14f7f2`.
- https://raw.githubusercontent.com/leanprover/lean-eval-leaderboard/939d69c88292358adf60b124f29605215a1e422a/benchmark-snapshot/BenchmarkProblems/ProblemPermuteToUnimodal.lean — HTTP 200; 3232 bytes; SHA256 `c233283c4aa516d7c27fbe249ad9f4b37aefc02aa296185bc4cacdec64576138`.
- https://raw.githubusercontent.com/the-omega-institute/automath/60ce0a1548858b977dd8719efb939ceb3e87effe/lean4/Omega/Zeta/XiTimePart9KFoldFiberLayerCountRealrootLogconcavity.lean — HTTP 200; 743 bytes; SHA256 `ce9c815455a19284fb945953b9e0ba664a711126809c0e58f968f641db1d0f45`.
- https://raw.githubusercontent.com/project-numina/LeanTriathlon/2aede4209c203ae9901eff870744e4b77dc6173f/LiveLeanTriathlonSorry/AndersonTheorem/All.lean — HTTP 200; 1024 bytes; SHA256 `3530579a0f3019a67ce5855f0eb0ea422750ee8a812b08567e2ee7e2ec5a76fe`.
- https://raw.githubusercontent.com/alok/breakthroughs/5365082217b0aa641fdc753c4d910aded8c4c1b0/2026-07-24-erdos-attack/lean/Erdosattack/IndepPoly.lean — HTTP 200; 2868 bytes; SHA256 `1c31cbd4e6658ad9b5744d9bea50cc3ce97b811f728338234835486d163f8d4f`.
- https://raw.githubusercontent.com/Beneficial-AI-Foundation/vericoding-benchmark/387cd69996792d452ead7b0460f36ee4c5cdd148/specs/LA0020_specs.lean — HTTP 200; 2993 bytes; SHA256 `c6ee6499747d2d6f770787ed985dd67030935defc7fcf88cb7de590c36572b56`.
- https://raw.githubusercontent.com/plby/lean-proofs/1268917deaaaa0d674f651287027baa26cea9920/src/latest/ErdosProblems/Erdos1165/NegativeBinomial.lean — HTTP 200; 20687 bytes; SHA256 `0e5dbf0a873edf692b2e8034e77943c29c9a3a48fa447ee17b04620c0698da7b`.
- https://www.google.com/search?gbv=1&udm=14&q=%222605.12822%22 — HTTP 200; 91183 bytes; SHA256 `d0dee97f179e2b81783b648f02bd5f9aaad766a404422e108277174b5f502b9a`.
- https://export.arxiv.org/api/query?search_query=all%3Afibonomial&start=0&max_results=50 — HTTP 200; 50087 bytes; SHA256 `fe7c0d24da439c708c2e19b150d44f2ac6f664497feee301397b2f72d4de1c63`.
- https://api.semanticscholar.org/graph/v1/paper/ARXIV:2605.12822?fields=title,year,citationCount,citations.title,citations.externalIds — INVALID: HTTP Error 429: .
- https://api.github.com/search/repositories?q=unimodal%20language%3ALean — HTTP 200 via gh API (EXIT=0); 55 bytes; SHA256 `4af480b8ee5b87b369a76c49bd22c9a783908272ebffbe97898f8ab0f0772a5f`.
- https://api.github.com/search/code?q=unimodal%20language%3ALean — HTTP 200 via gh API (EXIT=0); 216057 bytes; SHA256 `f47507b2b64037eeb9da2531055b17405f4aa90843d1f82ad6c58829d4672a9c`.
- https://api.github.com/search/issues?q=%222605.12822%22 — HTTP 200 via gh API (EXIT=0); 79 bytes; SHA256 `c9938edecb99d754b2d039ac9eec320a94c769b6a6417921e2dcbef9e2fe01a0`.

Planned address: `D5/S0/Certificates/Polynomials/QProductNecessityRefutation`.
The existing Certificates Blueprint bucket has 70 direct files (72 recursive);
a Polynomials child holds this first real certificate and its mirrored source.
No new domain registration is needed; Certificates is already registered S0.

## First Lean implementation

Canonical route succeeded at the planned GID. Two input-contract errors were
fixed before routing: manifest must be repository-relative, and F requires
artifact=lean. The manifest lives under ignored .lake/build, not in the report.

First real Lean attempt reduced every finite inequality and failed only on the
zero tail: `i > 9 ⊢ 2 ≤ i → Nat.choose 6 (i - 2) = 0`. The simplifier had
normalized `(i+1)-3` to `i-2`, so the supplied rewrite did not match. Supplying
`6 < i-2` fixes the exact remaining goal; no mathematical assumption changed.
`family_coeff` directly applies `Polynomial.coeff_one_add_X_pow` and
`Polynomial.coeff_mul_X_pow'`. The new `six_unimodal` is private and establishes
all natural-index inequalities, not merely a truncated coefficient list.

## Kernel and semantic controls

Warm file gate `lake env lean D5/S0/Certificates/Polynomials/QProductNecessityRefutation.lean`
EXIT=0. Both claim and result have only propext, Classical.choice, Quot.sound.
The built-in Lean LSP was exercised through `lake env lean --server`, opening
the actual source: zero diagnostics, and hover at zero-based line 88, column 10
returns `QProductNecessityRefutation.result : ¬claim`. The first protocol probe
mistook a server inlay-refresh request for a hover response; it was discarded,
then rerun matching a response with no method and the correct client request ID.

The attempt-local `controls.lean` imports the real module and passed EXIT=0.
It proves non-unimodality for every k=1..5 by an actual strict fall followed by
a strict rise (indices (1,2), (1,3), (2,3), (2,4), (3,4), respectively).
It proves unimodality for k=6,7,9, including each infinite zero tail, and checks
all six coefficient lists in the brief exactly. These probes are not additional
public deposited statements. This proves the chosen witness is minimal **within
the specified all-twos, r=3, b=2 family**, not among all parameter tuples.

Pre-PR duplicate check after fetching dev at
`7fd01f41212a2b67264882e6d42802d222fe019b`:
`git grep -i -P '2605\.12822|qfibonomial|QProductNecessity|q.?product.*unimodal'
origin/dev -- D5 Problems Library` had no matches (EXIT=1).
`git merge-tree --write-tree HEAD origin/dev` EXIT=0, tree
`ac105293118980ca5c0803169f28e699b6e25e4b`. No existing source was moved or retired.

## Build and proof-shape evidence

`make lean` EXIT=0, 232.479 seconds, 12,912 jobs, on this macOS ARM worktree
with the seeded donor cache described above. This is a local build measurement,
not a CI performance claim. Full log: attempt-1/make-lean.log.

The repository `proof-edges.sh` succeeded:
`EDGES_OK edges=10 kernel_nonauxiliary_constants=7`.
Its kernel-derived live dependency path includes
`result → six_unimodal (private) → family_coeff (private) → family_eq (private)`.
The generated JSON stays attempt-local; it is not a tracked report projection.

Only public theorem: `result`.
- proof_shape: content.
- Direct frozen dependencies (GID + statement_id): none (empty set).
- escape_witness: private `six_unimodal`.
- admission_basis: escape-witness.
- Computational use: certified-instance; refutes the closed `claim`.

Four escape-witness checks: (i) the elaborated constant edges above put it in
result's transitive dependency closure; (ii) the new inequalities at the six-factor
product are established here by exact arithmetic, not projected from a frozen
premise or obtained by instantiating a pre-existing unimodality theorem;
(iii) unimodality of a specific polynomial is not definitionally equal to the
negation of the universal necessary-condition assertion; (iv) it is the actual
unimodality argument supplied to the hypothesized claim, and that specialization
is used to obtain the impossible divisibility-or-bound disjunction. It survives
reduction and is not an unused conjunct. Dropping it leaves the implication's
antecedent unproved. The coefficient/shift identities are supporting Mathlib
rewrites; no new upstream binomial theorem is claimed.

```text
LEAN_CACHE {"status":"present","worktree":"/Users/chronoai/trureturing-qfib-unimodal","donor":null,"method":"none","reason":null,"stamp_miss":null,"pin_sha256":"sha256:6c4c682ffba051b5744fe7a75ccc99d7f3b20227b3b026f392f3315be0adaa4e","clonefile_errno":null,"clonefile_errnos":[],"clonefile_attempts":0,"clonefile_cleanup_error":null,"mathlib_missing_olean_files":0,"mathlib_missing_olean_samples":[],"archive_status":"not_attempted","archive_mode":null,"archive_skip_reason":"project olean state is warm","archive_reason":null,"archive_producer_commit_sha":null,"archive_workflow_run_id":null,"mathlib_olean_state":"warm","mathlib_olean_probe_error":null,"project_olean_state":"warm","project_olean_probe_error":null}
```

## Report and locator gate

`make lean-report` EXIT=0, 64.162 seconds. Its typed utility receipt reports
`is_closed_negation=true` for the declared claim/result pair.
The first `make emit` failed EXIT=2 after 15.686 seconds: `invalid-doi`, because
LibraryNoteCatalog requires selecting DOI or URL, not both; the consequent
`dangling-literature-reference` is the same rejected note. The frontmatter now
selects the exact v1 HTML URL (`doi: null`); the actual DOI remains documented
in the nonempty Verified locator section. This is a locator-selection fix, not
a claim that the paper lacks a DOI. Rechecking follows this checkpoint.

Corrected `make emit` EXIT=0, 50.611 seconds, generated the one intended
Blueprint. Mandatory `scribe-content-checks.sh` with the original exact base
EXIT=0, 23.859 seconds: Describe `red=0`; Markdown `judged=1 formula(s)=0 red=0`.
The document uses an addressable Lean statement and prose rather than a display
formula, so the real Markdown/KaTeX check had zero formula expressions to parse.
Its source acknowledgement resolves to the versioned Library URL. The script
does not select projections for these changed paths, so `projections --check`
was also run explicitly: EXIT=0, 10.856 seconds. These gates do not claim online
verification of unrelated Library notes that the Describe tool marks OBSERVE.

## No-atom freeze

`make deposit-uncovered GID=D5/S0/Certificates/Polynomials/QProductNecessityRefutation.result
BASE=248a800843acf89ed184074d66a8d577fc028f99` EXIT=0, 84.068 seconds.
The canonical command reused the cached report, passed deposit-header-check,
emitted no changed Blueprint, then ran `ledger-align --add` for this module:
`added=1 changed=0 conflicts=0`; final sentinel has `reason=NO_ATOM`.
Freeze event: `e7223612e75583c5d1c68a6cfb9f02cbfb143ce219afcbea0206b4846ca1ab80`.
State pin: `Golden/Frozen/state/D5/S0/Certificates/Polynomials/QProductNecessityRefutation.lean.json`.
No atom or coverage edge was created; the delivery is an uncovered deposit of
the external named assertion's refutation.

The staged index passed `make -C tools capacity-audit`:
`CAPACITY_AUDIT_RESULT exit=0 reason=clean`. Final source diff has seven intended
paths and passes `git diff --check`.

After committing the freeze, the required `shapes.sh` first failed on the system
Python 3.9.6 importing `str | None` in facts.py. The inner kernel extraction had
already succeeded. Re-running the same unmodified repository script with the
installed `/opt/homebrew/bin/python3` (3.14.4) passed EXIT=0, 3.103 seconds:
`EDGES_OK edges=10 kernel_nonauxiliary_constants=7`. It lists six public definitions
and the sole public theorem `result`; its other-D5-module dependency column is
empty. That column does not count Mathlib dependencies. The generated table and
edge JSON remain attempt-local. No replacement evidence tool was written.

The script's trailing stock prose abbreviates norm_num as zero contribution;
the authoritative current CLAUDE.md 3.2 explicitly distinguishes normalization
of supplied atoms from establishing a new atomic proposition. The content
assessment above uses the latter criterion and the four witness checks; neither
the marker column nor that stock prose is treated as a machine verdict.
