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
