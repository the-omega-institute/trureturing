# CRIM Conjecture 3: implementation record

Production: no skill; Codex implementation worker, single-agent source inspection
and checks. No independent review is claimed. User-supplied numerical values
are predictions to compare against, not computational evidence.

Worktree: `/Users/auricstudio/trureturing-robin7smooth-0909`.
Branch: `lane/math/crim-grundy-refute-0910`.
Immutable starting commit: `bf7e99c6dec64fc5d08786d6d2e4e885ef642f17`.
Date: 2026-09-10 (Asia/Singapore).
Worker artifacts: `/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/crim-grundy-0910/attempt-1`.

## Preregistration v1, before computational probes or Lean implementation

question_answered: Does the displayed r >= 7 formula in printed Conjecture 3
of arXiv:2606.16828v1 agree with the recursively defined normal-play CRIM
Sprague–Grundy value? The proposed test is r=7, k=5, with rectair
[6,6,5,4,3,2,1]. This is a first-tier recent conjecture target; the literature
check below is still being completed. Implementation must stop if a prior
proof/refutation is found or if the printed target differs from the brief.

Proposed escape_witness: the paper-specific move graph consisting of deletion
of each row and conjugate–row-deletion–conjugate column moves, together with
a verified finite-game SG/mex evaluator whose recursion descends in partition
size. A finite DAG certificate must cover every option recursively through
the terminal empty partition. The supplied prediction is 377 distinct states,
maximum descent depth 12, 12 distinct root options and root SG value 1.
These counts and option values are unverified predictions at this registration.
No list of twelve hardcoded SG constants may define the claim or replace
recursive verification. The equality mex({0,2,4,5})=1 alone is not the witness.

Planned public theorem: `result : Not claim`; the claim must quantify only
over the printed rectair formula and refer to the actual graph and evaluator.
Proposed proof_shape: content. Direct frozen dependencies: none identified.
Proposed admission_basis: escape-witness (conditional on observing a live
witness satisfying CLAUDE.md 3.2). Proposed utility: certified-instance,
refutes the module's claim. `refutes` is not an admission_basis value.
There will be no priority claim, no conclusion about other paper results,
and no assertion about an intended or repaired formula.

## Rendered source inspection

Downloaded `https://arxiv.org/pdf/2606.16828v1` (659535 bytes) and the current
abstract page. Rendered PDF pages 4, 5, 6, 8 and 18 with PyMuPDF and visually
inspected the PNGs, not only the extracted text. Images and text are retained
in the worker artifact directory.

| Item | Printed reading | Comparison with brief |
| --- | --- | --- |
| Rectair, p. 5, section 2.2 | R^k_{r,c} = [c^{r-k}, c-1, ..., c-k] | matches |
| Domain, p. 5 | r,c positive; 0 <= k < min(r,c) | retained |
| Conjecture 3 argument, p. 18 | R^k_{r,r-1} | matches |
| Exceptional condition | k=r-2 and r odd | matches |
| Exceptional value | 3 | matches |
| Otherwise value | 1 | matches |
| Stated range | r >= 7 | matches |
| Row move, p. 8 | Remove part i, 1 <= i <= r | matches |
| Column move, p. 8 | Conjugate the result of a row move on the conjugate | matches |
| Empty parts, p. 4 | Parts are positive; the only partition of 0 is [] | zero rows/columns are absent |
| Play convention, p. 6 | Normal play; terminal ordinary SG is zero | retained |

Page 2 also states that the remaining pieces reattach after deletion. Page 18
has surrounding assertions about small rectairs; the target here is exactly
the displayed r >= 7 formula. The preceding prose mentions R^k_{r,r+1}, while
Conjecture 3 itself prints R^k_{r,r-1}; the displayed conjecture is the target.

## Ordered reuse and bind-only check

1. D5: `git grep -n -P '\b(Grundy|mex|Sprague|CRIM)\b' -- 'D5/**/*.lean'`
   returned three comment occurrences, all in ComplementaryGoldenRatioLimit.
   Positive control with the same PCRE word boundaries, `\b(theorem|def)\b`
   on TripodNimPeriodRefutation, returned its actual declarations.
2. Pinned Mathlib is v4.33.0, commit
   `db584cd6d46c92f209a44c0f1c829460d327499d`.
   Whole-Mathlib PCRE `\b(mex|PGame|Sprague|Grundy)\b` found only three
   explanatory mex comments in Cardinal/Basic and Ordinal/Basic. No
   `SetTheory/Game` files, `PGame`, named `Nat.mex` or `Ordinal.mex` API were
   found. Nat.Partition exists in Combinatorics/Enumerative/Partition/Basic:
   it bundles positive Multiset parts and their sum, including ofMultiset
   and ofSums (which removes zero parts). Multiset.erase and its strict
   decrease theorem are available. Finset.strongInductionOn and lt_wf are
   available in Data/Finset/Card. These do not supply the CRIM graph or SG
   value. One initial Multiset/Order path probe failed because that file
   does not exist; the successful AddSub read supplies erase facts.
3. GitHub repository discovery and Reservoir located
   `vihdzp/combinatorial-games`. Inspected its tree at
   `a087fede837fa7f4ee6a2ffb2c6560a3112d4d6d`, Graph.lean,
   Impartial/Grundy.lean and Specific/Nim.lean. This library has GameGraph,
   well-founded moveRecOn, toIGame, and IGame.grundyAux / Impartial.grundy.
   These are noncomputable and use nimbers and infima of complements.
   Its current toolchain is v4.34.0-rc2. The inspected tree has no CRIM or
   partition-specific game. Reservoir lists older builds too; a toolchain
   mismatch alone is not the reason for declining reuse. The missing work
   remains the CRIM graph and an executable finite evaluation certificate.

No exact theorem or direct graph/evaluator instantiation establishing this
counterexample was found in these scopes. Instantiation, frozen projections,
and normalization alone do not discharge the required recursive computation.
Thus the initial bind-only attempt did not close the target. No Lean module
has been created at this registration.

## Literature status, in progress

The current arXiv abstract page lists only v1, submitted
15 June 2026 15:09:22 UTC. The rendered v1 retains Conjecture 3 above.
OpenAlex exact-title query returns two records for this same preprint,
W7164942864 and W7165064556; both have cited_by_count=0 and neither is
accepted/published. Crossref query.title, first five results, has no exact
title match. These are bounded observations, not proof of absence.

The OpenAlex CRIM/Grundy query also found supplementary artifacts for
"Losing positions of CRIM for partitions with at most six parts"
(Zenodo 22070743/22070744); their contents and MathDB's rectair entry are
being checked before numerical or Lean work. Google returned challenge
pages, DuckDuckGo a challenge, Brave HTTP 429, Yahoo HTTP 500, and Bing
irrelevant results. None of those failures counts as a successful negative
search. The actual MathDB site is mathdb.com; mathdb.org is unrelated.
