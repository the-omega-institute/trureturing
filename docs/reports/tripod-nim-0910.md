# Tripod Nim preregistration v1

Production: no skill; single Codex implementation worker; no independent review claimed.
Target: printed Conjecture 2, arXiv:2401.07943v1, literature-attested.
Tier: recent small conjecture; literature status pending verification.
question_answered: Does every periodic orbit of the paper’s D(3,n) have minimal period dividing its printed expression?
Proposed proof_shape: content, subject to failed bind-only attempt and source/literature checks.
Proposed escape_witness: a faithful finite transition semantics for §9.3 and an explicit correctness bridge to a bit-vector evaluator; live certificates must establish the 264-step return and nonreturns at 24, 88, 132 from the transition itself. Endpoint numeral arithmetic is not the witness.
Proposed admission_basis: escape-witness.
Proposed utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/TripodNimPeriodRefutation.claim; result=D5/S0/Certificates/TripodNimPeriodRefutation.result; claim=D5/S0/Certificates/TripodNimPeriodRefutation.claim
Direct frozen dependencies: none identified; Mathlib is not a frozen D5 dependency.
Scope: one periodic orbit; no 109-step initial-state reachability proof.
Stop conditions: mismatch in printed formula or transition rules; already proved or formally refuted in literature; successful bind-only proof; inability to complete reported honestly.
No computation of the proposed orbit has been performed at registration time.

Registered UTC: 2026-09-10T10:40:53.454867+00:00


## Source check before implementation
Rendered PDF pages 28 and 30 independently inspected. The printed formula is 2(4n)(4n+1), with orbit period dividing it. Remark 9.2 says n ≤ 9. Section 9.3 defines k rows of 2n+k bits, lower rows corresponding to smaller entries. First shift left and fill the right column with zeros; for each row whose harvested bit was zero, in bottom-to-top order replace the leftmost eligible zero by one. The leftmost n columns are excluded, and only additions made in the current transition prohibit reuse of a column. Bit 0 = leftmost is our encoding convention, not a numbered bit convention asserted by the paper.
ArXiv abstract page lists only v1, 15 January 2024. Further literature checks pending.

## Initial reuse receipts
1. D5: git grep -n -P '\b(Grundy|nim|Sprague|Tripod|Hennessey)\b' -- 'D5/**/*.lean': exit 1, no matches. Same-boundary positive control '\bCatalan\b': exit 0, 15 files.
2. Pinned Mathlib db584cd6d46c92f209a44c0f1c829460d327499d (v4.33.0): same mathematical name scan has no matches. Dynamics/PeriodicPts/Defs.lean provides IsPeriodicPt, minimalPeriod, IsPeriodicPt.minimalPeriod_pos, IsPeriodicPt.minimalPeriod_dvd and isPeriodicPt_iff_minimalPeriod_dvd. Logic/Function/Iterate.lean supplies Nat.iterate, iterate_succ_apply, iterate_succ_apply', iterate_add_apply. These remove the need to reprove general iteration and minimal-period theory, but provide no D(k,n) evaluator facts.
3. GitHub repository query 'tripod nim lean': 0 repositories. Query 'combinatorial games lean': vihdzp/combinatorial-games, Happyves/Lean_Games, t4ccer/misere-games; contents not yet inspected.
Bind-only status: no closure established; remaining obligation is transition semantics and evaluator correctness, not divisibility arithmetic. No D5 module has been created at this stage.


## Independent exact computation
After the rendered source check, method A uses Boolean arrays, slices off the left column, and scans permitted columns with a set recording this transition's insertions. Method B uses packed integer rows, shifts right by one (bit 0 represents the left column), and selects the lowest available bit with `available & -available`. Rows are bottom to top. Both start at (1,2047,2042); neither uses the supplied endpoint values. All 264 successive results agree and the only return in steps 1..264 is step 264. No floating point; no initial-state reachability calculation.

| Steps | Boolean arrays | Packed words |
|---|---|---|
| 24 | (1024, 2047, 1021) | (1024, 2047, 1021) |
| 88 | (1, 2038, 3464) | (1, 2038, 3464) |
| 132 | (1, 2014, 2082) | (1, 2014, 2082) |
| 264 | (1, 2047, 2042) | (1, 2047, 2042) |

Script and complete orbit: worker-owned attempt directory `compute.py`, `computation.json`. These are independent implementations by one worker, not independently authored or reviewed computations.

## Bounded literature and ecosystem review
The arXiv submission history retrieved during this attempt lists only [v1], Mon, 15 Jan 2024 20:15:55 UTC. Rendered source is the v1 PDF. The title-page date is distinct from the arXiv deposit date.
OpenAlex title query returns only W4390962538, arXiv submittedVersion, not accepted/published, cited_by_count=0. Crossref query.title (top five) gives no exact title. Brave exact-title query returns only arXiv abstract/PDF. No published proof, refutation or formal correction was located within these successful queries. This is a bounded non-finding, not a claim that none exists. Google and DuckDuckGo returned challenges; Bing returned unrelated results and is not counted as a successful negative search; Semantic Scholar returned HTTP 429. Some further Brave queries returned HTTP 429. The supplied MathDB reader-written, unverified computation has not been independently retrieved and was not used as computational evidence. No priority claim.
Third-party Lean: vihdzp/combinatorial-games HEAD a087fede837fa7f4ee6a2ffb2c6560a3112d4d6d contains standard ordinal/nimber Nim and Sprague–Grundy infrastructure; the inspected Specific/Nim.lean defines a single-heap game, not D(k,n). Happyves/Lean_Games at 66f6f0599b53cdd86c6ccc7000f0f76ecf83591d and t4ccer/misere-games at 8fffccecc75399358e3155e36e8742a78bc82eaa have no paths matching Nim/Tripod/Grundy/Sprague. Repository and path queries are screening evidence, not an exhaustive semantic proof of library absence.
Initial bind-only attempt outcome: no proof obtained from the located declarations. General period arithmetic is available; the paper-specific transition and its evaluator bridge remain missing from the inspected libraries. Proceeding under the preregistered content hypothesis.

Report correction: the arXiv submission time has now been read directly from archived HTML: 20:15:55 UTC. The earlier unverified time placeholder was incorrect and is withdrawn.


## Implementation and observed proof shape
Only public theorem (included declaration counts checked separately below): `D5/S0/Certificates/TripodNimPeriodRefutation.result`.
- proof_shape: content.
- Direct frozen dependencies (GID + statement_id): [] (none; only Mathlib imports).
- escape_witness: The local `runRows_correct` proof inside `result` proves by induction on rows that decoding the bit-vector row processor gives the literal Boolean-row processor, using `read_shift` and `read_insert`. `evaluator_correct` supplies the semiconjugacy and `decode_injective` reflects nonreturns. Four new kernel evaluations establish return at 264 and nonreturns at 24, 88, 132 on the live proof path. No checkpoint endpoints are definitions or hypotheses of the claim.
- admission_basis: escape-witness.
- utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/TripodNimPeriodRefutation.claim; result=D5/S0/Certificates/TripodNimPeriodRefutation.result; claim=D5/S0/Certificates/TripodNimPeriodRefutation.claim

Proposed versus observed: the preregistered finite transition, evaluator bridge and four iteration certificates are all present. The implementation uses an absorbing `none` only when the paper's insertion rule has no legal column; all returning present boards have defined steps. This makes no extra default move. This is a representation detail within the original witness, not a replacement witness. Generic minimal-period and iterate results are reused from Mathlib. The finite divisor check and 264 ∤ 3280 arithmetic are not asserted as the escape witness. Auxiliary mathematical proofs are local `have` statements inside `result`; data operations are private definitions. `runRows` uses a fold returning a continuation, which processes the first (bottom) row before its continuation. `claim` is the only closed Prop definition and `result` the only source-level theorem. Inspector verification of the exact included count is recorded below. No reachability segment, axiom, sorry, native_decide, deposit, cover or PR is introduced.

`make lean` run 3 exited 0, 12912 jobs. Claim and result both report exactly [propext, Classical.choice, Quot.sound]. Run 1 failed on an incorrect Mathlib import path; run 2 found two bit-index proof obligations; run 3 resolves both. The earlier error builds' inserted diagnostic sorryAx terms are not accepted proofs; only the successful run is evidence. The final source contains no sorry. Logs are in the attempt directory. Blueprint and gate verification still pending at this checkpoint.

## Exact source anchors
Printed text: “Every periodic orbit of D(3,n) has a period which is a divisor of 2(4n)(4n+1).” Formula parentheses and divisor direction were checked visually on printed page 30. Page 28, §9.3 is the transition source. First n columns means indices 0 through n−1 in our convention, so index n is eligible. A logical left shift is an integer right shift because bit 0 is the left column. Simultaneous column exclusion concerns newly added ones only. For k=3 and n=10 the width is 23. The full checklist has no mismatch.

PDF SHA-256: 0ad5c4442051e5ff5fcff63ce85bfb9c3773199512e7c5597809a8abba31cebd


## Included-declaration correction
The first successful `make lean-report` exposed that this repository includes private helper theorems in statement identity. The first implementation therefore did not yet satisfy the required included-theorem count, despite its successful Lean build. The auxiliary proofs have now been moved inside `result`, and the recursive row processor expressed by `List.foldr` to avoid generating a separate equation theorem. No inspector code or name-filter rule is changed. This preserves the preregistered mathematical witness and the row-processing order; it only changes the representation and proof scope. `make lean` run 5 exited 0 (12912 jobs); its claim/result axiom lists are exactly [propext, Classical.choice, Quot.sound]. Run 4 exposed an induction-hypothesis unfolding issue introduced by the fold refactor; run 5 fixes it. The fresh semantic report is still running at this checkpoint.


The second semantic report confirms exactly one included theorem, `result`. Its absent utility evidence revealed a strict-header formatting error: `digest` must close the standard header on the same line. The required proof-shape annotations are now in a separate adjacent header comment. The canonical `lean-utility-input` command now emits the correct claim/result obligation. `make lean` run 6 exits 0; a new report will verify the typed evidence. No parser, admission rule or producer has been edited.
