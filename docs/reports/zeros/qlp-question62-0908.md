# Question 6.2: weak q-Laguerre-Polya differentiation

## Result and provenance

- Target: arXiv:2606.17864v1, Question 6.2; LANE #6160.
- Tier: **第一档 / first tier**: a question explicitly stated in a 2026 paper, with a short refutation and no later resolution found in the searches documented below.
- `target_proved: true`: the closed theorem `question62_refuted : Not Question62Claim` has passed Lean.
- `proof_shape: bind-only`; `escape_witness: null`.
- `admission_basis: user-authorized-bind-only-refutes` (the explicit implementation brief).
- `skill: consensus-rnd:sshx`; `producer: one codex-cli implementation worker`.
- `independent_review: ASSUMED-UNVERIFIED`. No second agent or independent Lean reviewer was used.
- Branch: `lane/math/qlp-question62-0908`; initial HEAD / gate baseline: `3ec3f3fb60565c257755640feff72210cd5ddd80`.
- Lean: `v4.33.0`; Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Module: `D5/S3/Zeros/Jensen/WeakQlpDifferentiation.lean`.
- Worker artifacts: `/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qlp-question62-0908/attempt-1` (below: `ATTEMPT`).

The first mathematical implementation was an anonymous, local-`let` bind-only probe, before creating the admission module. `bind-probe-5.log` records its successful `/usr/bin/time -l make lean`; the exact probe is retained as `ATTEMPT/Question62BindProbe.lean`, outside D5. The final theorem uses the same argument. No escape witness is claimed for the cubic construction, discriminant calculation, or contradiction.

Policy discrepancy is explicit: current `CLAUDE.md` 3.3 says refutes does not add a fourth admission basis and still requires one of 3.2's three bases. This brief explicitly directs implementation of a valid bind-only refutes. This delivery follows that task-specific authorization; it does **not** claim an escape witness, an upstream theorem already proving the whole target, or a pre-registered atom-required bridge. Passing SL-031 certifies the bounded formal relationship, not that soft policy interpretation.

## Paper verification

Independently downloaded the [v1 PDF](https://arxiv.org/pdf/2606.17864v1) and [v1 HTML](https://arxiv.org/html/2606.17864v1) on 2026-09-08. Both returned HTTP 200; the PDF has 12 pages. Title, authors (Dimitar K. Dimitrov and Boris Shapiro), and date (16 June 2026) match the brief. Page numbers below are the printed PDF pages. Quoted mathematics is transcribed into LaTeX; wording and numbering are preserved.

1. **Page 12, Question 6.2:**

   > Is $LP_q^w$ closed under differentiation? Equivalently, if $B_q f\in LP$, must $B_q(f')\in LP$?

2. **Page 3, equation (1.6):**

   > Given a real entire function $f$ written as in (1.3), define its normalized $q$-Borel transform by

   $$(B_q f)(z):=\sum_{k=0}^{\infty}a_k\frac{q^{k(k-1)/2}(1-q)^k}{(q;q)_k}z^k.$$

   Equation (1.3), p. 2, is $f(z)=\sum_{k=0}^{\infty}a_k z^k/k!$. On p. 2, $(a;q)_n=\prod_{j=0}^{n-1}(1-aq^j)$ and $(a;q)_0=1$. Hence for ordinary polynomial coefficients $c_k$, the image coefficient is $c_k k! q^{k(k-1)/2}(1-q)^k/(q;q)_k$. The Lean definition includes exactly that factorial and finite product.

3. **Page 3, Definition 1.1:**

   > For fixed $q\in(0,1)$, the weak $q$-Laguerre–Pólya class is

   $$LP_q^w:=\{f\text{ real entire}:B_q f\in LP\}.$$

These three readings agree with the orchestrator's definitions. In particular, the weak class is the coefficient-side **inverse image**, not the image class.

## Literature search

These are independent worker searches on 2026-09-08. In the inspected scope, no later paper claiming to solve Question 6.2 was found. This is a **search conclusion, not a proof that no answer exists**. arXiv API searches cover indexed metadata; they are not exhaustive full-text searches.

| Service and query | Observed result | Receipt under ATTEMPT |
| --- | --- | --- |
| arXiv API, `ti:"Weak and strong" AND all:"Laguerre"`, max 20 | 1 result: original v1 | `search-arxiv-title.xml` |
| arXiv API, `all:"q-Borel" AND all:"Laguerre"`, max 100, newest first | 1 result: original v1 | `search-arxiv-qborel.xml` |
| arXiv API, `all:"closed under differentiation" AND all:"Laguerre"`, max 100 | 0 results | `search-arxiv-question.xml` |
| OpenAlex, search `"q-Borel" differentiation`, first 10 | total 50; inspected first 10; original paper and unrelated works, no resolution claim | `search-openalex-qborel.json` |
| OpenAlex, same query, `from_publication_date:2026-06-16`, max 100 | 2 results: original and unrelated M-estimators paper | `search-openalex-recent.json` |
| OpenAlex, `cites:W7165220176`, max 100 | 0 citing works | `search-openalex-citing.json` |
| Crossref, title as `query.bibliographic`, first 5 | 5 older/unrelated matches, no resolution claim | `search-crossref-title.json` |

Google title and DuckDuckGo question searches returned verification/challenge pages, so they are not counted as negative search evidence. Bing RSS for q-Borel returned irrelevant generic Q results and is likewise excluded. Raw responses are retained. The literature review remains bounded by indexing, result ranking, and access limitations.

## Collision and upstream checks

The original `origin/dev` search was pinned at `da39f6f761f0773daa081ba238f5d30e2e29feb8`; the remote-tracking ref subsequently advanced during the session. The following PCRE commands preserve the original readout and expand it to both requested subtrees. Counts are matching **lines**, with distinct file counts shown separately.

```sh
git grep -Pn '(qBorel|q_borel|Laguerre.?P(o|ó)lya|LaguerrePolya)' origin/dev -- D5
git grep -Pn '\bnormalizedJensen_degree_lowering\b' origin/dev -- D5
git grep -Pn '(qBorel|q_borel|Laguerre.?P(o|ó)lya|LaguerrePolya)' da39f6f761f0773daa081ba238f5d30e2e29feb8 -- D5/S3/Zeros/Jensen
git grep -Pn '\bnormalizedJensen_degree_lowering\b' da39f6f761f0773daa081ba238f5d30e2e29feb8 -- D5/S3/Zeros/Jensen
git grep -Pn '(qBorel|q_borel|Laguerre.?P(o|ó)lya|LaguerrePolya)' da39f6f761f0773daa081ba238f5d30e2e29feb8 -- D5/S3/Zeros
git grep -Pn '\bnormalizedJensen_degree_lowering\b' da39f6f761f0773daa081ba238f5d30e2e29feb8 -- D5/S3/Zeros
```

Each negative-target query: **1 line / 1 file**, `JensenPolynomialObstruction.lean:12`, a search comment only; **0 related declarations**. Each positive control: **2 lines / 1 file**, `NormalizedJensenDegreeLowering.lean:108,142`. Both query families use `-P`, including the word-boundary positive control. No `-E` command was used. Reading the Jensen obstruction module found no q-Borel transform or answer to this question.

An expanded case-insensitive search was also run:

```sh
git grep -Pn '(?i)(q[-_ ]?borel|laguerre|q[-_ ]?pochhammer|q[-_ ]?factorial)' da39f6f761f0773daa081ba238f5d30e2e29feb8 -- D5/S3/Zeros
```

It returned **4 lines / 3 files**: the same comment and three ordinary descending-factorial identities (including substring matches inside `eq_factorial`). No related declaration was found. The same `Zeros` positive control above returned 2 lines.

Pinned Mathlib search:

```sh
rg -n -P '\b(qPochhammer|q_pochhammer|qFactorial|q_factorial|qBorel|q_borel)\b' .lake/packages/mathlib/Mathlib
```

Result: **0 hits**, EXIT 1. Contrary to the brief's library availability expectation, `Mathlib/RingTheory/Polynomial/Pochhammer.lean:34` lists `q-factorials, q-binomials, q-Pochhammer` under TODO. Existing ordinary Pochhammer polynomials use additive rising/falling factors and cannot be substituted for $(q;q)_k$.

The matching local PCRE positive control `rg -n -P '\bascPochhammer\b' .lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Pochhammer.lean` returned **46 lines / 1 file** (EXIT 0).

Loogle endpoint `https://loogle.lean-lang.org/json`, GET parameter `q`: `qPochhammer` and `qFactorial` both returned `unknown identifier`; quoted `"q-Borel"` and `"Laguerre-Pólya"` both returned `count: 0`. Receipts: `loogle-qPochhammer.json`, `loogle-qFactorial.json`, `loogle-q-borel.json`, `loogle-laguerre-polya.json`. Reused existing Mathlib polynomial linear maps, differentiation, splitting, degree, and quadratic discriminant theorems; no q-product theorem was re-proved.

## Faithfulness and proof

The paper's $LP$ is an **entire-function** class: p. 1 defines it by limits, uniformly on compact subsets of $\mathbb C$, of real polynomials with only real zeros. Its weak q-class is the inverse image under $B_q$. The witness here is a polynomial, hence a real entire function, and its transform is again a polynomial.

For a real polynomial, classical LP membership is equivalent to all roots being real. If it splits over $\mathbb R$, the constant sequence of that polynomial supplies the compact-uniform approximation. Conversely, for a nonzero LP polynomial, Hurwitz's theorem on either open half-plane excludes nonreal zeros of the limit; zero is included by the closure convention. Mathlib's `Polynomial.Splits` expresses precisely splitting over the real coefficient field and includes zero and constants; `Polynomial.splits_iff_card_roots` gives the equivalent root-multiset-cardinality formulation. This analytic equivalence is explained in Lean comments and here, not claimed as a newly formalized analytic theorem.

If the paper's general differentiation-closure assertion were true, its restriction to real polynomials would be `Question62Claim`. Negating this necessary restriction faithfully refutes the general assertion. No approximation hypothesis, simplicity of roots, or extra assumption about LP is added to the Lean claim.

At $q=1/2$, ordinary coefficients are

$$f=1+3z+\frac92z^2+\frac72z^3,\qquad B_{1/2}f=(1+z)^3,$$
$$B_{1/2}(f')=3+9z+7z^2,\qquad\Delta=9^2-4\cdot7\cdot3=-3.$$

The proof normalizes the two transform identities, applies `(Splits.X_add_C 1).pow 3`, and specializes the assumed claim. `Splits.exists_eval_eq_zero` and `degree_quadratic` would then give a real root $x$ of the quadratic. `discrim_eq_sq_of_quadratic_eq_zero` forces $-3=(14x+9)^2$; `sq_nonneg` and `linarith only [hs, hn]` contradict this. All facts used by the final decision step are explicit.

## Per-declaration accounting

All GIDs below have prefix `D5/S3/Zeros/Jensen/WeakQlpDifferentiation.`. The only included named theorem is `question62_refuted`; the earlier self-test is an anonymous `example`. Direct frozen D5 dependencies for the theorem: **[]** (therefore no frozen GID / `statement_id` pairs). All imports are pinned Mathlib. The two identities in its proof are local facts, not private declared helpers.

| Declaration | Role and utility | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- | --- |
| `qBorel` | General transform definition; live definition dependency of the refutation; no separate computational theorem | not-applicable(definition) | null | companion of the authorized refutes module |
| `halfCounterexample` | `certified-instance`, concrete witness; used by `question62_refuted` | not-applicable(definition) | null | companion of the same refutes |
| `Question62Claim` | Unique closed Prop definition, target of `basis=refutes=gid:...Question62Claim` | not-applicable(definition) | null | the pre-existing paper question's polynomial restriction |
| `question62_refuted` | `certified-instance`; result proving `Not Question62Claim` | **bind-only** | **null** | **user-authorized-bind-only-refutes** |
| anonymous self-test | Exact transform normalization for the same witness; no public GID or independent admission | bind-only | null | companion check for that refutes |

The sole `utility:` header line is between `anchors` and `digest`, with exact `; ` separators and key order `kind; basis; result; claim`. The `refutes=gid` target equals the claim GID. This module is not labeled `none`.

Reading `UtilityDeclarationValidator.cs:319` and `tools/lean-inspector/Inspector.lean:216` shows uniqueness is checked **among included declarations matching the selected final name**, not by counting all module theorems. `includeInStatement` at inspector line 106 can include named private lemmas; anonymity/internal-detail status matters. The delivered source avoids private helpers and has one public theorem. `closedNegation` checks no universe/free/metavariables, Prop type, current-module theorem, and both theorem type and inferred proof type definitionally equal to `Not claim`. Actual inspector/gate results are recorded below, not inferred from this source reading.

The actual inspector reports **4 included declarations: 3 definitions and 1 theorem**, with `utility_refutation.is_closed_negation=true`. It binds both claim and result to source hash `sha256:61ec9452c1a31e44308922280b7b6e0733d83f8f9c8452b3b7b4f34579f69b1d`. Equation and tactic-generated auxiliary declarations are excluded. The source-bound evidence and included declaration data are retained in `ATTEMPT/utility-inspector-evidence.json`.

All four public declarations were checked with `#print axioms` in the final Lean file. Each prints exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, private axiom, numerical oracle, changed heartbeat limit, recursion limit, or altered build constant was introduced.

## Verification and delivery

All timed Lean commands were `/usr/bin/time -l make lean`, on this macOS Apple M3 Ultra worktree (28 logical CPUs, 103079215104 bytes physical RAM) with project and Mathlib oleans warm according to `LEAN_CACHE`. `jobs` below is Lake's reported job count, not a measured concurrency width; no job-count override was supplied.

| Stage | EXIT | jobs | real seconds | maximum RSS bytes | Receipt |
| --- | --- | --- | --- | --- | --- |
| Bind probe 1, failed normalization/elaboration | 2 | 12602 scheduled | 43.54 | 5955649536 | `bind-probe.log` |
| Bind probe 2, failed | 2 | 12602 scheduled | 21.87 | 2935341056 | `bind-probe-2.log` |
| Bind probe 3, failed | 2 | 12602 scheduled | 22.59 | 2939781120 | `bind-probe-3.log` |
| Bind probe 4, failed | 2 | 12602 scheduled | 20.15 | 2936160256 | `bind-probe-4.log` |
| Bind probe 5, full local-let refutation | 0 | 12602 | 22.30 | 2947596288 | `bind-probe-5.log` |
| Step 1, transform and self-test | 0 | 12602 | 21.25 | 2937028608 | `step1-lean.log` |
| Step 2, closed claim | 0 | 12602 | 19.20 | 2937552896 | `step2-lean.log` |
| Step 3, refutation and axiom prints | 0 | 12602 | 20.00 | 2995191808 | `step3-lean.log` |

The maximum across all timed attempts is **5,955,649,536 bytes**, including the failed first probe; the final successful formal module uses **2,995,191,808 bytes**. The required single-line utility header triggers Mathlib's nonfatal 100-character style warning. It was not split or suppressed, because the admission grammar requires that line and build constants must stay unchanged.

The first `make lean-report` exited 2 due to Scribe `CS0103` errors for `Lbrack` / `Rbrack`; these were corrected to existing `OpenBracket` / `CloseBracket` tokens. Raw errors are in `lean-report.log`. This was not a Lean proof failure.

- `make lean-report`: EXIT **0** (`lean-report-2.log`); subsequent workflow uses validated cached reports of the unchanged Lean source.
- `make emit`: EXIT **0** (`emit.log`, `emit-2.log`); only the new module's canonical mirror was emitted.
- Full `make gate BASE=3ec3f3fb60565c257755640feff72210cd5ddd80`: EXIT **2**, 761 s (`gate.log`). All eight engineering test projects passed (4976 tests total); selftest passed. SL-031 passed. The remaining errors were `SL-032 ... GovernanceProcessReference 'bind-only'` in Scribe prose and `FILEMAP-GENERATED-STALE-INVENTORY` because the emitted mirror was not yet indexed. The governance sentence was removed from Scribe (classification remains in this report), and the mirror was added to Git's index.
- Corrected `make gate BASE=3ec3f3fb60565c257755640feff72210cd5ddd80 GATE_ARGS=--skip-engineering`: EXIT **0**, 118 s (`gate-2.log`). It reused the preceding passed engineering suite; only narrative text and content data changed. Actual SL-031 output is `UTILITY-OBSERVED ... kind=certified-instance basis=refutes target=gid:D5/S3/Zeros/Jensen/WeakQlpDifferentiation.Question62Claim semantics=unverified-by-machine`.
- `make deposit`: EXIT **0**, with the exact command below (`deposit.log`). Header precheck passed; `LEDGER_ALIGN ... changed=0 added=1 unchanged=3699 conflicts=0`; coverage is `absorbed-closed`, with no gaps.
- Final gate after FirstFreeze, with the same immutable BASE and `GATE_ARGS=--skip-engineering`: EXIT **0**, 115 s (`gate-final.log`). SL-031, SL-008, SL-016 and filemap conformity passed; the missing-state observation is gone. The prior full engineering suite is reused, with no judge or Lean source change.

The successful local gate reports the Scribe file as a **SL-022 protected-surface change**. The underlying admission command returns 3 for that classification; the documented local wrapper returns 0 and states `content checks passed`. This is explicitly recorded, not represented as an unconditional raw admission exit of zero. The implementation brief authorizes this Scribe/documentation and deposit work. Independent review is still unverified.

The final whitespace scan reports only a blank line at EOF in the machine-generated preamble CAS blob (`git diff --cached --check`, EXIT 2). Those bytes preserve the source section boundary and its content address, so they are not hand-normalized. The same check excluding `Meta/Digestion/atoms/sha256/**` returns EXIT 0; the admission gate validates the canonical generated data.

Before ingestion, `rg -n '(2606\.17864|Question 6\.2|q-Borel|weak.q.Laguerre)' Meta/Digestion/atoms/sha256` returned 0 hits (EXIT 1), including extensionless CAS files. The deposit wrapper requires an atom argument even for a `refutes=gid` header. Following the repository's existing external-refutation source workflow, this worker added `docs/develop/theory/QLP_DIFFERENTIATION_REFUTATION.md` and ran:

```sh
make ingest BASE=3ec3f3fb60565c257755640feff72210cd5ddd80 SOURCE=docs/develop/theory/QLP_DIFFERENTIATION_REFUTATION.md
make deposit ATOM_ID=3bcfdb86c3eeef01808e84387737a1e4b1b54b336477dd95f66631b630e3d3af GID=D5/S3/Zeros/Jensen/WeakQlpDifferentiation.question62_refuted BASE=3ec3f3fb60565c257755640feff72210cd5ddd80
```

Ingestion returned EXIT 0 and created exactly two CAS atoms. The theorem atom `3bcfdb86c3eeef01808e84387737a1e4b1b54b336477dd95f66631b630e3d3af` states the negation of the entire universally quantified polynomial claim, with the exact normalized transform; it does not claim failure for every fixed q. The bibliographic/interpretive preamble atom `29f4f542eda7bfe827c98d86e152bf0497e4500b127502f9519266809bcee3e5` was read using `make atom-context` and settled by `make settle` as `nonpropositional-inapplicable`, with exact source-boundary/next-atom references and an explicit justification that no additional analytic theorem is being marked proved (`atom-context.log`, `settle-preamble.log`). This is a scope classification of introductory context, not kernel certification of the analytic correspondence. No fake atom, unrelated coverage, or unmatched placeholder was used. This post-proof bookkeeping registration is **not** claimed as a pre-registered escape witness or atom-required bridge; the admission basis stated above is unchanged.

Frozen receipts, read directly from the new writer output:

- Module statement: `sha256:d07505ba9ddd77bad38e61ac2a02e1cc2e2b8c4219fc8fa9d9e8250c61a98d6c`.
- Claim statement: `sha256:888fac8711ccebfe6bce1dcc1fa86f8cbd9f58e265f0e25807f1b68967b695a1`.
- Result statement / exact coverage target: `sha256:ae34af3106d0863c34125bdb133954ccf07fee3d32173a19fdcfa6ce152d5152`.
- Freeze event: `sha256:a398eb1fac350695fb77593a5a2f7cc6bb1a90de6709559c43058f816789c1a5`; `prerequisite_frozen_node_ids: []`.
- State: `Golden/Frozen/state/D5/S3/Zeros/Jensen/WeakQlpDifferentiation.lean.json`.

Steps **1, 2, 3 and 5** are implemented; optional step 4 is not part of this delivery.

Sequential green Lean commits were each pushed before starting the next mathematical step:

1. `e5818b5fa6`: transform and self-test.
2. `bb46dc3e57`: closed claim.
3. `d9527f00a2`: closed refutation and axiom prints.

The final documentation commit, push receipt, current gate exit, and complete changed-path list are also published in `ATTEMPT/result.json`. No PR is opened by this worker.

## Limits of the claim

The optional parameter-family theorem was not implemented. No claim is made to have solved any other question in the paper, characterized $LP_q^w$, or proved any positive closure property. No general LP analytic theory was added to Lean. The orchestrator's five rational checks and original mathematical derivation are provenance supplied in the brief; the worker's Lean builds and searches above are independent executions, but the orchestrator's mathematics is **not** counted as independent Lean review. Source fidelity and any claim of being the first solution remain `ASSUMED-UNVERIFIED` beyond the documented bounded search and mathematical explanation.
