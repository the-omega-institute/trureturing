# Relative prime spread: S17 paper proof and verification provenance

This report accompanies Section 28 of
[ARITHMETIC_BOUNDARY_QUANTIZATION.md](../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md).
It records the C33 / S17 implementation candidate, its completed primary input,
and the caller's existing fixed verification. The remaining mathematical gap is
the sign of \(G\) at unbounded common height within the bounded relative-spread region
for a fixed set of three distinct primes. This report does not incorporate the later
common-height or balanced-all-slab primaries.

## Production and trust boundary

- Context: caller-owned `consensus-rnd:sshx`, repository `CLAUDE.md` §5.11;
  delegated Codex CLI implementation worker I12, flight
  `qgh0910-i12-relative-spread`, attempt 1. The worker consulted the local sshx
  skill at `1.0.0-beta.43/skills/sshx/SKILL.md`; that is a consulted skill version,
  not an independently verified statement of the caller's runner version.
- Work target: `/Users/auricstudio/trureturing-qgh-variance`;
  branch `lane/math/quantized-gh-relative-spread-0910`;
  immutable implementation BASE `feb497ec31f68e09ccc547a08810c398e66f3ee6`.
  Repository: <https://github.com/the-omega-institute/trureturing>.
- The worker read `CLAUDE.md` and `agents/CONTEXT.md` completely and inherited
  the complete supplied seven-field GoalArtifact, including C1-C34, S1-S17,
  harness and revisions: `repo-prior-exposed`. The repository guidance and
  caller brief are visible context, not sterile priors.
- Mathematical primary: task `aaaf57ba-7b72-4143-b830-b4b58fe7fc2c`, conversation
  `conv_576df749336210e9`, observed model **GPT-6 Astra**. These task/conversation/model
  associations are supplied by the caller's dispatch; I12 did not independently
  query the browser service. The primary identifies its role as primary research,
  not independent review. Its `proved` verdict is a paper claim, not kernel admission.
- Primary prior disclosure: `external-prior-exposed`; account/project context is
  unknown and uncontrollable, with sterile context unverified. Its attempted
  pinned theory and finite-design URL fetches returned `DisabledError`.
  Exact repository source/report fidelity was therefore `ASSUMED-UNVERIFIED`
  in that primary response. It rederived support, separation, saturation and tail
  facts from supplied mathematical definitions rather than depending on the
  inaccessible finite-maximum argument. Local I12 checks do not rewrite that
  historical access limitation.
- Mixing: a completed primary conclusion plus the completed caller audit are
  fallible implementation inputs; I12 supplies paper exposition and local checks.
  These are not independent review votes or evidence of model-family diversity.
  No peers, children, new oracle invocation, live neighboring target, worker logs
  or dereferenced `log_ref` contents are inputs. The optional S16 snapshots were
  not needed: this worktree contains the sealed S16 source itself.
- Caller retains Git/PR ownership. I12 does not stage, commit, push, create branches,
  merge, publish, or change repository policy.

## Immutable inputs

| Input | Identity | Use |
| --- | --- | --- |
| Sealed theory prefix at BASE | 201529 bytes; 3627 LF-terminated lines; SHA256 `b7cb35d87d0a7b7e569c49ab57f2b556c454257de8bd65899587d13be1338537` | Preserve every byte and append Section 28 |
| `/tmp/qgh-boundaries-0908/pro-relative-prime-spread-envelope-0909.json` | 17289 bytes; SHA256 `7d0bddfc1fcf761290f7bf777663f52f07af927eb2832001a67ff509bdeb4f11` | Read only its conclusion as the primary paper input; do not open its log reference |
| `/tmp/qgh-boundaries-0908/caller-relative-prime-spread-audit-0909.json` | 2299 bytes; SHA256 `493e5f8d2432469936611f95c5d34a42ea5463bb1b29188e827b135ac14b4c47` | Preserve the existing 11 fixed symbolic checks and paper audit |

The raw primary has literal escaped nonnegative-integer notation in two prose
strings. Section 28 typesets ordinary \(\mathbb Z_{\ge0}\); the immutable raw input
is neither normalized nor rewritten. The earlier caller phrase about excluding
\(G<0\) was a sign-wording error corrected by the primary and the audit before this
implementation: the small-coordinate hypothesis **proves \(G<0\)** and **excludes
\(G\ge0\)**.

## Exact mathematical scope and source map

The continuous theorem fixes positive steps with eight distinct subset sums,
\(T\ge\log2\), \(0\le s\le S\), \(t\ge s\), and
\(c=(T,T+s,T+t)\). Slabs have finite real budgets,
\(Q+\log5040<M_0<M_1\), and at least two actual corners in the closed budget
interval. The same primal \(D\), distance normalization \(\rho^2=\sum\delta_i^2/6\),
\(L=\mu-\rho\), \(H=\mu+2\rho\), and \(G=D-f(H)-2f(L)\) are retained.

Section 28.3 retains the primary constants exactly (the source's \(K\) is the
payload's \(K_W\)):

\[
K=\frac{(S+4Q)^2+(2S+4Q)^2+(S+Q)^2}{9},\quad
\epsilon=\delta/18,\quad a=e^{-(S+Q)/2}(1-e^{-\epsilon}),
\]
\[
R=1+\max\left\{2S+3Q,\sqrt{6K},9K/\delta,
\tfrac32(S+Q)+3\log\!\frac2{1-e^{-\delta/18}}\right\}.
\]

For \(t\ge R\), every admissible slab satisfies \(e^TG<-a<0\).
The margin remains strict at \(t=R\); the constants are independent of common height.

| Source units | Faithfulness and proof obligations covered |
| --- | --- |
| 28.1-28.3 | Paper/reference status, exact hypotheses, closed corners, strict cutoff, explicit unchanged constants |
| 28.4-28.5 | Positive support including zero variance; nonstrict lower-budget monotonicity; second-largest-corner saturation; exact empty-domain condition |
| 28.6 | Geometry throughout saturated finite intervals with \(M_1\le A+Q\); strictly nearest endpoints \(d_1,d_2,c_3\); no claim of this geometry on the unbounded tail |
| 28.7 | Exact rationalized remainder, zero iff \(W_\perp=0\), and denominator at least \(2t>0\), independent of \(T\) |
| 28.8-28.9 | Primal resource bound, both \(q\le h_1+h_2\) and \(q\ge h_1+h_2\) cases, agreement at equality, \(L\ge m_{\rm low}+\delta/18\) |
| 28.10-28.12 | Integral bounds, strict margin at the rounded real threshold, all intermediate upper budgets, and a separate strict upper-tail monotonicity proof |
| 28.13-28.14 | Unique factorization, label permutations, corrected small-coordinate exclusion, and fixed-prime relative spread \(<R\) as a necessary condition for any \(G\ge0\) |
| 28.15-28.16 | Nonzero nonnegative integer rays, \(\Delta>0\), exact ceiling \(N\), no order-stabilization condition, cutoff equality and vacuous empty-domain cases |
| 28.17-28.19 | Infinite remaining geometric family, unbounded height, classical attribution, evidence provenance and caller-owned remaining delivery |

The positive-support proof in 28.4 uses the same box lower bound already proved in
27.5, with the corner mean in the interval; it also states the weaker primary
triangle-inequality estimate. This supplies the necessary self-contained fact
without reproducing the earlier general-dimensional derivation. The finite-range
proof controls every saturated interval directly, so no general finite-maximum
proof, optimizer construction, or numerical critical-node enumeration is needed.

For a fixed unordered prime triple, take \(S=3\log(3p_{\max})\).
Subset-sum distinctness and distinct lower coordinates follow from unique
factorization; each prime, step and exponent travels with its coordinate under
sorting. The two exclusion arguments show that any box allowing \(G\ge0\) must
have spread \(<R\). This is not a uniform assertion as the prime set varies.

For \(b_i(n)=m_i n+r_i\), \(m,r\in\mathbb Z_{\ge0}^3\), \(m\ne0\), choose
fixed extreme slope labels, put \(\Delta=\alpha_{i_+}-\alpha_{i_-}>0\),
\(\beta=\gamma_{i_+}-\gamma_{i_-}\), and use
\(N=\max\{0,\lceil(R-\beta)/\Delta\rceil\}\).
The lower bound on spread holds before any coordinate-order stabilization.
Equality \(\Delta n+\beta=R\) is excluded strictly by the theorem.
No numerical value of \(R\), \(a\), or \(N\) was computed.

The remaining geometric region contains infinitely many exponent boxes, via
\(b_i=\lceil Z/h_i\rceil-1\) at arbitrarily large \(Z\). This is an analytical
construction of bounded shape, not a witness of either sign. The comparison gap
is not described as an RH-equivalent criterion, and no RH progress, general-prime
sign result, novelty, formal proof or Lean freeze is claimed.

## Classical reference status

The primary attests reading Boyd and Vandenberghe,
[Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf),
Appendix A.1.2 printed p.634 (norm axioms), §3.1.5 pp.72-73 (norm convexity),
and §3.1.3 p.70, equation (3.3) (strict first-order condition).
Section 27.19 separately preserves the preceding caller's direct book-page check
and the supplied PDF identity: 6881335 bytes, SHA256
`40d976c83c18cce1900eff8c41bd5ad408c102b813af39d05ff85678ccf8d76e`.
These are existing attested classical ingredients. I12 did not make a fresh
network retrieval or independently repeat that literature check.
The specialized uniform spread argument is repo-derived and proved in the source;
it is not attributed to the textbook. Originality remains unassessed.

## Preserved caller fixed verification

The caller's audit records SymPy **1.14.0**, **11** successful fixed symbolic
identities, checked at `2026-09-09T15:56:14.235408+00:00`. The dispatch supplies
host session **11977**, exit **0**. I12 preserves this as previously checked
caller evidence; it did not read that session's logs and did not replay the checks
as a new experiment. The check names, audit scope and corrections are reproduced
below from the identified JSON input without changing their substance.

```json
{
  "primary_task": "aaaf57ba-7b72-4143-b830-b4b58fe7fc2c",
  "checks": [
    "three exact distance coordinates form tU+W",
    "norm of U squared",
    "unit vector normalization",
    "projection v explicit sign and constants",
    "linearized L explicit expression",
    "orthogonal remainder identity",
    "orthogonal remainder nonnegative sum of squares",
    "q<=h1+h2 low-average difference",
    "q>=h1+h2 low-average difference",
    "norm squared projected decomposition",
    "high-coordinate lower geometry threshold"
  ],
  "exact_symbolic_identities": 11,
  "sympy": "1.14.0",
  "cpu_candidate_search": false,
  "gpu_dispatches": 0,
  "numeric_radius_or_ray_cutoff_computed": false,
  "paper_audit": [
    "All h_i positive and distinct subset sums ensure delta>0; the latter is explicit outside prime labels.",
    "t>=sqrt(6K_W) gives projected z>=t/sqrt6; rationalization denominator >=2t, without a T-dependent remainder.",
    "For saturated finite slabs q-r>=delta holds at arbitrary real upper budget, so the bound covers the whole interval without using the unreviewed 25-node theorem.",
    "Positive support and monotonicity handle the upper tail separately; far-coordinate geometry is not asserted beyond A+Q.",
    "The +1 in R makes the tail inequality strict, including t=R; T=log2, s=0/S and q=h1+h2 are allowed.",
    "Fixed-prime S uses p_max and permutation-invariant Q/delta; a nonnegative-gap box must have relative spread<R.",
    "For every nonzero nonnegative integer exponent ray, Delta=max(alpha)-min(alpha)>0 by unique factorization. The spread lower bound needs no eventual coordinate-order sorting.",
    "A bounded relative region still contains arbitrarily large common heights; no finite prime/exponent complement or RH conclusion follows."
  ],
  "caller_prompt_correction": "The previous brief phrase excludes slabs with G<0 was a sign-wording error. The proven condition gives G<0 and excludes G>=0; corrected before any source implementation of this new result.",
  "primary_text_notation": "The raw JSON contains literal Z_{\\u22650} in two prose strings. The explicit domain spells nonnegative integers; retain raw response and use Z_{>=0} in later source.",
  "independent_review": false,
  "checked_at_utc": "2026-09-09T15:56:14.235408+00:00"
}
```

## Execution scope and candidate validation

| Activity in I12 | Executed count |
| --- | ---: |
| CPU candidate generation / exponent-box search | 0 |
| GPU dispatches / kernels | 0 |
| Old fixed-xi search replay | 0 |
| New numerical radius or ray-cutoff computations | 0 |
| Re-executions of the caller's 11 symbolic checks | 0 |
| New oracle or child-worker dispatches | 0 |
| Independent review seats run by I12 | 0 |

CPU work is limited to source/identity/coverage verification and ordinary
orchestration. The 11 existing fixed checks are not relabeled as search counts.
There is no generic harness build or Lean build in this increment; only any
compilation internal to the authorized canonical ingestion command belongs to
that command.

The only canonical generation door is:

```sh
make ingest BASE=feb497ec31f68e09ccc547a08810c398e66f3ee6 SOURCE=arithmetic-boundary-quantization
```

Validation checks the source prefix against the full immutable baseline bytes,
the primary and audit identities, preservation of all historical CAS/entries and
reports, one new report, and the generated pairing and source-span coverage of
all new numbered units. Entries are read under the actual schema, including
`receipts.chain_atoms` and nested children. Source text and CAS bytes have distinct
roles: canonical segmentation or EOF normalization is not a source correction.
All generated bytes, including any generator-owned trailing blank lines, must be
retained exactly. Any canonical tool error or incomplete coverage must be surfaced
in the worker's result rather than repaired by hand.

The following readings are implementation self-checks, not independent review.
Canonical ingestion completed in host session **69137**, exit **0**, with
`residual_open_added=24`, `skipped_existing=185`, `coarse_fallbacks=0`,
`open_genres=0`, `cas_objects_written=24`, and `ledger_changed=true`.
The bounded post-ingest verification completed in host session **73867**, exit **0**.

| Checked property | Observed result |
| --- | --- |
| Final source | 224856 bytes; 4141 lines; SHA256 `69702718f3602c508146f50cf70ebd78ef81adb09c2b826041d357e4a7dc11c8` |
| Whole historical prefix | Byte-for-byte equal to all 201529 BASE bytes; 3627 lines and the required prefix SHA256 preserved |
| Historical tracked objects | No modified/deleted path among 31945 CAS objects, 31987 backfill paths (including registry data), or 63 reports present at BASE |
| New source/report scope | Only the theory source is a modified tracked path; exactly this report is newly added outside canonical CAS/backfill |
| New canonical pairing | 24 CAS objects and 24 matching residual-open entries; every CAS SHA256 matches its address, `cas_ref` and raw fingerprint; all new `coverage_gids` are empty |
| Whole-unit source fidelity | All 19 units, 28.1 through 28.19, match a complete generated parent CAS body byte-for-byte, including its trailing LF bytes |
| Nested receipt integrity | Two `receipts.chain_atoms` parents and four child objects; each ordered concatenation equals its parent exactly; recursive child references resolve |
| Source notation | 59 display-math pairs and 241 inline-math pairs balanced; no escaped `\u2265` remains in the appended source |
| Primary/audit preservation | Both raw identities unchanged; the embedded 11-check audit JSON equals the supplied audit object |
| Git ownership | HEAD and branch remain the assigned values; no staged changes |

The 24 generated pairs comprise 19 new complete numbered units, four chain children,
and one historical EOF variant. The new 27.20 CAS
`0f2edd971934f092c03f1e0337c405bb5451bc782882f1ac74a39f24caff5055`
equals the existing
`b9312012d7a50523b18a81b1ab7058f32eea0ff09e16407d3aedde32b8f752a1`
bytes followed by one extra LF. The original CAS and its entry remain intact.
This is a canonical segmentation consequence of appending after the previous EOF,
not a new mathematical claim or a hand repair. Twenty-one new CAS objects end in
two LF bytes, and three end in one; every generated byte is retained unchanged.

The source spans below are zero-based UTF-8 byte intervals `[start,end)`, measured
in the final source. They are this report's verification readings, not hand-written
ledger boundary fields. Each ID identifies
`Meta/Digestion/atoms/sha256/<id>` and its paired
`Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/<id>.yaml`.

| Numbered unit | Source byte interval | Complete parent CAS SHA256 |
| --- | --- | --- |
| 28.1 | [201605,203008) | `d909d065108c6ff90cad2a6bbb302d62ee874ad330be75a3f7fbd4ab809af2bc` |
| 28.2 | [203008,204578) | `a56c3f09cf4383ce7d9c0336b4c407edb01b8bb2b794c53665d6deb8b30254b0` |
| 28.3 | [204578,205409) | `da5990461071ee1014ccaffb07e78213e5d660faa9650358edc7dcb2c70824dd` |
| 28.4 | [205409,206979) | `5178013c573ba273f04e369efc0c880aaf8ae56c97795c808944c783b47767fc` |
| 28.5 | [206979,208114) | `40819c2f3992d49ee73c13964c12ebfe031eaebae82e24ee59eac620fda90939` |
| 28.6 | [208114,208969) | `0063ecde9f3280a226a3664701ca0f6592368e41c8bcfc996acff6963cb4c058` |
| 28.7 | [208969,210288) | `21352388acac0523543842b7760dc22a46d08f4155e4b471e06d567213026b89` |
| 28.8 | [210288,211272) | `df32a6dc56baa2a0f3077b9c851f5938d011b02882163950f005f7377865c394` |
| 28.9 | [211272,212137) | `b250a8df3bee3667aa2331003939dc36596f85b8ebdf331d24234ca2c9c1f490` |
| 28.10 | [212137,213167) | `75bcca43ee1e0c4fd5136040dd4c646fcbbb8d006e21538677c9463bd385ad0d` |
| 28.11 | [213167,213913) | `bf7a0be461ca58e5084fefcad736fe9072a2b53b8e2239f887693ca79553cbac` |
| 28.12 | [213913,215101) | `010e6050d411cd7dcabbbdc100782eba7c268b33fbed72e6de659b67974622d9` |
| 28.13 | [215101,216799) | `53d65039c18712b90142dc04a85800a2f425d32a8c215055e722a2e4e1b146a5` |
| 28.14 | [216799,217793) | `4751a333c6abcabfd75a07ff46c37a8d543854765c27f1062d14460079d621f0` |
| 28.15 | [217793,219371) | `add6b8e1f142552e87609f666945b4b5e2db35c10d620bf7fa05d7683abf90f0` |
| 28.16 | [219371,220328) | `8f68143bff753863ef47a4dfe73c6552bc06565cf7e5063b5b0190a30b38c993` |
| 28.17 | [220328,221578) | `6d8521f9077ebf00ed948722f786ed7139527a4b38c52cf6aaaece4ab4103a89` |
| 28.18 | [221578,222901) | `5c8fe1bab72138aa36c554c15fadb39a328393d4f159abd8b76800f1fe448a5d` |
| 28.19 | [222901,224856) | `6d5c629de009b70b0239c0a0b56d5cd5ffb90cf6f868ca84e94b500a1aa89939` |

The chain children are also canonical paired objects:

- Parent `53d65039c18712b90142dc04a85800a2f425d32a8c215055e722a2e4e1b146a5`: `5fadee0720f94e3d88aff57b68bd5bbd843b61f5e50be251a5f1ca18959ee321`, `be3dea0c53699c252ace634f82a98b2aa68a6d970cc5ed78d2e8164ef438c9a4` (ordered, lossless concatenation).
- Parent `6d8521f9077ebf00ed948722f786ed7139527a4b38c52cf6aaaece4ab4103a89`: `bdf712632d0a2cb3abc728145264be6e824ab2f9a19888a61a9eeead07a37bf2`, `dc7d3354ece031c5d8e97172bac5a93e6174f01bf367578a020a8889ecc42972` (ordered, lossless concatenation).

The worker envelope carries every changed-file identity and the bounded verification artifact reference.

One report-only assertion initially exited 1 because its row-count query covered
both the earlier proof map and the complete CAS table: it counted 21 single-unit
rows while expecting 19. Restricting the query to the explicitly named complete
parent CAS table returned exactly 28.1 through 28.19 and exited 0. This was a
verification-query scope error; no source or generated bytes were changed in
response. The canonical ingest and whole-unit byte comparisons had succeeded.

## Remaining obligations

1. I12 returns the candidate and actual canonical/verification evidence, with any
   unresolved error explicit. This is an implementation proposal only.
2. After I12 is terminal, the caller must seal the exact delta and arrange independent
   source/architecture/quality/verification review under the repository workflow;
   I12 has no independent review verdict.
3. The caller owns staging, commit, push, PR creation and ordinary required repository
   gates. Review and final S17 `MERGED` remain dependent on S16 `MERGED`; this worker
   does not inspect or settle the live S16 review target. An unmerged candidate is
   not delivery and is not termination of the standing research goal.
4. No formalization has been performed. Any future Lean admission or pruning-rule
   implementation needs its own approved scope, exact arithmetic and source identity,
   verification and review; ingestion alone does not discharge it.
5. The sign within bounded relative spread at unbounded common height, and the broader
   prime problem, remain unresolved by this layer. Later common-height/all-slab
   results need their own source increments and cannot be imported as I12 evidence.
