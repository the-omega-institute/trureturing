# Full-source supplier capacity at h = 15

[Actual-source Read memory witnesses](read_memory.md) supplies TM68's complete
six-call c/u/v tables and actual-tree certificate:99 states at H=60 and98 at
H=61,62,63, all56 literal INITIAL outputs, with accepted-pre-first-rho material
18,21,22,23 reported separately. The all-controller lower61 is retained;
exact state minima and paid/physical memory correspondence remain unresolved.

These finite mathematical artifacts support [TM60.3–5](../../develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#TM60-T3): the conditional authentic supplier alphabet has minimum size four at H = 60, 61, 62, 63 under the original TM30/TM58/TM59 contract.

[h15_joint_cover.py](h15_joint_cover.py) uses Python 3.9 or newer and only the standard library. From any working directory, run:

```sh
python3 -I -S -B /path/to/h15_joint_cover.py
```

The default certificate path is beside the script. `--certificate PATH` supplies another path; `--write` regenerates its finite data. The optional `--prior PATH` checks a discovery certificate's complete partitions and Hall sets against the independently enumerated families. There is no time-dependent cutoff or external solver.

The calculation constructs every tight partition by forward prefix enumeration, deduplicating only equal partitions of all 42 targets. It considers all 12,341 triples with repetition. Breadth-first alternating paths produce a matching and a deficient target set for each triple. Every Hall inequality is checked directly, including all 12 zero-weight obligations. A separate exact rational Clifford matrix calculation checks 105 actual unit words in three windows. The unchanged TM58 formula and literal initial target dictionary are checked by 420 actual word executions across all four cap residues, including terminal acquisition, acceptance equality, refusal and every hidden tag-0 composition.

[h15_joint_cover.json](h15_joint_cover.json) contains the finite proof data. Target order is the 35 finite points in lexicographic order followed by the seven folded rows in increasing order. A slot is the integer bit mask of its targets, with target 0 in the least significant bit. Each partition sorts its nonempty masks numerically; partitions sort lexicographically. Triple order is lexicographic `combinations_with_replacement(range(41), 3)`.

Each `hall_rows` entry is `[maximum_matching_cardinality, deficient_target_mask, neighbor_slot_count]` for the corresponding triple. The neighbor count sums over three distinct positions, even when two partition indices agree. All entries satisfy `popcount(mask) - neighbor_slot_count = 42 - cardinality > 0`. `paths` retains one tight path per partition. `maximum_matching` provides a 41-target assignment; its slot indices concatenate the three partition slot lists, and -1 denotes the unmatched target. The coverage histogram counts every triple once.

The retained results are 41 tight partitions, 12,341 deficient triples, and maximum coverage 41. The prefix partition counts are 1 through endpoint 9, then 2, 2, 2, 11, 22, 41 at endpoints 10 through 15. The complete upper check has 56 distinct initial targets, with branch counts AA = 96, AR = 52, RA = 48, RR = 224 across 420 executions. All use zero reads, at most one accepted replacement, and nine whole-source calls.

The finite calculation does not enumerate all trees or all controllers. Its lower-bound scope comes from the all-action necessary bridge in TM59.3/TM60.3, checked in the paper against original same-history collisions. Its complete-source upper scope comes from Atomic360's Euler/bracketing correspondence and TM30's behavior congruence, used in TM58. The selected actual words are mathematical witnesses; no representative is substituted during the original execution. This is ordinary paper mathematics and exact arithmetic, not Lean/kernel certification, an admission check, an authentic supplier implementation, or physical-device evidence.

The weight-only constraint is 30 / 10 = 3 and does not rule out three symbols. The stronger conclusion requires the complete joint integer obstruction. The source theory reuses TM58's own simultaneous resource witness; only alphabet size is asserted optimal. All authentic evidence acquisition, same-source authentication, production, delivery, retention, contexts, guards, archives and paid costs retain their original boundaries. No claim is made about other caps or asymptotic optimality.

The mathematical deduction is repo-derived. Atomic359–360, TM30, TM38, TM47, TM58 and TM59 are the source suppliers; classical neighbor counting and matching are intermediate methods. The discovery proof and certificate were advisory inputs, independently checked against forward enumeration, every Hall set, and actual source arithmetic. No discovery transcript or process log is part of these artifacts.

## TM63 small-cap joint control

[joint_small_caps.py](joint_small_caps.py) and [joint_small_caps.json](joint_small_caps.json) support TM63. The script enumerates all 920 unit leaf words in the complete $h=4$ composition domain, checking all three unit windows and the literal initial targets and the constant initial `Read`, and verifies the same two-call policy for $H=16,17,18,19$. The policy first attempts the original $ρ$ modification and then appends the existing actual context $a^{H-12}$ on either response branch. Its four response words are `AA`, `AR`, `RA`, `RR`, so it has three reachable REQUEST values and two worst-case modifying/total source calls. The certificate also records the binary one-call response bound and the Kraft-tight four-word code. All bracketings are covered by the Atomic360/TM47 behavior-congruence bridge in the paper proof; no finite enumeration is presented as a controller search or a physical cost proof.

The same report retains 312 exact mixed-history checks on six actual composition witnesses and four caps, with both context sides, equality acceptance and unchanged rejection. It also gives a legal single-$ρ$ history whose current Read changes from $A$ to $B$ although $J(A)=A+B$, and a merged Read state with three reachable exact responses. The Read alphabet remains the original Clifford alphabet; the all-policy state lower bound rests on the paper's instruction-type case proof.

## TM67 parameter frontier

<a id="TM67-E1"></a>

[TM67.2–3](../../develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#TM67-T1) give the authentic full-source material family and the joint original-call tail. [parameter_frontier.py](parameter_frontier.py) and [parameter_frontier.json](parameter_frontier.json) retain finite arithmetic falsifier evidence in this supplier-capacity domain.

The script uses Python 3.9 or newer and only the standard library. From the repository root, run:

```sh
python3 -I -S -B docs/reports/fib-supplier-capacity/parameter_frontier.py
```

The default certificate path is beside the script. `--certificate PATH` selects another certificate; `--write` regenerates the deterministic JSON data. The default command recomputes the cases and checks exact certificate equality.

The complete composition triangle is checked for every integer cap $8\le H\le803$: 796 caps and 5,333,200 composition points. The calculation uses the original authentic TM58 supplier formula, literal target encodings, actual positive-context guard inequalities and acceptance equality. Every branch/entry has a unique initial target, and no target is missing. The 760 tail cases with $H\ge44$ check $d_2=H-8L-11$, the $Q$ branch bound and the balanced-threshold original-call upper bound. Genuine omission contributes one prefix call and no fictitious context; emitted contexts contribute two prefix calls and material only on their accepted branches.

The certificate records the cap range, regime counts, zero branch/entry collisions, zero missing targets, tail bound values, and selected cases with branch sizes. Target tuples in the calculation are injective arithmetic encodings of the literal INITIAL dictionary; the tag-2 field order remains $(2,(\mathbf u_{\rm unit},C))$ in the theorem and original output. Arithmetic encodings supply no online target or size port.

This is finite falsifier evidence for the explicit source-faithful policy. It does not enumerate all policies or controllers and does not replace TM67's all-family and all-policy paper proofs. Coverage of every actual Euler word, ordered bracketing, complete history and permanent collision uses Atomic360 and TM30/TM38/TM45/TM47 under their original hypotheses. It supplies no small-cap exact call optimum and no paid, controller-memory, physical, installed, supplier-production, archive, permission, Lean or kernel certification.

## TM69 five-Request obstruction

<a id="TM69-E1"></a>

[TM69.2](../../develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#TM69-T2) proves that every correct complete authentic TM58 controller on full $U_H$, $H=60,61,62,63$, with at most six total original calls needs at least six reachable Request states and 62 complete Request/Halt states. Its paper proof permits repeated genuine Reads and forgetting the initial supplier symbol. It counts completed modification words and fixed modifier-to-Halt edges, then compares two actual near-saturated original sources at every request of a complete execution. It does not use a first-Read capacity as an all-visit capacity.

[five_request_obstruction.py](five_request_obstruction.py) and [five_request_obstruction.json](five_request_obstruction.json) retain purpose-specific finite corroboration of that proof. The script uses Python 3.9 or newer and only the standard library, importing the existing actual ordered-tree, authentic supplier, literal INITIAL target and Clifford evaluators in [six_call_material.py](six_call_material.py). That evaluator independently compares integer normal forms with the exact rational matrices in [h15_joint_cover.py](h15_joint_cover.py).

From the repository root, run:

```sh
python3 -I -S -B docs/reports/fib-supplier-capacity/five_request_obstruction.py
```

The default recomputes the evidence and compares canonical certificate bytes. `--write` regenerates the deterministic certificate; `--certificate PATH` selects a different certificate. The script resolves its imports and default certificate relative to itself and also runs from another working directory.

The census keeps all 105 allowed compositions, all 56 literal INITIAL targets, the authentic loads `(17,12,14,13)` and the original nested tag-2 field order. It checks the displayed positive source at each composition with left-associated and balanced ordered brackets, including all three unit windows: 630 exact window checks. These finite bracket choices do not establish the all-bracketing lift; the paper uses Atomic360/TM58's complete actual-source correspondence and TM30/TM47 transport.

The necessary guard census covers all 44 admissible small-context mass pairs $(d_s,e_s)$ with $\delta<e_s\le\delta+4$ and $1\le d_s\le e_s\le2d_s$. For each pair it checks positive $d_L$ through $H+1$; larger masses reject all nine targets and cannot give a 4/5 split. Equality acceptance gives exactly $H-43-e_s\le d_L\le H-36-e_s$, hence $13\le d_L\le23$. Each actual mass pair has the explicit positive word $\alpha^{2d-e}\beta^{e-d}$; these are witnesses, not a restriction of the arbitrary context words in the theorem.

| cap | necessary guard cases | balanced guard cases | actual first-rho collision pairs | actual row11 context collisions | near-pair relation checks |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 60 | 488 | 64 | 6 | 248 | 12 |
| 61 | 620 | 80 | 6 | 320 | 32 |
| 62 | 756 | 96 | 6 | 396 | 68 |
| 63 | 896 | 112 | 6 | 476 | 136 |

Each first-rho case verifies the authentic membership, distinct INITIAL outputs, accepted original whole substitution, identical actual current Clifford read/size and over-cap next size for the paper's symbol2/3/4 pair, using both bracket choices. Row11 cases cover every $13\le d_L\le23$ that accepts row11 and every integer $d_L\le e_L\le2d_L$, with both context sides and both bracket choices. They verify the actual permanent tag-0 collision of `(11,13)` and `(11,15)`.

Near-pair checks use the genuine trees $\omega_{1,13}$ and $\omega_{1,14}$, with different literal targets `(0,1,56)` and `(0,1,60)`. At all offsets $0\le U\le\delta$, they check rejection preserving the same tree object for rho, a 13-leaf context and a 49-leaf context, and check every positive binary word fitting the larger tree's remaining slack, on both sides and bracket choices. The accepted updates preserve the four-leaf difference and exact current Clifford equality, including equality acceptance. These are bounded instances of the paper induction; they neither enumerate all histories nor implement a five-Request controller. In particular, the unbounded-in-history assertion that every visited genuine Read agrees rests on the transparent source-pair induction, not these finite checks.

Exact rational Kraft arithmetic separately gives at least four no-Read completed targets for six distinct targets after three common modifications, and at least two for five targets. The certificate records the initial three and forced two modifier-to-Halt edge budgets. These are necessary relations, not an exhaustive controller search or a source-realizability certificate.

Combining the paper lower with the existing TM68 witnesses gives $62\le K_6(60)\le99$ and $62\le K_6(H)\le98$ for $H=61,62,63$. Exact minima and six-Request attainment remain unresolved. This report makes no Lean/kernel, independent-review, required-CI, merge, paid/physical/installed saving, supplier realization or sustained-goal completion claim. All original source, response, permission and cost obligations remain those of TM69.1.

## TM70 complete 87-state construction

[TM70.3](../../develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#TM70-T3) gives an actual complete controller for each $H=60,61,62,63$: exactly87 reachable states, including56 literal INITIAL Halts,23 actual context Requests,6 rho Requests and2 actual Read Requests. Every run uses at most6 original calls, at most1 accepted rho, and accepted material before its first rho attempt at most17,18,19,20 respectively, with equality attained. The material minima are reused from TM65/TM67. Exact controller minima and paid/physical savings remain unresolved.

[controller87.py](controller87.py) and [controller87.json](controller87.json) retain all four immutable c/u/v tables and complete finite data. Python3.9 or newer, standard library only; the published source evaluator and rational Clifford matrices are imported relative to the script. From any working directory:

```sh
python3 -I -S -B /path/to/controller87.py
```

The default recomputes the certificate and checks exact bytes. `--certificate PATH` selects a certificate; `--write` regenerates it. The JSON stores instructions and actual response transitions separately from offline compilation proof data. Only the table address and current actual response select the next instruction; entry sizes, original targets, supplier provenance, offsets, factors and verification counters are not runtime ports. The full Read keys encode exact Clifford elements in the unique original normal form; signs, exponent parity and grade are retained. Defaults select Q00 and Halt updates are self-loops without extra states.

For every one of105 compositions at every cap, execution uses the actual source word omega and its one-leaf cyclic rotation, each with left-associated, right-associated and balanced ordered brackets. The2520 actual-tree executions include7560 initial unit-window checks. At each actual Read the integer normal form is compared with the independent exact rational matrix product. Whole candidates accept equality; refusals preserve the entire old tree by identity and count as calls. The serialized tables reach all87 states, all35 responses at L and all7 at L0, and all56 literal outputs, including14 nested tag2 outputs and every hidden tag0 composition. Mathematical execution rows retain the actual state, response, successor and whole candidate size for each original composition.

The finite data also refute merging L with L0, discarding response signs, reversing the H61 fourth-symbol marker, and treating the shared fourth-symbol C4 refusal as a free skipped operation. The complete all-Euler-word/all-bracketing assertion rests on TM70.3's source-faithful induction, not exhaustion of these finite samples or all policies. Original supplier evidence, source identity, permissions and paid construction/guard/retention/output obligations remain intact. This is ordinary mathematical corroboration, with no Lean/kernel, authentic supplier implementation, optimizer, minimum87, six-Request attainment or physical-cost claim.

TM70.4 directly applies the existing independent static FIB-name capacity contract: eight positions have55 legal names, fewer than56 required literal Halts; nine have89 and can name all87 constructed states. This yields minimum static length9 in that declared register contract, without a controller-state optimum. The constructed binary address width is7; microsteps, cross-seam writes, physical bits, installation and paid costs are separate obligations.
