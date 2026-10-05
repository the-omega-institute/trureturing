# Full-source supplier capacity at h = 15

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
