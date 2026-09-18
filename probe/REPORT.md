# Zhao vincular stack probe

## Preregistered falsifiable predictions

Recorded before inspection, downloads, or computation.

1. An independently implemented right-greedy stack map, with the stack read top to bottom, reproduces the source's four outputs for input 514362: 463215, 263415, 426315, 632415.
2. Over S_9, the maximum fibre size of SC_{1_23_} exceeds 128.
3. At n = 5, the fibre-size multiset has two distinct values strictly greater than 4.

These are predictions, not verified conclusions. The source and issue #8634 still require clause-by-clause fidelity checking. All work is confined to this worktree and probe/. Third-party downloads will remain in runner scratch.

## Statement fidelity

Source: arXiv:2410.17057v1, fetched as the source archive into runner scratch; no third-party files enter this worktree. The macros in main.tex (lines 54, 59, 60) define SC, underline, and the symmetric group. Introduction paragraph 2 defines adjacency by underlining; paragraph 3 and pictures/ex*.tikz give exactly the four specified figure outputs.

- 4.14: dynamics.tex, label 1un23preimages: n >= 2; both maximum fibre sizes equal 2^(n-2). An attained-maximum predicate for each map expresses the same chain equality.
- 4.19: dynamics.tex, label 1un23uniquemaximum: the two specified words uniquely achieve the respective maxima. The source omits an n range. Issue #8634 explicitly supplies n >= 2 as an interpretation; the requested n = 8 refutation is unaffected by the small-n boundary. Strict inequality for every other permutation expresses unique attainment.
- 5.2: futuredirections.tex, second conjecture: n >= 3; second-largest distinct fibre value is 2^(n-3); exactly 2*n-2 permutations attain that value. The refutation must negate this entire conjunction via its first clause only.
- The source describes right-greedy sorting but has no formal transition rule. The adopted left-to-right input scan, stack word top-to-bottom, push iff the whole proposed stack avoids the pattern, otherwise pop and retry, agrees with the stated interpretation in #8634. The source does not explicitly specify this convention; agreement of the four anchors is its operational check.

No clause mismatch requiring a revised preregistration was found. The formal-answer skill is subordinate here to the explicit probe-only scope, exact JSON response, prohibition on delegation, and externally named open-problem-resolution exception; no generalized wrapper or D5 mutation will be manufactured.

## Independent Python result

Whole-word containment enumerates all triples and imposes the indicated adjacency; it never uses a new-top-only rule. Both increasing and decreasing maps were exhaustively evaluated on S_2 through S_9.

| n | inputs per map | max 1_23 | max 3_21 | designated increasing maximizer fibre |
|---|---:|---:|---:|---:|
| 2 | 2 | 1 | 1 | 1 |
| 3 | 6 | 2 | 2 | 2 |
| 4 | 24 | 4 | 4 | 4 |
| 5 | 120 | 8 | 8 | 8 |
| 6 | 720 | 16 | 16 | 16 |
| 7 | 5040 | 32 | 32 | 32 |
| 8 | 40320 | 64 | 64 | 64 |
| 9 | 362880 | 144 | 144 | 128 |

All three predictions passed. The four anchors reproduce exactly. F(765432819) = 144. At n = 5 the histogram over **all** outputs in S_5 is {'0': 65, '1': 19, '2': 24, '3': 1, '4': 8, '5': 2, '8': 1} (including 65 zero fibres); the first-clause witnesses have fibres 5 and 8.

The complete independent results, maximizers, histograms, and explicit witnesses are in enumeration.json. At n = 8 the three maxima are 65432718, 65432817, 76543218, each with 64 preimages. The preregistered n >= 2 uniqueness statement additionally fails at n = 2 (both permutations have fibre 1); the requested formal probe will still use n = 8.

Python measured wall duration: 9.790535 s. These are executable enumeration results, not yet kernel proofs.
