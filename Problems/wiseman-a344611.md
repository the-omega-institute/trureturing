---
slug: wiseman-a344611
bibkey: oeis2021a344611
doi: null
url: https://oeis.org/A344611
triage: theorem
motivation_gids:
  - D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.result
---

## Problem

Gus Wiseman's OEIS A344611 revision 27, FORMULA, states: “Conjecture: a(n) <= A160786(n). The difference is 0, 0, 0, 0, 1, 2, 4, 9, 16, 28, 48, 79, ...”. Its NAME is “Number of integer partitions of 2*n with reverse-alternating sum >= 0.” Its COMMENTS define “The reverse-alternating sum of a partition (y_1,...,y_k) is Sum_i (-1)^(k-i) y_i.” The OFFSET is “0,2”, including the empty partition. A160786 revision 25 gives “a(n) = A027193(2n+1).” A027193 revision 78 counts partitions into an odd number of parts. The electronic sources have no page numbers, DOI or arXiv identifier.

For a decreasing positive partition $\lambda=(\lambda_1,\ldots,\lambda_k)$ of weight $m$, set $R(\lambda)=\sum_{i=1}^k(-1)^{k-i}\lambda_i$, with $R(())=0$. The assertion is

$$
\forall n\in\mathbb N,\quad
\#\{\lambda\vdash2n:R(\lambda)\ge0\}
\le\#\{\mu\vdash2n+1: \text{the number of parts of }\mu\text{ is odd}\}.
$$

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Positive decreasing integer partitions of a specified weight | `Nat.Partition`, with `parts.sort (· ≥ ·)` | Positive multiset parts with the weight constraint; decreasing sorting is inlined. |
| Reverse signs and the empty sum | `reverseAlternatingSum` | Existing integer recurrence `TrimmedAlternatingPartitions.trimmedSums`, last endpoint with default zero; the update is $z\mapsto a-z$. |
| Partitions of $2n$ with $R\ge0$ | `a344611` | `Nat.card` of the literal nonnegative-endpoint subtype. |
| Odd number of parts at weight $2n+1$ | `a160786` | `Odd p.parts.card`; no parity restriction on individual parts. |
| Every $n\ge0$ and non-strict comparison | `claim`, `result` | The natural-number quantifier includes zero; no added source hypothesis. |

## Motivation

The settling GID is `D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.result`, admitted as `open-problem-resolution (#23757; Proved)`. The named external conjecture and its source and literature screen are recorded in [#23757](https://github.com/the-omega-institute/trureturing/issues/23757). There is no anchor atom. The source note is [oeis2021a344611](../Library/PermutationPatterns/oeis2021a344611.md).

## Gap

The missing relation is an injection between different weights, $m$ and $m+1$. The existing integer accumulator and partition sorting are reused. Fixed-weight parity identities alone do not provide the required injection. The neighbouring A344743 comparison has a different target and is not equivalent.

## Route

For odd source length, increase the first part by one. For even source length, append a part of size one. Both branches preserve positivity and decreasing order, increase weight by one and produce odd length. The private theorem `endpoint_even_le` proves the even-length endpoint bound by two-step induction. Its consumer `first_pair_eq` forces equal first and second parts in every nonempty even-length source with nonnegative endpoint. The odd branch has a unique largest part, and the nonempty even branch has a repeated largest part. The empty source maps to $[1]$. Branch inverses and disjointness give `raiseList_injective_on`, then `raisePartition_injective` for every source weight $m$. The public `result` applies `Nat.card_le_card_of_injective` at $m=2n$.

## Falsifier

A source partition with an invalid image, a collision between different sources, or a natural index violating the count comparison would contradict the proposed assertion. The integer recurrence, empty-list default and odd-number-of-parts convention are part of the exact claim. A failure of the adjacent A344743 conjecture is not a refutation of A344611.

## Evidence

Kernel evidence is `D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.lean`: public `result : claim`, with the private endpoint, branch-disjointness and injection lemmas named above. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

Experiment: [wiseman-a344611 at revision 6c424c1a68a8d81ed46f83a441a14a179d1708c4](https://github.com/the-omega-institute/trureturing-experiments/tree/6c424c1a68a8d81ed46f83a441a14a179d1708c4/docs/reports/wiseman-a344611). The unmodified `check.py` extracted from that revision was run as `python3 /Users/auric/.sshx/af3ecdd104fa85fef1d8b17a/attempt-1/stageb/check.py`, exit 0, final line `ALL_CHECKS_OK`. Script SHA-256: `99253e529398497e64c2e444787a2a1c97a40cc99d29219d1432c547fcc396ba`. It exactly enumerates $n=0,\ldots,20$, checks 61,515 qualifying source partitions, independently checks partition totals and length parity by dynamic programming, verifies four sequence prefixes and the published difference prefix, and checks the two branch inverses and disjointness. It checks equality at $n=0,1,2,3$, strictness witnesses at $n=4,\ldots,20$, and the adjacent comparison at $n=1$. These are finite computations.

The escape audit of the sole public theorem, `result`, is unfinished: [#24072](https://github.com/the-omega-institute/trureturing/issues/24072). No four-slot registration is claimed validated.

## Triage

### What the settlement shows

1. **Proved, kernel-checked:** `raiseList_injective_on` establishes injectivity on positive decreasing lists with nonnegative reverse endpoint. `raisePartition_injective` establishes the induced injection for every source weight $m$, with target weight $m+1$. The decisive mechanism is `endpoint_even_le` and its equal-first-pair consequence, separating the parity branches.
2. **Proved, kernel-checked:** `result` proves the exact A344611 inequality for every $n\ge0$, including the empty-partition boundary.
3. **Computed:** the pinned experiment in Evidence exits 0 with `ALL_CHECKS_OK`; it checks 61,515 sources for $n=0,\ldots,20$, equality at $n=0,\ldots,3$ and strictness witnesses at $n=4,\ldots,20$. This claim has computation evidence only.
4. **Open:** the separate uniform strict-inequality strengthening for every $n\ge4$ is not formalized in this delivery. The finite witness checks do not close that formalization obligation.
5. **Computed:** A344743 is not equivalent: at $n=1$ its stated comparison is $0\ge1$. This finite comparison is checked by the experiment in Evidence; it does not refute A344611.

The proof extends from even source weights to the injection at arbitrary source weight. The partial literature screen in #23757 identifies no other published result whose proof depends on this conjecture; completeness of that dependency search is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The partial screen in #23757 covers the primary OEIS entries and histories, specified arXiv sections, recent partition-theory leads, Zenodo, public Lean collections and repository records. OpenAlex and Semantic Scholar were rate limited; Fine, Merca and Arnold texts and the independently unopened Chaves thesis remain explicit access gaps. No exhaustive novelty conclusion follows from those searches. No source journal version or source arXiv paper is identified. The source settlement and the separate uniform strictness strengthening have different evidence states. The unfinished escape audit is tracked by #24072.
