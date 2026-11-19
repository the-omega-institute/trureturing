---
slug: shao-zhao-italian-cycle-closed-form
bibkey: shao2026italiandomination
doi: 10.48550/arXiv.2610.00108
url: https://arxiv.org/abs/2610.00108v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.result
---

# A finite sum for the labelled-cycle Italian coefficients

## Problem

Pingping Shao and Chengye Zhao, *Counting Weight-k Italian Dominating Sets on Trees and Cycles*, arXiv:2610.00108v1, §9, direction 4:

> Deriving explicit closed forms for $d_I(C_n,2n-j)$ for general $j$ via the exclusion-counting method of Theorem 7.1 (the polynomiality of these coefficients in $n$ is already established in Lemma 3.4).

The named problem is preregistered in [#23882](https://github.com/the-omega-institute/trureturing/issues/23882). Its settlement is Proved for every $n\ge3$ and $0\le j\le2n$. Vertices are labelled; rotations and reflections are distinct functions. The suggested exclusion method is a route, rather than a restriction on the requested coefficient identity. Subtracting the answer from the unrestricted trinomial coefficient also supplies an explicit excluded count.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A labelled simple cycle with $n\ge3$ | `Fin n`, `finRotate n`, and `3 ≤ n` in `CycleDeficit.claim` | The two cyclic neighbours are distinct in this range. |
| Italian labels in $\{0,1,2\}$ and neighbour sum at least two at every zero | Imported `CycleItalianDominationRecurrence.IsItalian`, with labels `Fin 3` | The existing source definition is reused. |
| Weight $2n-j$ | `OrdinaryWords.dI n (2*n-j)` | The literal weight sum occurs in the finite subtype. |
| Every $0\le j\le2n$ | Natural `j` and the bound in `claim` | Zero is included; no added restriction. |
| An explicit nonrecursive closed form | `closedForm`, `zeroFree`, `allExceptional`, and the finite sums of `gapTerm` | Integer guards, rational arithmetic and ordinary binomial coefficients only. |

## Motivation

`D5/S3/Combinatorics/Graph/ItalianDomination/CycleDeficit.result` gives every coefficient by one guarded finite sum, rather than a recurrence in the cycle length. Its admission basis is `open-problem-resolution (#23882; Proved)`, generality is `G`, and utility is `none`: the statements concern arbitrary parameters and include no fixed numerical certificate.

## Gap

The source poses the general-deficit formula as an open direction. Its previously settled total-count recurrence does not determine the individual coefficients. Tree coefficients, symmetry quotients and a Lean fixed-deficit polynomial corollary are outside this settlement. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Write $y_i=2-f_i$. Valid deficit words satisfy $y_i=2\Rightarrow y_{i-1}+y_{i+1}\le2$. A zero-free gap is either exactly $22$ or has no adjacent twos. For $m$ zeros, $b$ exceptional gaps, $c$ ones and $a$ ordinary twos, put $t=m-b$. Then $n=m+c+a+2b$ and $j=c+2a+4b$.

For $t>0$, the ordered gaps are counted by

$$\binom mb\binom{c+t-1}{c}\binom{c+t}{a}.$$

Marking a labelled zero multiplies the unmarked count by $m$ and gives $n$ possible root positions. Thus the refined count is $n/m$ times that product. This is a vertex-marking count, including for periodic words. When $t=0$, the word repeats $022$ and has three labelled shifts. Marking a one gives the zero-free contribution. These disjoint classes exhaust the coefficient.

## Falsifier

A counterexample would be a labelled Italian function, with $n\ge3$ and $0\le j\le2n$, whose coefficient disagrees with `closedForm`; or a failure of the ordinary-word and rooted-gap bijections. The settling theorem quantifies over the full parameter range.

## Evidence

The Lean modules are `OrdinaryWords`, `RootedCycleGaps` and `CycleDeficit` under `D5/S3/Combinatorics/Graph/ItalianDomination/`. The settling theorem is `CycleDeficit.result : CycleDeficit.claim`. The canonical Library note is [shao2026italiandomination](../Library/Combinatorics/shao2026italiandomination.md).

The escape audit is unfinished for the public theorems listed in [#27880](https://github.com/the-omega-institute/trureturing/issues/27880). The missing evidence is a faithful dependent-family reconstruction, variation, sensitivity and observational dependence; no validated registration is claimed.

### Exact coefficient experiment

[Experiment directory at commit 7037f0ac550c4ca5a0202e7b1e69f4499b056d4a](https://github.com/the-omega-institute/trureturing-experiments/tree/7037f0ac550c4ca5a0202e7b1e69f4499b056d4a/docs/reports/shao-zhao-italian-cycle-closed-form). The committed `check.py` has SHA-256 `ecec4f3ab19529fea7a0dd2f7760965642c6318ca660d2f80abf909df1ab76c3`. The command `python3 /tmp/op-shaozhao00108/stageb-check.py`, run on that exact blob with Python 3.14, exits 0 and reports `ALL_CHECKS_OK`: all 88,560 labelled ternary functions for $3\le n\le10$ and all 3,712 coefficients for $3\le n\le60$, $0\le j\le2n$, agree. These are finite computations.

## Triage

### What the settlement shows

1. **Proved, kernel-checked:** `OrdinaryWords.marked_vertex_identity` and `RootedCycleGaps.refined_cycle_marking_count` count labelled marked vertices; `RootedCycleGaps.zeroFree_cycle_marking_count` gives the one-mark identity. Periodic words have exactly $m$ zero marks or $s$ one marks. No stabilizer correction occurs.
2. **Proved, kernel-checked:** `RootedCycleGaps.refined_cycle_marking_count` holds for arbitrary $N+1=m+c+a+2b$ with $m>0$. The ordinary case uses $b<m$. **Proved in prose:** setting $b=m$, $c=a=0$ in that identity gives $mK=3m$; cancellation of $m>0$ gives exactly three labelled $022$ shifts, as used by `CycleDeficit.result`.
3. **Proved, kernel-checked:** `RootedCycleGaps.zeroFree_cycle_marking_count` applies at every positive length represented as $c+a+1$. **Proved in prose:** a failed guard makes the corresponding `if` term zero. At $j=2n$, weight zero forces every Italian label to be zero; its neighbour sum is zero, contradicting the Italian inequality for $n\ge3$. Hence the endpoint coefficient, and by `result` the formula, are zero.
4. **Computed:** the exact coefficient experiment above exits 0 with `ALL_CHECKS_OK`, covering 88,560 functions for $n=3,\ldots,10$ and 3,712 coefficients through $n=60$.
5. **Computed locally:** `python3 /tmp/op-shaozhao00108/probe/refined_check.py` exits 0 with `REFINED_GAP_CHECKS_OK`: 797,148 words for $3\le n\le12$, 591 refined parameter classes, 482 nonempty. The script SHA-256 is `020efdfaaa5a589475f817350251a246d41464137938177a9b54e6281891f452`. Its immutable publication in the experiments repository is unverified; this reading is not a published reproducibility claim or a universal proof.
6. **Open:** tree coefficients, rotation/reflection quotients and a Lean fixed-$j$ polynomial corollary. The argument settles the named general labelled-cycle coefficient question; it imposes no change on the source’s other theorems.

## ASSUMED-UNVERIFIED

The bounded literature screen is the one recorded in #23882. Citation APIs were rate-limited; some survey and foundational texts were not read in full. No exhaustive priority or novelty certification is claimed. Immutable publication of the refined-gap checker is unverified. Four-slot escape registration remains unfinished under #27880.
