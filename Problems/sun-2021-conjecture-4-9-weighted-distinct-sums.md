---
slug: sun-2021-conjecture-4-9-weighted-distinct-sums
bibkey: sun2021weighteddistinctsums
doi: 10.1007/s10801-021-01028-8
url: https://arxiv.org/abs/1811.10503v6
triage: theorem
motivation_gids:
  - D5/S3/Arith/Additive/SunWeightedDistinctSums.result
---

# Sun's weighted distinct-sum bound

## Problem

Zhi-Wei Sun, *On permutations of {1,...,n} and related topics*, J. Algebraic Combin. 54 (2021), 893–912, DOI 10.1007/s10801-021-01028-8, arXiv:1811.10503v6, Conjecture 4.9, printed page 18:

> Conjecture 4.9. Let $n\in\mathbb Z^+$ and let $F$ be a field with $p(F)>n+1$, where $p(F)=p$ if the characteristic of $F$ is a prime $p$, and $p(F)=+\infty$ if the characteristic of $F$ is zero. Let $A$ be any finite subset of $F$ with $|A|\ge n+\delta_{n,3}$, where $\delta_{n,3}$ is 1 or 0 according as $n=3$ or not. Then, for the set $S(A):=\{\sum_{k=1}^n k a_k:a_1,\ldots,a_n\text{ are distinct elements of }A\}$, we have $|S(A)|\ge\min\{p(F),(|A|-n)n(n+1)/2+n(n^2-1)/6+1\}$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A field $F$ | `F : Type`, `[Field F]` in `claim` | The preregistered carrier is literal. |
| Characteristic zero gives infinity; prime characteristic gives that prime | `pF` | `ringChar`, zero test and `ENat` top/cast. |
| Positive $n$ | `n : Nat`, `1 ≤ n` | Positive integers represented by positive naturals. |
| $p(F)>n+1$ | Characteristic hypothesis in `claim` | Strict comparison in extended naturals. |
| Finite $A$ | `A : Finset F`, `[DecidableEq F]` | Decidable equality is a classical representation requirement; it excludes no classical field. |
| $|A|\ge n+\delta_{n,3}$ | Size hypothesis in `claim` | The conditional is exactly 1 at $n=3$ and 0 otherwise. |
| Distinct selected elements; weights $1,\ldots,n$ | `weightedDistinctSums` | Embeddings from `Fin n` into $A$, weighted by the natural value plus 1. |
| Numerical expression and minimum with $p(F)$ | `sunBound` and the conclusion of `claim` | Natural subtraction is exact under the size hypothesis; both divided products are integral, so natural division preserves the source expression. |
| Refutation | `result : ¬ claim` | The witness is $F=\mathbb Q$, $n=2$, $A=\{0,1,2\}$. |

## Motivation

The settling declaration is `D5/S3/Arith/Additive/SunWeightedDistinctSums.result`. Its admission basis is `open-problem-resolution (#16084; Refuted)`; the published conjecture and the literal conventions are preregistered in [#16084](https://github.com/the-omega-institute/trureturing/issues/16084).

## Gap

The conjecture requires at least five distinct sums for a three-element set at $n=2$. Distinct input tuples do not ensure distinct weighted sums. The source's exception at $n=3$ does not cover this obstruction at $n=2$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Route

Specialize the universal assertion to $\mathbb Q$, $n=2$, $A=\{0,1,2\}$. The six ordered pairs yield $2,4,1,5,2,4$. The consumed private `mem_weighted_two`, `sums_eq` and `sums_card` establish the exact weighted-sum set and cardinality. The consumed private `pF_rat`, `a_card`, `size_hyp`, `char_hyp` and `sun_bound` check the characteristic, admissibility and bound. `result` concludes by contradiction from $5\le4$.

## Falsifier

The claimed bound is falsified by the admissible rational witness with $|S(A)|=4<5$. The mechanism would fail if the selected pairs were not distinct members of $A$, if a hypothesis excluded this set, or if the characteristic truncated the required minimum below five; the compiled proof checks all these obligations.

## Evidence

The module has `generality: I`: its refutation uses the fixed rational witness $n=2$, $A=\{0,1,2\}$. The module is `D5/S3/Arith/Additive/SunWeightedDistinctSums.lean`; its Scribe and emitted Blueprint carry the four definitions and the settling theorem, with exactly one Refuted `OpenProblemResolutionClaim`. `result` states the negation of the full conjecture. The axiom closure of every public declaration is contained in {`propext`, `Classical.choice`, `Quot.sound`}.

### Exact finite experiment

[Experiment directory at commit `71e148735c8d580857c622ef6b5d2086776861b4`](https://github.com/the-omega-institute/trureturing-experiments/tree/71e148735c8d580857c622ef6b5d2086776861b4/docs/reports/sun-2021-conjecture-4-9-weighted-distinct-sums).

Command: `git -C /Users/auric/trureturing-experiments show 71e148735c8d580857c622ef6b5d2086776861b4:docs/reports/sun-2021-conjecture-4-9-weighted-distinct-sums/check.py | python3`; exit 0. Script SHA-256: `1ecac5c8de3fdb6b9262f2feff52e2b1073f2d05f28bae61921a6ff8abf1ab47`. The rational set is $\{1,2,4,5\}$, with cardinality four and proposed bound five. Prime-field checks give cardinality four at $p\in\{5,7,11,13,17,19,23,29\}$. The progression scan uses $A=\{0,\ldots,m-1\}$ with $1\le n\le6$ and $n+\delta_{n,3}\le m\le n+4$. The subset scan uses every $m$-element subset of $\{0,\ldots,9\}$ for $(n,m)=(2,2),(2,3),(2,4),(3,4),(3,5)$. The failure rows are $(n,m,|S|,\mathrm{bound})=(2,3,4,5)$ in each scan; the script's error indicator is zero. These are exact integer computations, not a uniform theorem about all set sizes or fields.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Collision mechanism at the rational witness | Proved; kernel-checked | The consumed private `sums_eq` proves $S(\{0,1,2\})=\{1,2,4,5\}$; `sums_card` proves cardinality four, `sun_bound` proves the proposed bound five, and `result` refutes `claim`. |
| Canonical three-term progressions in the tested prime fields | Computed | The pinned experiment gives $|S|=4<5$ for every prime $5\le p\le29$. It tests $u=0,t=1$. |
| All nonconstant three-term progressions in allowed fields | Proved in prose; not formalized | The affine calculation below proves the extension. A finite computation alone cannot establish a universal quantifier over fields, $u$ and $t$. |
| Progression scan and subset scan | Computed | The exact experiment scope in Evidence has only the failing pair $(n,|A|)=(2,3)$. No broader subset sweep is attributed to this script. |
| Every subset of $\{0,\ldots,9\}$ at $n=2,3$ beyond the sizes in Evidence | Open | The pinned script does not test the additional sizes; the full-size sweep is unverified. |
| Candidate amendment excluding $(n,|A|)=(2,3)$ | Open | The tested range supports adding this exception to the cardinality requirement. The unrestricted amendment is neither proved nor formalized. |
| Sun–Zhao lower bound at $n=2$ | Literature reading | *Linear extension of the Erdős–Heilbronn conjecture*, J. Combin. Theory Ser. A 119 (2012), 364–381, arXiv:0810.0467v7, Theorem 1.1 and (1.1), gives $\min\{p(F)-\delta,2|A|-3\}$, where $\delta=[n=2\ \&\ a_1+a_2=0]$. For weights 1,2 in the allowed characteristics, $\delta=0$; at $|A|=3$ its bound is three, consistent with four. This theorem is not on the module's dependency path. |
| Experiment | Computed | The pinned directory, rerun command, exit 0, SHA-256 and exact scope are given in Evidence. No program or dataset is embedded here. |
| Other source statements and Remark 4.9 | Literature reading | Remark 4.9 proposes the same bound for finite additive groups. Additive groups of the tested prime fields have the same failing witness. Conjecture 4.9 is posed independently; this refutation does not invalidate the source's separately stated theorems. It supplies no settlement of other conjectures. |

For the concrete witness, $(0,1)$ and $(2,0)$ both yield two, while $(0,2)$ and $(2,1)$ both yield four. This explanation is direct arithmetic; the exact set and cardinality are also established by the consumed private Lean helpers named above.

For the progression family, write $A=\{u,u+t,u+2t\}$ with $t\ne0$. Each distinct ordered pair has weighted sum $3u+(i+2j)t$ for distinct $i,j\in\{0,1,2\}$. The coefficients are precisely $\{1,2,4,5\}$. The characteristic hypothesis at $n=2$ permits characteristic zero or a prime at least five, so every nonzero difference between these coefficients (of absolute value at most four) is nonzero in $F$. Multiplication by $t$ and translation by $3u$ preserve distinctness. Thus all four values are distinct and the bound is five. This paragraph is a prose proof of the family, not a Lean theorem or a finite computational certification of every allowed field.

The failure is a missing exceptional size at $n=2$. The closest surviving statement in this delivery is the exact rational cardinality; the unrestricted amended bound remains open. The Sun–Zhao estimate is compatible with the counterexample and is not refuted by it.

## ASSUMED-UNVERIFIED

The bounded source and literature screen is recorded in #16084; global absence of prior published solutions is not established. The uniform candidate amendment and the subset sizes outside the pinned experiment's scope remain open. The affine family argument above is not Lean-formalized.
