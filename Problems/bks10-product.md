---
slug: bks10-product
bibkey: blitvickammounsteingrimsson2026patterns
doi: 10.48550/arXiv.2610.29846
url: https://arxiv.org/abs/2610.29846v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson135289467Product.result
---

# The 135289467 overlap-three product formula

## Problem

Blitvić, Kammoun and Steingrímsson, *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*, arXiv:2610.29846v1, Section 7 item 10, page 49:

> The enumeration for 135289467 with overlap 3, for example, has a
> product formula according to our data, but the successive factors are
> not single binomial coefficients. However, the factors are polynomial
> starting from $j=3$, namely
> $121\binom{j-3}{0}+168\binom{j-3}{1}+72\binom{j-3}{2}$, in the
> binomial basis.

Let $A_j$ count actual permutations of length $9+6(j-1)$ whose windows starting at $1+6t$, $0\le t<j$, are order-isomorphic to $135289467$. All pairwise strict comparisons are imposed; additional occurrences are permitted. The settled statement is

$$
A_1=1,\qquad A_2=30,\qquad
A_j=\left[121\binom{j-3}{0}+168\binom{j-3}{1}+72\binom{j-3}{2}\right]A_{j-1}
\quad(j\ge3).
$$

No assertion at $j=0$ or about every product formula in the source's data is included. Preregistration: https://github.com/the-omega-institute/trureturing/issues/21331.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Actual permutations on $[n]$; all pairwise strict comparisons | `PackingMaximumRefutation.count`, `SourcePacking`, `Packs` | Positions and values both decrease by one; no quotient by symmetry. |
| Pattern $135289467$, overlap $3$ | Literal zero-based vector in `claim`, overlap argument $3$ | The vector is inlined in the public claim; the proof uses the Core pattern. |
| Prescribed starts and exact length; extra occurrences allowed | `windowIndex`, `Packs`, `count` | Existing definitions are reused; no avoidance condition. |
| Factors in the displayed binomial basis from $j=3$ | Third conjunct of `claim` | Every natural $j$ with $3\le j$ is quantified; the coefficient expression is literal. |
| Initial normalization of the same count | First two conjuncts of `claim` | $A_1=1$ and $A_2=30$ are proved for the same source cardinality. |

## Motivation

The inverse pattern gives a chain of comparisons in each window. Ordering positions by their values converts a packing to a word of labels. A fixed seven-label head has two orders; the remaining order constraints admit a six-label recursion. This explains the polynomial factor through disjoint shuffle cases.

## Gap

The fixed-pattern assertion is proved by `BlitvicKammounSteingrimsson135289467Product.result`. Classification of other patterns with the same mechanism, a theorem for all polynomial product factors, and the separate pattern-$14325$ congruence remain open here.

## Route

The imported `PackingMaximumRefutation` owns the literal source packing count. The Core module supplies the inverse-pattern chain correspondence and the residual order relations. The settling module constructs the inverse rank correspondence, splits off the two possible heads, and computes the second base through two chain shuffles. Its `result` combines these with `BKS10Residual.residual_recurrence` and `BKS10Gluing.binomial_factor`.

For residual size $s$, the two shuffle cases contribute
$\binom{s+3}{2}+\binom{s+4}{2}=(s+3)^2$.
With $s=6j-10$ this is $(6j-7)^2$, equal to the source's binomial expression. Iterating the recurrence gives $A_j=30\prod_{t=3}^{j}(6t-7)^2$ for $j\ge2$; this displayed product is a prose consequence of the kernel-checked recurrence, not a separate public Lean theorem.

## Falsifier

An incorrect packing/word correspondence, an omitted comparison between the six removed labels and the surviving labels, a failure of exhaustiveness or disjointness of the two head/shuffle cases, or a wrong initial count would invalidate the route. The Lean proofs establish the corresponding equivalences and exact cardinalities for all stated parameters; the independent finite checks below test their original comparison presentations.

## Evidence

The settling declaration is `D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson135289467Product.result : claim`. Both new modules have `generality: I` and `utility: none`; the occurrence count is unbounded. The settling admission basis is `open-problem-resolution (#21331; Proved)`; the supporting Core source has `escape-witness` admission basis.

The Scribe's Proved resolution names this dossier and the settling declaration. Escape audit is unfinished for the public theorem targets named in https://github.com/the-omega-institute/trureturing/issues/22588. No four-slot registration is claimed validated.

### Independent computation

The experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/4d71187d9d6b130700eead37199ca57be8707648/docs/reports/blitvic-kammoun-steingrimsson-135289467-overlap-3-product), file `check.py`, SHA-256 `7d9a7b1c86a997abf15ea4bbd149da2c57ebb1d95c300ad143ab52b94862504c`. The referenced blob exists at that revision. Executing its exact bytes with `python3 /tmp/op-bks10-stageb-check.py` exits 0 and reports `ALL_CHECKS_OK`.

Original-window ideal counting gives, for $j=1,\ldots,9$,
$1$, $30$, $3630$, $1049070$, $554958030$, $466719703230$, $571731636456750$, $961080880883796750$, and $2123027665872307020750$.
The check visits 47024 ideals at $j=9$ and independently enumerates all $9!$ permutations at $j=1$. It checks chains, the seven-element head and residual comparisons for $j=2,\ldots,12$, with gluing from $j=3$, and generic gluing on 76 forward-edge DAG presentations on zero through four vertices. These are presentations, not 76 poset isomorphism classes. Finite computation supplies no uniform proof beyond these ranges.

## Triage

1. **Computed:** the recurrence cannot extend to $j=2$: the experiment gives $A_1=1$, $A_2=30$, while $(6\cdot2-7)^2A_1=25$. The separate second base count is essential. Evidence: the pinned experiment and command above, exit 0.
2. **Proved in prose:** the square factor is the sum of two disjoint shuffle cases. For a fixed survivor word of length $s$, if $b$ precedes $e$, the forced prefix is $a,b,e$, leaving a chain of length $s+1$ shuffled with $u<v$, hence $\binom{s+3}{2}$ choices. If $e$ precedes $b$, the prefix is $a,e$, leaving a chain of length $s+2$ shuffled with $u<v$, hence $\binom{s+4}{2}$ choices. The cases are disjoint and exhaustive. Their sum is $[(s+3)(s+2)+(s+4)(s+3)]/2=(s+3)^2$.
3. **Proved in prose:** the gluing cardinality formula applies to every finite survivor language $T$ of permutations of one common label list $L$ disjoint from the six markers. Apply the preceding case count separately to each survivor word. Filtering to $L$ uniquely recovers that word, so the assembled sets for different words are disjoint. Every assembled word has precisely one of the two cases. Thus the total is $(|L|+3)^2|T|$. This uses no internal relation of a survivor beyond membership in $T$ and its permutation of $L$. Repeated labels in $L$ do not affect this recovery argument.
4. **Computed:** the independent checker agrees with the target through $j=9$, checks decomposition through $j=12$, and checks generic gluing on 76 DAG presentations. Evidence: the pinned experiment, command, exit 0 and SHA-256 above. Uniform extensions of these finite tests are not asserted by computation; the main recurrence instead has its separate Lean proof.
5. **Open:** classification of other patterns with this gluing mechanism; no assertion about all polynomial product factors.
6. **Open:** the separate pattern-$14325$ modulo-$10$ observation is outside this settlement.

### What the settlement shows

**Kernel-checked:** `result` proves both base counts and the recurrence with exactly the source's binomial coefficients for every $j\ge3$. The decisive mechanism is the six-label removal with a shift of the survivor relations, followed by the two disjoint shuffle cases. **Proved in prose:** their square multiplier is independent of the survivor language's internal constraints, as derived above. **Computed:** the exact finite scopes are those of items 1 and 4. **Open:** recognizing all patterns with this recursion and explaining all polynomial product factors. No change to the source's other results is claimed: its general packing correspondence is reused, and neither the packing-maximum question nor the item-11 congruence is a consequence of this settlement.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The bounded screen recorded in #21331 covers the primary v1, citation indexes, title and fixed-pattern searches, related cluster/poset enumeration work, and the source's references. It located no settlement of this fixed-pattern assertion in the searched scope. Unpublished work and the cited manuscript in preparation were not read. No worldwide-priority claim is made. The original pattern-packing correspondence and ordinary binomial shuffle counting are prior results.
