---
slug: mandal-neetu-dicyclic-question-63-refutation
bibkey: mandalneetu2026dicyclic
doi: 10.48550/arXiv.2602.09073
url: https://arxiv.org/abs/2602.09073v1
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.result
---

# Mandal–Neetu Question 6.3 on dicyclic subset parity

## Problem

Sagar Mandal and Neetu, *Exact and Asymptotic Counts of MSTD, MDTS, and
Balanced Sets in Dicyclic Groups*, arXiv:2602.09073v1, Question 6.3,
ask verbatim in `Main.tex`, line 792:

> Is it true that $\mathrm{S}_{\mathrm{Dic}_{4n}}(m),\mathrm{D}_{\mathrm{Dic}_{4n}}(m)  \text{ and }\mathrm{B}_{\mathrm{Dic}_{4n}}(m)$ are even integers for any positive integers $n,m$ with $n\geq 3$ and $2\leq m\leq 2n$?

The [versioned source](https://arxiv.org/src/2602.09073v1) fixes this wording.
`Main.tex` has SHA-256
`7ed61ecf73935d71b750c85a2f03f635b3669ae370d87e41f16c653c0e48f959`.
Line 120 defines the product interpretation of the paper's sum and difference
sets. Line 121 presents the actual group of order $4n$ by
$a^{2n}=1$, $b^2=a^n$ and $b^{-1}ab=a^{-1}$.

For every distinct $m$-element subset $A$ of this group, put
$AA=\{xy:x,y\in A\}$ and $AA^{-1}=\{xy^{-1}:x,y\in A\}$.
The three counts are the numbers of all such subsets with
$|AA|>|AA^{-1}|$, $|AA|<|AA^{-1}|$ and $|AA|=|AA^{-1}|$,
respectively. Lines 183–187 define these unrestricted counts; the
type-restricted counts in lines 189–193 are different quantities.

| Source clause | Lean meaning |
| --- | --- |
| every positive integer $n\geq3$, of either parity | `n : ℕ`, `3 ≤ n`; the bound supplies `NeZero n` |
| actual dicyclic group of order $4n$ | Mathlib `QuaternionGroup n`; its generator `x` corresponds to $b$ |
| every $2\leq m\leq2n$ | `m : ℕ`, `2 ≤ m`, `m ≤ 2 * n` |
| all distinct $m$-subsets | `(Finset.univ : Finset (QuaternionGroup n)).powersetCard m` |
| $AA$ | `productSet A`, the image of `A.product A` under `(x,y) ↦ x * y` |
| literal right quotient $AA^{-1}$ | `rightQuotientSet A`, the image under `(x,y) ↦ x * y⁻¹` |
| unrestricted S, D, B | `sumDominantCount`, `differenceDominantCount`, `balancedCount` |
| all three counts are even | the conjunction of `Even` on the three natural counts |
| full affirmative answer and its refutation | `claim : Prop` and `result : Not claim` |

The factors may coincide, and images remove repeated values. Each subset is
counted once; there is no conjugacy-orbit quotient or restriction to a subset
type. The natural-number bounds imply the source's positivity requirements.

## Motivation

The three comparisons partition the same family of subsets. Their common
total therefore imposes a parity constraint before any individual class
needs to be counted.

## Gap

The cited source asks for simultaneous evenness throughout its full range.
The preceding paragraph establishes only the stated odd-$n$, $m=2,3$
observations. Those observations do not restrict the quantifiers of
Question 6.3. The admissible instance $n=3$, $m=4$ has an odd total number
of subsets, obstructing the proposed conjunction.

## Route

For a finite family and two natural-valued functions, trichotomy splits the
family into the greater, smaller and equal comparison classes. The private
`comparison_partition` uses `Finset.card_filter_add_card_filter_not` twice
and elementary comparison normalization. Its consumer `counts_total`
applies this identity to the actual product and right quotient cardinalities
on `univ.powersetCard m`. `Finset.card_powersetCard` gives

$$S_G(m)+D_G(m)+B_G(m)=\binom{|G|}{m}.$$

The result consumes `counts_total` with `G = QuaternionGroup 3` and `m = 4`.
`QuaternionGroup.card` gives $|G|=12$, and Lean checks
$\binom{12}{4}=495$. The instance satisfies $n\geq3$ and
$2\leq4\leq2n$. Three even counts would have an even sum, contradicting
this odd total. No individual product-set classification is enumerated.

## Falsifier

A change to the source quantifiers, the actual group, the universe of all
distinct subsets, the right-quotient convention, the strict comparisons or
the simultaneous parity conclusion would invalidate the source mapping.
The kernel theorem is the literal negation of the full affirmative claim;
it does not select an individual odd class or prove a stronger parity law.

## Evidence

The formal result is
`D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.result`.
The canonical scoped deposit checks the closed claim/result relation and
freezes the module using the pinned Lean toolchain. Its accepted axiom
closure is exactly `propext`, `Classical.choice` and `Quot.sound`.

[Issue #28433](https://github.com/the-omega-institute/trureturing/issues/28433)
and its [immutable preregistration](https://github.com/the-omega-institute/trureturing/issues/28433#issuecomment-6736377472)
fix the literal event before mathematical execution. The
[source/reuse qualification](https://github.com/the-omega-institute/trureturing/issues/28433#issuecomment-6736994575)
records the bounded source and literature readings: no exact complete answer
was located in the accessible results. Current and private D5 declarations,
Problems, Library, theory, pinned Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` and bounded public Lean/GitHub
queries supplied no exact prior theorem. The repository recheck preserves
that conclusion within the searched scope. No matching theory volume or
atom was found for this question; freezing uses `deposit-uncovered`.

The source's question and definitions are attributed to Mandal and Neetu.
The negative answer is a repository derivation, not a theorem attributed to
those authors. This is a Tier 1 numbered subsidiary question under the
repository's external named-problem rule. The module and all three authored
proofs have `proof_shape: bind-only`, `escape_witness: none` and module
`admission_basis: open-problem-resolution`. Consumer edges are
`result → counts_total → comparison_partition`; the two private helpers
organize that live derivation and supply no separate novelty or admission
basis. There are no frozen D5 prerequisites. The five public finite-set
definitions and `claim` fix the meaning consumed by `result`.

The utility is a certified-instance refutation of the exact claim. The only
authored public theorem is the designated literal `result`; it is exempt
from four-slot escape registration. No companion theorem, Reg declaration
or new axiom is claimed. The Scribe result node binds this dossier with
`ResolutionKind.Refuted`.

## Triage

### What the settlement shows

**Proved in Lean:**
`D5/S3/FiniteGroups/SubsetProducts/DicyclicSubsetParityRefutation.result`
refutes the full affirmative answer to the cited Question 6.3. Its failure
mechanism is the joint parity obstruction: the three classes exhaust all
four-element subsets of the order-12 dicyclic group, and their total is 495.

**Prose consequence of the partition identity used in that proof:**
evenness of the total number of $m$-subsets is necessary for simultaneous
evenness of the three counts. This necessary condition alone is not
sufficient; an even total does not force its three summands to be even.
No additional standalone Lean theorem is asserted here.

**Literature scope:** the source's preceding odd-$n$, $m=2,3$ observations
remain separate published statements. This refutation neither reproves nor
contradicts them. Conjecture 6.2, tracked separately in
[issue #22887](https://github.com/the-omega-institute/trureturing/issues/22887),
and the paper's other questions receive no settlement from this result.
The Mohan–Neetu small-doubling Conjecture 6.3 concerns a different paper
and group. Any deduction requiring the full affirmative Question 6.3 loses
that premise; no such deduction is otherwise evaluated here.

**Open:** a corrected universal range, sufficient conditions for joint
evenness, and any proposed general law for the individual class parities
require independent proofs. No individual class was computed or identified
as odd in this argument.

## ASSUMED-UNVERIFIED

Worldwide absence of a prior answer and first-resolution priority remain
unverified. The bounded search had incomplete public issue-search access
and does not cover private external work. Journal-version equivalence and
later corrections are not established. The conclusion is tied to the cited
v1 wording. The resolution binding records the repository's claim; machine
validation of its shape and frozen target does not prove source-language
fidelity.
