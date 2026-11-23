---
slug: rossi-2026-irredundant-atom-sizes
bibkey: rossi2026permutohedron
doi: 10.48550/arXiv.2611.25741
url: https://arxiv.org/abs/2611.25741v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Geometry/Permutohedra/IrredundantAtomSizes.exact_spectrum
---

# Rossi’s irredundant atom sizes

## Problem

Giovanni Rossi asks, “Which sizes between $2$ and $\mathrm{rk}\,x$ occur for minimal sets of
atoms generating $x$?” Take the type-A permutohedron on $n\ge 3$ labels. Its non-bottom
faces correspond to ordered partitions, with order given by merging adjacent blocks.
A partition with $b$ blocks has rank $n-b$. The atoms are the singleton-block partitions,
and the empty join is the added bottom. For every face $x$ of rank at least two and
every natural $k$, ask for a $k$-element set of atoms whose join is $x$ and whose
proper subsets all have joins strictly below $x$.
[arXiv:2611.25741v1, §10.3 item 4, first question](https://arxiv.org/html/2611.25741v1#S10.I3.i4)

## Motivation

The two extremal sizes do not determine which intermediate sizes occur. A construction
must keep exactly the cuts of $x$ while ensuring that each atom contributes a separate
obstruction to recovering a further cut.

## Gap

Proposition 5.5 gives the extremal sizes. The bounded search found the ordered-partition
presentation and relevant prefix infrastructure. No source in that search settled all
intermediate sizes. [Proposition 5.5](https://arxiv.org/html/2611.25741v1#S5.Thmtheorem5)
· [Preregistration and search scope](https://github.com/the-omega-institute/trureturing/issues/33384)

## Route

Identify each ordered partition with its chain of proper cumulative cuts. Extend the chain
of $x$ to a permutation flag and split the free ranks into $k$ nonempty groups. Within
each group apply the adjacent exchanges in list order to the current permutation. Each
exchange changes just its own prefix rank, even when consecutive exchanges share a
position. The resulting atoms share exactly the cuts of $x$. Deleting the atom belonging
to a group restores a prefix at any rank in that group. Monotonicity of finite joins
then gives strict loss for every proper subset.

For an irredundant set of at least three atoms, deletion of each atom gains a cut belonging
to every retained atom. Such cuts have free ranks, and the assigned ranks are distinct.
This gives the upper bound. The empty join and single atoms have ranks below two. The
size-two case uses the rank hypothesis directly.

## Falsifier

A face of rank at least two missing a size in the stated interval, or an irredundant family
outside that interval, would falsify the classification. A cut restored after deleting one
atom must belong to every retained atom, and it must be absent from the original join.

## Evidence

`D5/S3/Combinatorics/Geometry/Permutohedra/IrredundantAtomSizes.exact_spectrum` proves
the classification with Lean's `IsAtom` and `Finset.sup`. The ordered-partition
equivalence identifies adjacent block merges with reverse cut inclusion and gives rank
$n-b$. The permitted axiom closure consists of `Classical.choice`, `Quot.sound` and
`propext`.

## Triage

`theorem`.

### What the settlement shows

**Proved** by `D5/S3/Combinatorics/Geometry/Permutohedra/IrredundantAtomSizes.exact_spectrum`.
Every size from two through the rank is realized on every face of rank at least two.
Partitioning the free ranks supplies witnesses uniformly, and distinct private ranks imply the
upper bound.

**Open.** The second question of item 4 asks how many irredundant generating families suffice
to cover the atoms below a face.

## ASSUMED-UNVERIFIED

Literature priority beyond the bounded search is unverified. The full text of
Billera–Sarangarajan was unavailable in the checked route.
