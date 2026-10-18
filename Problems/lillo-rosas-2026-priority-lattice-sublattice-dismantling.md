---
slug: lillo-rosas-2026-priority-lattice-sublattice-dismantling
bibkey: lillo2026prioritylattice
doi: 10.48550/arXiv.2603.28905
url: https://arxiv.org/html/2603.28905v1#S6.I1.i4
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.result
---

# Sublattice dismantling of the priority lattice

## Problem

Adrián Lillo and Mercedes Rosas, *The Priority Lattice*, arXiv:2603.28905v1,
[Section 6, item 4](https://arxiv.org/html/2603.28905v1#S6.I1.i4), ask:

> A sublattice dismantling is a subdivision of a lattice into two non-empty sublattices. A lattice is sublattice dismantlable if it can be decomposed into 1-element lattices by consecutive sublattice dismantlings. We have checked with the help of SageMath that $\Pi(n)$ is sublattice dismantlable for $n=$ 1 to 5. Is this always the case?

The question quantifies over every positive integer $n$. The source's priority
forests are increasing rooted forests on $0,\ldots,n$ with interval components.
Their order is edge containment, with an additional greatest element.
The existing `PrincipalFilters.Pi` is this literal carrier, and `coreOrderIso`
identifies it with `WithTop (IntervalForest n)`.

A subdivision is read as a disjoint partition into nonempty sublattices, closed
under the ambient binary meet and join, without requiring the ambient bounds.
The identical definition and the interval/complement split in
[Sage's immutable implementation](https://github.com/sagemath/sage/blob/133eb21d995e6aa5b6de2cd8db798a442e5cc033/src/sage/combinat/posets/lattices.py#L4032)
support this standard meaning. The source does not separately say “disjoint”.
The authors' historical Sage version and exact call are unknown. Evidence of an
intended overlapping-cover meaning would invalidate this semantic bridge.

## Motivation

The answer is negative: $\Pi(6)$ is not sublattice dismantlable.
The declaration `SublatticeDismantling.result` has the exact type `¬ claim`,
where `claim : Prop` is
`∀ n : Nat, 1 ≤ n → Dismantlable (Set.univ : Set (Pi n))`.
Thus one positive parameter refutes the whole universal question.

## Gap

An abstract seventeen-element obstruction answers this source question only after its members are valid priority forests and its binary operations are actual ambient extrema. The construction below supplies that bridge, the hereditary restriction of recursive dismantling, and transport to the literal source carrier.

## Route

Put

$$F=\{(0,1),(0,2),(3,4),(3,5)\},$$

and, for $i,j\in\{0,1,2\}$, put

$$A_i=F\cup\{(i,3)\},\qquad B_j=F\cup\{(3+j,6)\},$$
$$C_{ij}=F\cup\{(i,3),(3+j,6)\}.$$

The set $S$ contains $F$, the six $A_i,B_j$, the nine $C_{ij}$ and the actual
ambient top: sixteen forests plus top, seventeen elements in total.
The component intervals are $[0,2],[3,5],\{6\}$ for $F$;
$[0,5],\{6\}$ for $A_i$; $[0,2],[3,6]$ for $B_j$; and $[0,6]$ for $C_{ij}$.
The Lean constructors prove the local interval condition and increasingness
required by `forestOfLocal`. The parents of vertices 3 and 6 distinguish all
sixteen forests; top is distinct from every forest.

For these particular forests, intersections remain valid and are ambient meets.
Compatible unions remain valid and are ambient joins. Conflicting parent
assignments have no forest upper bound, so their join is the actual top.
The proofs quantify over arbitrary ambient lower and upper bounds. They do not
assume the paper's unrestricted printed intersection/union formula, which need
not produce a valid interval forest on arbitrary inputs.

The resulting sublattice is the incidence lattice of $K_{3,3}$. Its least element
is $F$, its six atoms are $A_i,B_j$, and its nine coatoms are $C_{ij}$.
It has no nontrivial partition into two sublattices. If its bounds are separated,
the diagonal coatoms $C_{00},C_{11},C_{22}$ have pairwise meet $F$ and join top;
neither part can contain two of them. If the bounds are together, the other
part contains at most one atom and one coatom. A lone coatom is forced by its
endpoint atoms, while any atom has three incident coatoms, at least two in the
opposite part, whose meet forces that atom there. Both cases contradict closure.
The formal Boolean proof checks closure implications for the complete finite
operation table, without a computation-trust axiom.

Finally, dismantlability passes to every nonempty ambient sublattice. Intersect
the recursive subdivision tree with that sublattice. Equal ambient extrema
prove closure of intersections; empty child intersections are discarded, and
two nonempty children retain a valid disjoint partition. Hence a dismantling of
$\Pi(6)$ would dismantle $S$, which has no first split. The existing order
isomorphism transports the recursive predicate to the literal source carrier.

## Falsifier

An invalid interval forest, a failure of the ambient extremum proof, a collision
between distinct forest codes, a nontrivial closed two-part partition of $S$,
a failure of hereditary restriction, or evidence that the source means an
overlapping cover would invalidate the corresponding step. Every algebraic
step of the delivered conclusion is expressed in the Lean source; the source
interpretation retains the stated semantic boundary.

## Evidence

The [Lean module](../D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.lean) proves the exact negation of the all-positive-size claim. The axiom closures of its declarations are contained in `{propext, Classical.choice, Quot.sound}`. The proof uses actual ambient extrema and no computation-trust axiom.

The [Scribe source](../Blueprint/D5/S3/Combinatorics/PriorityLattice/SublatticeDismantling.scribe.cs) links the recursive definition, hereditary restriction, source-order transport, embedding, ambient meets and joins, and partition obstruction to their compiled declarations. Its settling node carries one `OpenProblemResolutionClaim` with `ResolutionKind.Refuted` for this dossier.

## Triage

The refutation does not challenge the authors' reported checks for $1\le n\le5$.
It proves neither those checks nor a minimality theorem. Padding the displayed
forests with isolated larger labels suggests the stronger $n\ge6$ statement;
that extension is not claimed as a separate kernel-checked result here.
The other final-section questions retain their own status. No principal-ideal,
principal-filter, or forest-count theorem is counted as new content.

The abstract incidence-lattice obstruction is background. The source-specific
content is the actual forest embedding, its ambient extrema, hereditary
restriction including empty branches, and the whole universal negation.

## ASSUMED-UNVERIFIED

The exact v1 question and source forest/order definitions are retained in the
[Library note](../Library/GraphInvariants/lillo2026prioritylattice.md).
The completed bounded primary/arXiv and repository searches found no equivalent
prior settlement. This is not exhaustive publication-priority clearance;
absence of every earlier published or unpublished resolution remains
`ASSUMED-UNVERIFIED`. The source's reported small-size computations are not
assumptions of the refutation.
