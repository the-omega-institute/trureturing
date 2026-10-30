---
slug: carnero-bravo-2025-hereditary-lexicographic-products
bibkey: carnerobravo2025independenceproducts
doi: null
url: https://arxiv.org/abs/2505.06457v2
triage: theorem
motivation_gids:
  - D5/S3/Geometry/HereditaryLexicographicProduct.result
---

# Carnero Bravo's hereditary lexicographic product question

## Problem

Andrés Carnero Bravo, *On independence complexes of graph products*,
arXiv:2505.06457v2, Section 4, Question 22 asks whether, under the hypotheses
of Theorem 21, $G\circ H$ belongs to $\mathcal W$. Both graphs are finite,
have at least two vertices, and belong to $\mathcal{SW}$.
Section 2 defines $\mathcal{SP}$ as contractibility or the homotopy type of
an ordinary wedge of spheres, and $\mathcal P$ additionally permits a
disjoint union of such wedges. The hereditary classes require the respective
property on induced subgraphs. The requested conclusion is unsuspended.

The paper does not separately specify the vertexless convention. This
settlement states it explicitly: sourceSW requires SP on every nonempty
induced vertex set; the output sourceW includes every induced vertex set,
including the empty one. The native realization of a vertexless graph is
empty. Its output P witness is an empty outer coproduct, rather than a
contractible point or a nonempty ordinary wedge.
The initial preregistration sketch represented the vertexless input by an
augmented empty-sphere model. The retained statement makes that boundary
explicit through the nonempty-induced input convention and the independent
empty-output proof; it does not assert ordinary SP for an empty realization.

## Motivation

Theorem 21 proves only that each suspension $\Sigma I(F)$ has a wedge or
contractible homotopy type. A solution of Question 22 must classify the
actual $I(F)$, preserve disconnected sphere-wedge components, and cover
arbitrary induced subsets of the actual lexicographic product.
The preregistration is [issue #22745](https://github.com/the-omega-institute/trureturing/issues/22745).

## Gap

The stated theorem in the primary source does not supply the unsuspended
conclusion. The bounded literature check of 28 October 2026 did not verify a
prior complete solution to this exact general question. It did not retrieve
a complete citation set or certify global priority. The existing local
one-vertex replacement equivalence alone also leaves the concrete sphere
closures and source-model transports to prove.

## Route

Use the actual heterogeneous graph-substitution induction and its occupied
fiber transport. Compactness of finite independence realizations reduces
arbitrary source sphere-wedge and coproduct indices to finite lists without
requiring those original indices to be finite. Actual quotient/native
homeomorphisms connect these models to the finite closure carriers.

Discharge the induction's point, ordinary-join and marked-vertex-wedge inputs
with the proved finite component constructions. Restrict the actual
sigma/product graph isomorphism to each selected vertex set and transport
its independence realization. For the empty selected set, prove the
realization empty and supply zero outer components separately.

## Falsifier

The settlement would fail if SP meant suspension, if its hypotheses were
uninhabited, if sphere dimensions zero or point components were excluded,
if original wedge indices were assumed finite, or if disconnected components
were identified through their basepoints. It would also fail if any closure
or native carrier equivalence remained an assumption, if only rectangular
induced subsets were covered, or if an ordinary empty-factor join replaced
the augmented simplicial empty-link case.

## Evidence

The [owning Scribe](../Blueprint/D5/S3/Geometry/HereditaryLexicographicProduct.scribe.cs)
states the full source correspondence and proof composition.
`HereditaryLexicographicProduct.result` quantifies over arbitrary finite
vertex types and both sourceSW hypotheses, retains both order-at-least-two
premises, and concludes sourceW of the actual lexicographic product.
No closure, endpoint, native-model or HEP premise is added.

`CompactSphereNormalForm` constructs the actual finite models and their
native homeomorphisms. `FiniteComponentClosure` supplies the actual marked
wedge and ordinary join closures, including point components and every
sphere-pair, suspension and circle multiplicity.
`OccupiedFiberSubstitution.independenceHomeomorph` and the original
`FiniteGraphVertexSubstitution.hereditarySubstitutionCore` handle all
occupied induced fibers and the genuine empty-link convention.
The implementation has a successful scoped Lean report with standard
axioms only. A compiled transient edgeless-graph check also witnesses that
the sourceSW hypotheses are inhabited.

## Triage

The formal result gives the affirmative unsuspended Question 22 conclusion
under the explicit nonempty-induced SW convention above. The output includes
the empty target through a proved empty realization. Original source sphere
and component indices are unrestricted; finite witnesses are a proved output
of compactness. The settling composition uses the preregistered
open-problem-resolution admission basis; it is not presented as a new
standalone non-binding calculation.

## ASSUMED-UNVERIFIED

Global novelty, literature priority and official problem acceptance are not
claimed. The primary source leaves the vertexless input convention implicit;
this settlement must retain the explicit convention stated above.
Source-readout registrations remain unfinished under
[issue #22742](https://github.com/the-omega-institute/trureturing/issues/22742).
The compiled Reg attempt proves that its particular truth-valued readout
cannot satisfy observational dependence; it does not rule out every lawful
alternative encoding, and no new declared_validated registration is claimed.
