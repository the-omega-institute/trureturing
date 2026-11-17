---
bibkey: hatcher2002algebraic
authors: Allen Hatcher
year: 2002
title: Algebraic Topology
doi: null
url: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf
claim: "The alternating simplex boundary has square zero and defines the simplicial chain complex. The ordinary quotient join satisfies the classical sphere identity S^m * S^n homeomorphic to S^(m+n+1). Circle power maps are covering spaces, with lifts governed by the covering-space lifting criterion."
strata_touched: []
license: citation-only
triage: anchor
---

# Simplicial boundary convention

The [author-hosted book](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
Section 2.1, pp. 105–106, defines the alternating deletion boundary and
proves its square is zero in Lemma 2.1. These are PDF pages 114–115.
The displayed complex there is unaugmented at degree zero. The consumer
explicitly adds the empty-face line in degree minus one and sends each
vertex to its unit; the edge boundary still has augmentation zero.

This supplies the chain convention in
[the five-face projection](../../docs/develop/theory/AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md),
Definition 22.1 and Theorem 22.2. Exterior degree is one more than the
chain degree in that chosen basis dictionary. The citation supplies
neither a chain retraction onto the sparse support nor a homology
interpretation of a probability-observation kernel.

# Ordinary joins and the sphere identity

## Locator

Source: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf

Chapter 0, “Operations on Spaces,” printed p. 9 (PDF page 18), defines
the ordinary join $X * Y$ as the quotient of $X \times Y \times I$ by
$(x,y_1,0) \sim (x,y_2,0)$ and
$(x_1,y,1) \sim (x_2,y,1)$. Thus the zero end retains $X$ and the one
end retains $Y$. The same page describes the iterated join of $n$
copies of the two-point sphere $S^0$, for $n \geq 1$, using the two unit
vectors on each coordinate axis, and gives a homeomorphism to $S^{n-1}$
by radial projection from the origin.

Chapter 0, Exercise 18, printed p. 19 (PDF page 28), asks to show
$S^1 * S^1 = S^3$ and, more generally, $S^m * S^n = S^{m+n+1}$.
This is the literature attribution for the classical homeomorphism
identity, stated as an exercise rather than a supplied proof.

The Euclidean sphere join consumer uses this ordinary quotient convention
and realizes the identity for every natural pair of dimensions, including
zero, with actual Euclidean unit spheres and their subspace topologies.
Its explicit intermediate maximum-norm normalization, coordinate
concatenation, and selected first-coordinate endpoint formula are local
refinements. These locators do not prescribe those formulas or certify an
information-escape registration, and do not resolve Carnero Bravo
Question 22.

# Circle power covers and lifting

The [author-hosted Chapter 1](https://pi.math.cornell.edu/~hatcher/AT/ATch1.pdf),
printed p. 56 (chapter PDF page 36), describes the covering
$p:S^1\to S^1$, $p(z)=z^n$, for positive integers $n$, with $|z|=1$.
Proposition 1.33, printed p. 61 (chapter PDF page 41), states the
based lifting criterion for a path-connected, locally path-connected
source $Y$: a lift of $f:(Y,y_0)\to(X,x_0)$ through
$p:(\widetilde X,\widetilde x_0)\to(X,x_0)$ exists exactly when
$f_*(\pi_1(Y,y_0))\subseteq p_*(\pi_1(\widetilde X,\widetilde x_0))$.

These are classical covering-space context for the matrix application in
[CircleDoubleCoverNoSection](../../Blueprint/D5/S3/ConceptDynamics/Topology/CircleDoubleCoverNoSection.md).
Its real rank-one projector field and factor-to-square-root correspondence
are derived there from the existing Lean no-section theorem and pinned
Mathlib matrix APIs. The citation alone is not a Lean certificate for the
matrix application and makes no originality or physical claim.

# Related source: line bundles and continuous frame selection

Allen Hatcher, *Vector Bundles & K-Theory*, version 2.2 (2017).

The [author-hosted version 2.2](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf),
Section 1.1, printed p. 7 (PDF page 11), identifies the Mobius bundle
with the canonical line bundle over $\mathbb{RP}^1\cong S^1$ through
the endpoint relation $(0,x)\sim(\pi,-x)$. Printed p. 8 (PDF page 12)
states that a rank-$n$ vector bundle is isomorphic to the trivial bundle
exactly when it has $n$ sections that are linearly independent in every
fiber. The same page distinguishes the Mobius bundle from the product
bundle using the complement of the zero section.

This supplies classical bundle context for the distinction between
pointwise factors and globally continuous frame selection in
[CircleDoubleCoverNoSection](../../Blueprint/D5/S3/ConceptDynamics/Topology/CircleDoubleCoverNoSection.md).
The application proves its obstruction using the existing Lean circle
no-section theorem, without assuming a bundle classification theorem.
Neither these locators nor the application assert physical realization
or a dynamics law. Only bibliographic attribution and paraphrase are used;
no source text or proof is copied into Lean.
