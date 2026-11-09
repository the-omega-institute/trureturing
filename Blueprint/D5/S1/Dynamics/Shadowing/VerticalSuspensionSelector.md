# Full Integer Crossing Selector on the Actual Suspension

## Abstract

The compact locally equiconnected vertical suspension has a continuous full integer selector for every compatible metric.

**Theorem 1.1 (Every compatible metric and every sufficiently small closed tolerance).**

$$\forall K, CompactMetrizableNonempty(K) \land LocalEquiconnection(K) \Rightarrow \forall d: CompatibleMetric(Suspension(K)), \exists deltaStar>0, \exists Rstar: IntegerSelector(d,vertical,deltaStar), \forall delta, (0<delta \land delta\le deltaStar) \Rightarrow \exists R: IntegerSelector(d,vertical,delta), \forall x\in ClosedPseudoOrbit(d,vertical,delta), R(x)=Rstar(inclusion(x))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/VerticalSuspensionSelector.compact_lec_crossing_selector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

K is an arbitrary nonempty compact metrizable space. A single continuous H:W×[0,1]→K is given on an open neighborhood W of the diagonal in K×K, with H(u,v,0)=u, H(u,v,1)=v and H(u,u,s)=u. No ANR, finite dimension, connectedness, symmetry or higher arity assumption is made.

The carrier M is the native quotient of K×[-1,1]: two representatives agree precisely when their heights agree and either that height is -1, that height is 1, or their K-labels agree. The two end faces collapse separately. Its topology is the quotient topology. The theorem quantifies over every metric d inducing exactly that topology, using replaceTopology with the explicit topology equality. The vertical homeomorphism is f(q(u,v))=q(u,(v+c)/(1+cv)), c=tanh(1), and has all integer powers.

Pδ is the subtype of ALL functions x:ℤ→M satisfying d(f(x(j)),x(j+1))≤δ for EVERY integer j, with the full product subspace topology. It is closed. Translation by n is an actual homeomorphism of this same domain and is proved to equal σ^n for σ=shift(1). IntegerSelector requires a continuous map R:Pδ→M, R(orb(z))=z for every z, and R(σ^n(x))=f^n(R(x)) for every integer n and every x. All negative times and errors equal to δ are retained.

There is δstar>0 and such an Rstar on Pδstar. For every 0<δ≤δstar, the theorem also supplies an IntegerSelector on Pδ whose map is literally Rstar composed with the natural subtype inclusion. Thus all smaller tolerances use one formula. No quantitative shadowing estimate is asserted beyond this exact selector contract.

The formula locates a weak crossing j with v(j)≤0≤v(j+1), where v(j)=height(x(j)). Put A=artanh(v(j)), B=artanh(v(j+1)), s=-A/(B-A) and T=-j-s. The output is q(H(L(x(j)),L(x(j+1)),s),tanh(T)). Compact bad-pair separation gives the sign rule and the W/interior checks at every admitted link. The sign rule makes B-A positive and s lie in [0,1]. Different crossings are adjacent at a zero height; the connector endpoint identities make their outputs exactly equal.

Every all-negative history maps to the lower pole and every all-positive history to the upper pole. At a crossing, a finite closed cover in a strict-sign neighborhood proves continuity. At an arbitrary strict-sign history, the compact tube lemma supplies label-uniform pole neighborhoods; one far coordinate bounds every crossing phase in that neighborhood. This includes arbitrary nonconstant strict-sign histories and makes no tail-convergence or local-finiteness assumption at a pole class.

The crossing construction and the arctanh interpolation are attributed to the supplied Pro author formula and its independently reviewed public source proof. The formal implementation reuses pinned Mathlib artanh, quotient topology, compact extrema, compact tubes and finite pasting. This is a substantive intermediate selector theorem. It proves neither the necessity of LEC nor compact LEC implies ANR, and claims no literature novelty or official acceptance.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/VerticalSuspensionSelector.compact_lec_crossing_selector`
