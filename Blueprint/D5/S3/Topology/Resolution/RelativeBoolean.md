# Relative Boolean graph resolution

## Abstract

The closure of the actual boundary-avoiding membership graph gives a compact zero-dimensional relative resolution with coherent continuous pair-map lifts.

Observation(C) consists of all actual subsets A of X whose ambient frontier misses every point of C. Cube(C) is Observation(C)→Bool, with Bool discrete. evaluation(C,x)(A) is actual membership of x in A, including nonopen A. graph(C,x)=(x,evaluation(C,x)); carrier(C) is the closure of its range in X×Cube(C), and Space(C) is that closed subtype. point(C,x) is the actual graph point, projection(C) is its first coordinate, and coordinates(C) is the cube coordinate. Global continuity of evaluation or graph is not assumed.

**Theorem 1.1 (Separating neighborhoods avoiding the core boundary).**

$$\begin{aligned}\forall X: \operatorname{Type}\left(u\right), {}[\operatorname{TopologicalSpace}\left(X\right)] \\\forall C: \operatorname{Set}\left(X\right), \\{}[\operatorname{CompactSpace}\left(X\right)] \\{}[\operatorname{T2Space}\left(X\right)] \\\operatorname{IsClosed}\left(C\right) \Rightarrow \\{}[\operatorname{TotallyDisconnectedSpace}\left(C\right)] \\\forall U: \operatorname{Set}\left(X\right), \operatorname{IsOpen}\left(U\right) \Rightarrow \forall x: X, x \in U \Rightarrow \\\exists V: \operatorname{Set}\left(X\right), \operatorname{IsOpen}\left(V\right) \land x \in V \land\\\operatorname{closure}\left(V\right) \subseteq U \land \forall c \in C, \neg{c \in \operatorname{frontier}\left(V\right)}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RelativeBoolean.exists_open_closure_subset_avoiding_frontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bernhard Banaschewski (1955). *Über nulldimensionale Räume*. DOI: [10.1002/mana.19550130302](https://doi.org/10.1002/mana.19550130302). URL: <https://doi.org/10.1002/mana.19550130302>.

*Commentary.*

Off C, shrink the closed singleton inside U minus C. On C, choose a clopen D in the compact subspace C containing x and contained in U. The ambient images K of D and L of its complement are closed. Normal shrinking gives K⊆V⊆closure(V)⊆U minus L. Points of D are inside V and all other core points are outside its closure. The frontier therefore misses C. This covers every x in U, including the cases C empty and D equal to all C.

**Theorem 1.2 (The actual resolution and coherent lifts).**

$$\begin{aligned}\forall X: \operatorname{Type}\left(u\right), {}[\operatorname{TopologicalSpace}\left(X\right)] \\\forall C: \operatorname{Set}\left(X\right), \\{}[\operatorname{CompactSpace}\left(X\right)] \\{}[\operatorname{T2Space}\left(X\right)] \\\operatorname{IsClosed}\left(C\right) \Rightarrow \\{}[\operatorname{TotallyDisconnectedSpace}\left(C\right)] \\\forall Xprime: \operatorname{Type}\left(v\right), {}[\operatorname{TopologicalSpace}\left(Xprime\right)] \forall Cprime: \operatorname{Set}\left(Xprime\right), \\\forall Xbis: \operatorname{Type}\left(w\right), {}[\operatorname{TopologicalSpace}\left(Xbis\right)] \forall Cbis: \operatorname{Set}\left(Xbis\right), \\\forall h: X \to Xprime, \forall hh: \operatorname{Continuous}\left(h\right), \forall hC: \operatorname{MapsTo}\left(h, C, Cprime\right), \\\forall k: Xprime \to Xbis, \forall hk: \operatorname{Continuous}\left(k\right), \forall kC: \operatorname{MapsTo}\left(k, Cprime, Cbis\right), \\\operatorname{CompactSpace}\left(\operatorname{Space}\left(C\right)\right) \land \operatorname{T2Space}\left(\operatorname{Space}\left(C\right)\right) \land \operatorname{IsTopologicalBasis}\left(\operatorname{setOf}\left(U: \operatorname{Set}\left(\operatorname{Space}\left(C\right)\right) \mapsto \operatorname{IsClopen}\left(U\right)\right)\right) \land\\\operatorname{Continuous}\left(\operatorname{projection}\left(C\right)\right) \land \operatorname{Surjective}\left(\operatorname{projection}\left(C\right)\right) \land \operatorname{Continuous}\left(\operatorname{lift}\left(h, hh, hC\right)\right) \land\\\operatorname{lift}\left(id, continuousId, \operatorname{mapsToId}\left(C\right)\right) = id \land\\\operatorname{lift}\left(\operatorname{compose}\left(k, h\right), \operatorname{comp}\left(hk, hh\right), \operatorname{comp}\left(kC, hC\right)\right) = \operatorname{compose}\left(\operatorname{lift}\left(k, hk, kC\right), \operatorname{lift}\left(h, hh, hC\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RelativeBoolean.functorial_resolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bernhard Banaschewski (1955). *Über nulldimensionale Räume*. DOI: [10.1002/mana.19550130302](https://doi.org/10.1002/mana.19550130302). URL: <https://doi.org/10.1002/mana.19550130302>.

*Commentary.*

X, Xprime and Xbis have independent universe levels u, v and w. The compact Hausdorff and closed zero-dimensional hypotheses are imposed only on the source pair (X,C). The pair maps h and k are continuous and send their distinguished subsets into the next ones. No compactness or separation is needed for their codomains to construct the lifts. compose(k,h) means k after h.

Every bit of a closure point constrains its base point: bit true puts it in closure(A), and bit false in closure(complement A). An explicit closed union containing the entire graph proves these constraints. The separating-neighborhood lemma then rules out different base points with identical cube coordinates. Thus coordinates(C) is injective. Compactness makes it a closed embedding into the binary cube; total disconnectedness pulls back, and the compact Hausdorff clopen-basis theorem gives the displayed basis. The ambient X×Cube(C) is not assumed zero-dimensional.

Compactness and Hausdorffness of Space(C) come from the closed subtype of the compact Hausdorff product. The actual graph points witness surjectivity of projection(C), even when graph is discontinuous. Empty X yields empty Space(C).

For an admissible target A, pullback(h,A) is the actual inverse image. Continuous.frontier_preimage_subset proves its admissibility. ambientMap(h) sends (x,t) to (h(x), A↦t(pullback(h,A))). Coordinatewise continuity makes this ambient map continuous. It sends each actual graph point to graph(Cprime,h(x)); MapsTo.closure therefore restricts it to lift(h,hh,hC). Projection commutes with h and lift sends point(C,x) to point(Cprime,h(x)). Identity and composition are exact equalities of these same subtype functions, using identity and composition of actual inverse images. Neither openness nor injectivity nor surjectivity of h or k is used.

**Theorem 1.3 (Singleton fibers at distinguished points).**

$$\begin{aligned}\forall X: \operatorname{Type}\left(u\right), {}[\operatorname{TopologicalSpace}\left(X\right)] \\\forall C: \operatorname{Set}\left(X\right), \\\forall c: X, c \in C \Rightarrow \\\operatorname{preimage}\left(\operatorname{projection}\left(C\right), \operatorname{singleton}\left(c\right)\right) = \operatorname{singleton}\left(\operatorname{point}\left(C, c\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RelativeBoolean.fiber_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bernhard Banaschewski (1955). *Über nulldimensionale Räume*. DOI: [10.1002/mana.19550130302](https://doi.org/10.1002/mana.19550130302). URL: <https://doi.org/10.1002/mana.19550130302>.

*Commentary.*

This theorem needs only a topological X and c in C. Since c avoids every admissible frontier, membership in each A or its complement places c in the corresponding interior. The forced-coordinate constraints determine every bit to be evaluation(C,c). Thus every point over c equals the actual graph point point(C,c). Compactness, closedness and zero-dimensionality of C are unnecessary for this fiber assertion.

**Definition 1.4 (The full inverse image of the core).**

$$\begin{aligned}\forall X: \operatorname{Type}\left(u\right), {}[\operatorname{TopologicalSpace}\left(X\right)] \\\forall C: \operatorname{Set}\left(X\right), \\\operatorname{coreHomeomorph}\left(C\right): \operatorname{Homeomorph}\left(C, \operatorname{subtype}\left(y: \operatorname{Space}\left(C\right) \mapsto \operatorname{apply}\left(\operatorname{projection}\left(C\right), y\right) \in C\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Topology/Resolution/RelativeBoolean.coreHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bernhard Banaschewski (1955). *Über nulldimensionale Räume*. DOI: [10.1002/mana.19550130302](https://doi.org/10.1002/mana.19550130302). URL: <https://doi.org/10.1002/mana.19550130302>.

*Commentary.*

sectionC(C) sends a subtype point c of C to point(C,c). For each admissible A the trace of A on C is clopen: its two membership choices are locally constant at every c. The indicator continuity criterion and product continuity prove the actual section continuous. coreHomeomorph(C) uses this section as forward map and projection as inverse on the full inverse image. The inverse laws use the singleton-fiber theorem. This homeomorphism also needs only a topological X.

The underlying compactification is classical Stone/Banaschewski, interpreted through the Michael modification. The bibliographic source and inspected scope are in Library/Topology/banaschewski1955nulldimensional.md. The explicit relative construction and proofs here make no novelty claim. No shadowing, finite-name, period or unrestricted Peng Question 5.1 result is asserted.

## References

- Truth anchor: `D5/S3/Topology/Resolution/RelativeBoolean.coreHomeomorph`
- Truth anchor: `D5/S3/Topology/Resolution/RelativeBoolean.exists_open_closure_subset_avoiding_frontier`
- Truth anchor: `D5/S3/Topology/Resolution/RelativeBoolean.fiber_singleton`
- Truth anchor: `D5/S3/Topology/Resolution/RelativeBoolean.functorial_resolution`
