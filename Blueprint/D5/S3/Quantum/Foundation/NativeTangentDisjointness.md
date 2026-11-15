# Native tangent disjointness on the full original carrier

## Abstract

Original weak exclusion-ball geometry forces distinct neighbor tangents to have zero intersection.

Source: VIII108.1-108.6 of QUANTUM_ORIGIN_EXCLUSION_SEGMENT_RIGIDITY_AND_PURE_LOCUS_TOPOLOGY_VIII. The same nonzero finite dimensional real V, closed pointed generating C and strictly positive original u determine the entire base K, every original extreme point P and the entire proper-effect interval [0,u]. W means only exclusionBalls with each entire D_p a Euclidean ball of positive dimension, and weakPair on original orthogonal pairs. No finiteness of P, common center, fullPair, numerical reciprocity, global metric, tangent covering or projection is assumed.

**Definition 1.1 (Directions of the entire exclusion ball).**

Lean statement: `D5/S3/Quantum/Foundation/NativeTangentDisjointness.directions`

*Formalization.* `D5/S3/Quantum/Foundation/NativeTangentDisjointness.directions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

directions b is vectorSpan over the reals of the whole original exclusion set D_q. Its equality with the range of the actual chart's linear part follows by mapping the vector span of the whole coordinate closed unit ball, whose affine span is the full coordinate space. For the center c_q=b.param(0), this is precisely lin(D_q-c_q), independently of the chosen entire chart.

**Definition 1.2 (Intrinsic tangent at the original point).**

Lean statement: `D5/S3/Quantum/Foundation/NativeTangentDisjointness.tangent`

*Formalization.* `D5/S3/Quantum/Foundation/NativeTangentDisjointness.tangent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

tangent b a_p is directions b intersect ker(a_p). Given any pure p in D_q, pull it back to a unit chart coordinate e. Apply the existing affine_zero_antipode theorem to the nonnegative affine function 1-a_p on the entire ball. Its nonzero diameter coefficient follows from an original joint companion where a_p vanishes. Thus a_p(b.param.linear(w))=0 forces inner(e,w)=0. All actual tangents are covered, with no extra orthogonality premise in the theorem. The definition includes dimension-one balls and their zero tangent.

**Theorem 1.3 (Distinct original neighbors have zero tangent intersection).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] [\operatorname{Nontrivial}\left(V\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in V,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\right) \Rightarrow \left(\operatorname{exclusionBalls}\left(C, u\right) \Rightarrow \left(\operatorname{weakPair}\left(C, u\right) \Rightarrow \left(\exists a \in \operatorname{Function}\left(\operatorname{pure}\left(C, u\right), \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right)\right),\; \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \operatorname{common}\left(C, u, p, \operatorname{apply}\left(a, p\right)\right)\right) \land \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall f \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{common}\left(C, u, p, f\right) \Rightarrow f = \operatorname{apply}\left(a, p\right)\right) \land \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \forall q \in \operatorname{pure}\left(C, u\right),\; \forall qprime \in \operatorname{pure}\left(C, u\right),\; q\in \operatorname{exclusion}\left(C, u, p\right) \Rightarrow \left(qprime\in \operatorname{exclusion}\left(C, u, p\right) \Rightarrow \left(q\neq qprime \Rightarrow \left(\forall b \in \operatorname{ExclusionChart}\left(C, u, q\right),\; \forall bprime \in \operatorname{ExclusionChart}\left(C, u, qprime\right),\; \operatorname{inf}\left(\operatorname{tangent}\left(b, \operatorname{apply}\left(a, p\right)\right), \operatorname{tangent}\left(bprime, \operatorname{apply}\left(a, p\right)\right)\right) = \operatorname{bot}\left(\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/NativeTangentDisjointness.whole_native_tangent_disjointness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Directly consume CommonPositiveExtension.whole_arc_effect: one family a of actual common effects, its uniqueness, and the full-space ArcFamily. For each nonzero common candidate z, each actual chart yields independent positive h=1/norm(w), an original opposite r, a signed B with B(z)=1/(2h), vanishing on the whole span of p and D_p, and the all-space circle identity. The map w is the actual chart preimage of the SAME vector z. The two coordinate norms remain independent.

Every real pair c,s with c squared plus s squared equal to one is realized by an angle, using pinned mathlib Complex.arg, cos_arg and sin_arg. Consequently the supplied circle consists of actual original pure states, with state expression ((1+c)/2)p+((1-c)/2)r+s h z and corresponding original effect ((1+c)/2)a_p+((1-c)/2)a_r+s B. This obtains the rational half-angle states from original sphere points, not arbitrary formal perturbations.

$\operatorname{x}\left(t\right) = \frac{{t}^{2} \cdot p + r + 2 \cdot h \cdot t \cdot z}{1 + {t}^{2}} \land y = \frac{p + rprime + 2 \cdot hprime \cdot z}{2}$

For every original neighbor v in D_p, its original positive a_v vanishes at p. Evaluating it on the rational native circle and multiplying by the positive denominator gives a_v(r)t squared+2h a_v(z)t nonnegative for every real t. The existing quadratic discriminant theorem forces a_v(z)=0. This is the needed original 108.4 annihilator consequence, proved without N_p or a projection and without assuming the unpaid full VII105.5.

Fix the second native circle state y=(p+rprime+2hprime z)/2, and evaluate the SAME actual original effect at the SAME y. For the first circle use c=(t squared-1)/(1+t squared), s=2t/(1+t squared). Its original positivity gives t squared+c0+2(hprime/h)t nonnegative, where c0=a_r(rprime). Substitute t=-hprime/h to obtain (hprime/h) squared<=c0; exchange the charts for (h/hprime) squared<=c1 with c1=a_rprime(r). No equality of c0 and c1 is used.

${\frac{hprime}{h}}^{2} \le \operatorname{apply}\left(\operatorname{apply}\left(a, r\right), rprime\right) \land {\frac{h}{hprime}}^{2} \le \operatorname{apply}\left(\operatorname{apply}\left(a, rprime\right), r\right)$

The actual singleton intersections from whole_joint_completion imply distinct neighbors have distinct opposite points. If a_r(rprime)=1, the first original frame sum and a_p(rprime)=0 force a_q(rprime)=0. Both r and rprime then lie in the same singleton D_p intersect D_q, a contradiction. Hence both cross readings are strictly below one. Their nonnegativity and the two reciprocal scale bounds imply 1<=c0 c1<1. This proves zero intersection for every pair of full charts.

The live new inference is the original tangent annihilation and the combination of two independently scaled native arc families through actual original state-effect positivity. Pure scalar normalization is only an internal step. Reused source suppliers are protected dependencies; this consumer does not approve, freeze, cover or settle the separate VII105.4 delivery. Full VII105.3 spectral generation, VII105.5 projectivity, VIII108.7 dimensions and VIII109 reconstruction remain outside this result. No physical realization, global classification or literature novelty is claimed.

The same-delivery Reg mirror reconstructs the complete original telescope and proves its actual-positive law. A complete Contract.Registration value additionally needs a lawful enrolled readout, whole-family intervention/sensitivity, observational dependence and exact sourceSelection evidence. The attempted whole-theorem observation has State=Unit, so it cannot supply two unequal state readouts; a faithful varying observation and its exact source reconstruction remain missing. These unfinished slots are tracked in https://github.com/the-omega-institute/trureturing/issues/29702. Compiled source reconstruction alone is not declared_validated.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/NativeTangentDisjointness.directions`
- Truth anchor: `D5/S3/Quantum/Foundation/NativeTangentDisjointness.tangent`
- Truth anchor: `D5/S3/Quantum/Foundation/NativeTangentDisjointness.whole_native_tangent_disjointness`
- Dependency: [D5/S3/Quantum/Foundation/CommonPositiveExtension](CommonPositiveExtension.md)
