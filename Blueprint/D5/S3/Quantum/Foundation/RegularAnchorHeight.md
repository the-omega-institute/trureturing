# Original regular anchors and uniform separation height

## Abstract

Continuity of the entire original zero-effect fiber controls arbitrary full confirming effects and gives a common positive height for labels with a fixed positive exclusion readout.

V is any finite dimensional real normed space, C its closed generating pointed cone, and u an original linear functional strictly positive on every nonzero cone vector. K is the entire base C intersect {u=1}, P is its entire extreme-point set, and E consists of all original real-linear effects between zero and u on C. Every full exclusion D(p) has an injective affine chart by a closed Euclidean ball of positive dimension, with dimensions allowed to vary. Equality of full exclusions implies equality of their original pure labels. In particular the statements apply to the original EB3 and Inj hypotheses; no inner product on V, closed P, pair-face premise or joint measurement is assumed.

**Definition 1.1 (zeroReadouts).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorHeight.zeroReadouts`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorHeight.zeroReadouts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C,u and p in the entire original P, zeroReadouts(C,u,p) is the image under FixedZeroObstruction.stateReadout of the entire zeroEffects(C,u,p). Its elements are continuous functions on all of K, with value f(x) at every original normalized state x. It includes the zero effect. The continuous-map supremum metric is exactly the original full-state effect metric.

**Definition 1.2 (ZeroContinuousAt).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorHeight.ZeroContinuousAt`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorHeight.ZeroContinuousAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every closed C, strictly positive u and original p in P, ZeroContinuousAt(hc,hs,p) means that for every sequence pn in the entire P tending to p in V, hausdorffDist(zeroReadouts(C,u,pn(n)),zeroReadouts(C,u,p)) tends to zero. The compact-space instance on K is supplied by base_compact(hc,hs). Both full zero-effect sets are nonempty and bounded, so this real Hausdorff distance is finite. This is the original Cont(B) condition; the pure sequences are not restricted to a selected ball or residual subset.

**Definition 1.3 (RegularAnchor).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorHeight.RegularAnchor`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorHeight.RegularAnchor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every closed C, strictly positive u and original p in P, RegularAnchor(hc,hs,p) is the conjunction of ZeroContinuousAt(hc,hs,p) and existence of one original linear ep such that, for every original linear e, membership e in fullZeroConfirmers(C,u,p) is equivalent to e=ep. Thus the domain is exactly P0 intersect Cont(B), with the full original confirming fiber.

**Theorem 1.4 (Every full confirmer converges at a regular anchor).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorHeight.regular_confirmation_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorHeight.regular_confirmation_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V,C,u with the hypotheses above, every original pure p, and every original linear ep, assume that for every original linear e, e belongs to fullZeroConfirmers(C,u,p) if and only if e=ep, and assume ZeroContinuousAt(hc,hs,p). For every sequence pn of original pure points tending to p in V and every sequence en of original linear effects with en(n) in fullZeroConfirmers(C,u,pn(n)) at every index, the corresponding continuous linear maps en(n) tend to ep in the operator norm on the full original dual. The en sequence is arbitrary; no continuous selector or uniqueness at pn(n) is required.

Fix an original pure s in D(p) and one full zero confirmer h of s. Original zero symmetry makes h a zero effect at p. Hausdorff approximation of the whole zero-effect fibers supplies b(n) zero at pn(n) converging to h uniformly on K. The existing zero_effect_maximizer supplies original pure global maximizers s(n) of b(n), lying in the entire D(pn(n)). Their h readings tend to one. Compactness of K and the exact singleton one-face full_zero_faces force s(n) to tend to s. All mixed limit states are treated in K before this singleton identity identifies the limit.

Compactness of the full effect interval supplies an arbitrary convergent subsequence of en. Moving evaluation shows its limit confirms p and vanishes at every original pure s in D(p), using the same-index approximants above. The original chart_boundary and the convex hull of the entire sphere extend vanishing to all mixed states in D(p). Unique full confirmation identifies the limit as ep. The subsequence criterion then yields convergence of the entire arbitrary en sequence.

**Theorem 1.5 (Uniform original height from a fixed positive exclusion reading).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorHeight.regular_anchor_uniform_height`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorHeight.regular_anchor_uniform_height` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every V,C,u with the same closedness, strict positivity, generation, whole-ball and injective-label hypotheses, every p in the entire original P, every original linear ep in fullZeroConfirmers(C,u,p), and every RegularAnchor(hc,hs,p), the following holds for every real epsilon>0. There exists one real sigma>0 such that for every original pure a and every original linear ea in fullZeroConfirmers(C,u,a), if there exists z in the entire D(p) with epsilon<=ea(z), then sigma<=(u-ep)(a). The same sigma applies to all a,ea and all possible moving z. No sigma or uniform reverse comparison gap is assumed.

If the conclusion fails, choose heights below 1/(n+1). Nonnegativity gives height convergence to zero. Every cluster point in compact K lies in the zero face of u-ep, equivalently the original one-face of ep, which is exactly {p}. Hence the entire pure sequence converges to p. The preceding arbitrary-confirmer theorem forces ea(n) to ep in the full dual. A bound R on the norm of every original state gives epsilon<=norm(ea(n)-ep)R at the moving z(n) in D(p), contradicting convergence to zero.

For the source endpoint family at a fixed regular anchor, the remaining application requires the actual pure endpoints a(v), their actual full confirming effects, and the original evaluation e(a(v))(q(-v))=2 gamma(v)>=2/(1+R(p))>0 on D(p), uniformly for every unit v. Once those original identities and the finite bound R(p) are supplied, the same epsilon and the theorem give one sigma for all directions. This statement does not establish those identities, the endpoint maximum characterization, support or cost regularity, a boundary homeomorphism, the five equivalent boundary continuity conditions, or a uniform lower bound on 1-d(v). No regular-anchor occurrence in a concrete model is asserted here. These are deductions in the original convex model, without a physical realization or literature priority claim.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorHeight.RegularAnchor`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorHeight.ZeroContinuousAt`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorHeight.regular_anchor_uniform_height`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorHeight.regular_confirmation_tendsto`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorHeight.zeroReadouts`
- Dependency: [D5/S3/Quantum/Foundation/FixedZeroObstruction](FixedZeroObstruction.md)
