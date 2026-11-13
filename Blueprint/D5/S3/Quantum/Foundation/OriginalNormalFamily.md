# Original normal support and complete dual edge intervals

## Abstract

Original normal support and complete dual edge intervals

V is an arbitrary finite dimensional real normed space, C a pointed cone, and u its original linear unit. Where stated, C is closed and generating and u is strictly positive on nonzero C. K is the entire normalized base and P its entire extreme locus. All original linear effects between zero and u are retained; the full confirming family F(p) includes u. Pure reciprocity exchanges only two pure endpoints. No mixed reciprocity, matrix specialization, weakPair, unit-width assumption or global uniform-fiber premise is used.

**Theorem 1.1 (Exact whole-cone support threshold).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.rho_positive_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.rho_positive_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In addition to closedness, strict positivity, generation and EB, assume Inj. Fix an original p, an entire chart a, ep in its full zero-confirming fiber, and Coordinates k supplied by the original restriction owner in the singleton branch. Set g=u-ep, D(v)=directionLift(k,v), and normalForm(k,alpha,v)=alpha g+D(v) as an original linear functional on all V. rho(k,v) is the supremum of -D(v)(x)/g(x) over every x in K except p. For every unit v the supremum is bounded, rho>=1, and normalForm is nonnegative on all C exactly when alpha>=rho. No positivity is inferred from an upper bound.

**Theorem 1.2 (Maximum after positivity is established).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.normal_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.normal_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume closedness, strict positivity and generation, with p,a,ep,k as above. For arbitrary real alpha and arbitrary vector v, if normalForm is nonnegative on the entire C, its value on all K is at most alpha+norm(v), and this value is attained at an actual point of the whole D(p). This uses the existing positive-annihilator maximum owner and the original chart formula. The positivity premise is indispensable.

**Theorem 1.3 (Actual neighboring confirmer and antipode).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_neighbor_support`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_neighbor_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under EB and Inj, for every original unit v and original pure q=a(v), the entire full zero-confirming fiber at q is a singleton eq. With lambda=1/(1+rho(k,v)), 0<lambda<=1/2 and eq(x)=(1-lambda)g(x)+lambda D(v)(x) for every x in V. At the actual old antipode a(-v), eq equals (rho-1)/(rho+1), and this antipode belongs to the whole D(q) exactly when rho=1. The exact original neighbor-uniqueness, lift and domination owners are consumed, preserving their proofs.

**Theorem 1.4 (Unique actual linear coordinate map).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_coordinate_map`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_coordinate_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any Coordinates k of the actual original normal restriction, coordinateMap(k) is a linear H from all V to the chart coordinate space. H(p)=0, H(a(z))=z for every coordinate z, and every scalar component inner(v,H(x)) is represented by an element of the actual normal span. Among all original linear maps with those normal-span components and the same whole-chart values, H is unique. The construction uses inverse Riesz representation of the actual inverse-restriction direction lifts. In original_row_saturation, k is obtained from original_coordinates under EB3, Inj and the exact singleton full zero-confirming fiber; Coordinates is not supplied as a desired output of that theorem.

**Theorem 1.5 (Full opposite edge interval).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_whole_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_whole_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under EB and Inj with the same actual normal data, every original proper b with b(p)=0 and b(q)=1 is exactly (1-s)(u-ep)+s eq for some s in [0,1], as an equality of functionals on the entire V. Conversely every such convex combination is proper and has those endpoint readings. A common actual zero point different from p bounds the coefficient by the unique neighboring confirmer coefficient.

**Theorem 1.6 (Complete fixed edge J(p,q)).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_fixed_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_fixed_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same original data, the entire original edge of proper e with e(p)=1 and e(q)=0 is exactly e=(1-s)ep+s(u-eq), s in [0,1], on all V. This is the complement of the full opposite edge, retaining every original effect. original_row_saturation consumes this interface to turn exact fixed-edge attainment into the pure-row minimum.

**Theorem 1.7 (Pure row to a genuinely positive original effect).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalNormalFamily.pure_row_positive_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/OriginalNormalFamily.pure_row_positive_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the original normal data, a proper full confirmer eq at q, a positive lambda, its whole-V normal formula, and the exact pure-row equality T(p,s)=min(ep(s),(u-eq)(s)) for every original pure s. The theorem proves that b=(g+D(v))/2 is proper on all C, b(p)=0, b(q)=1 and b(a(-v))=0; hence the actual old antipode belongs to D(q). The proof first obtains whole-C positivity by perturbing g in the direction of H(s). Direction domination pays positivity, and only then the whole-base maximum normalizes the perturbation into an actual effect. Complementing that effect uses the entire F(p). A negative reading of g+D(v) contradicts the exact pure row. The pure-row premise is a required protected join and is not asserted for an actual collapse by this module.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.normal_maximum`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_coordinate_map`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_fixed_edge`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_neighbor_support`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.original_whole_edge`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.pure_row_positive_bridge`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalNormalFamily.rho_positive_iff`
- Dependency: [D5/S3/Quantum/Foundation/OriginalRegularHeight](OriginalRegularHeight.md)
