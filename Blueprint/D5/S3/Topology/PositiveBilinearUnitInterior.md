# Interior outputs of the same two-call readback

## Abstract

Whole-cone positivity and real spanning make the two actual repeated-readback unit outputs interior, before imposing either orthogonality relation.

The carriers X,Y,Z are arbitrary real normed spaces with their original closed salient cones and specified interior order units, encoded by OrderUnitNorm.Data. Only the target of each interior claim must be finite dimensional. The cones are the whole original cones. No assertion that products positively generate a joint cone, no Jordan classification and no zero-comparison relation is assumed.

**Definition 1.1 (Real spanning of all bilinear values).**

Lean statement: `D5/S3/Topology/PositiveBilinearUnitInterior.Spans`

*Formalization.* `D5/S3/Topology/PositiveBilinearUnitInterior.Spans` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Spans(f) says that the real linear span of all f(x,y), with arbitrary real x,y, is the whole target. This does not replace the full target positive cone by product-positive inputs.

**Theorem 1.2 (A positive spanning bilinear map has interior unit output).**

Lean statement: `D5/S3/Topology/PositiveBilinearUnitInterior.unit_image_interior`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/PositiveBilinearUnitInterior.unit_image_interior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every bilinear map f between the displayed original cone spaces, whole-cone positivity and Spans(f) imply that f(unit_X,unit_Y) is interior in the target cone. If it were on the boundary, the existing boundary_support theorem would give a positive target functional beta vanishing there with strictly positive target-unit mass. Apply the existing positive_bound first to beta composed with f(-,unit_Y), then to beta composed with f(x,-) for positive x, and finally to beta composed with f(-,y) for arbitrary y. The functional vanishes on every bilinear value. Real spanning then makes it vanish on the target unit, contradicting its strictly positive mass.

**Definition 1.3 (The literal original repeated call).**

Lean statement: `D5/S3/Topology/PositiveBilinearUnitInterior.twiceReadback`

*Formalization.* `D5/S3/Topology/PositiveBilinearUnitInterior.twiceReadback` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the original bilinear L:Y times X to Z, original linear p:Z to Y and reference omega in Y, twiceReadback(L,p,omega)(a,b)=p(L(p(L(omega,a)),b)). This is a bilinear map derived from the same L,p,omega. It is not an independently supplied second readback or independent M.

**Theorem 1.4 (Both actual unit outputs are interior before DJ and DH).**

Lean statement: `D5/S3/Topology/PositiveBilinearUnitInterior.original_two_call_units_interior`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/PositiveBilinearUnitInterior.original_two_call_units_interior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A,D,E be the displayed original cone spaces, with D,E finite dimensional. For every original L,p,omega, assume omega positive, L and p positive on their whole cones, and the original real spanning equalities for twiceReadback(L,p,omega) and L. Then U=twiceReadback(L,p,omega)(unit_A,unit_A) and G=L(unit_D,unit_A) are interior in the original D and E cones. Positivity of M is derived through the literal two successive uses of p; the general bilinear theorem is then applied once to M and once to L. DJ, DH, C13, CP, a trace-preservation condition, a normalization inverse and any conclusion of Chapter 65 are absent from the hypotheses.

Source scope. This establishes the cone-geometric interior step of Quantum Origin V Proposition 74.4 once its original carriers and units have been faithfully represented by Data. It neither proves the complete S-to-EJA/JB entrance nor defines the actual support inverse square root. The finite-frame support and weight-commutator argument, the Chapter 65.3 first interface, the product-frame spanning consumer, full Theorem 74.7 and the same-original-rho Theorem 74.9 remain unproved. No atom coverage or frozen membership is asserted.

## References

- Truth anchor: `D5/S3/Topology/PositiveBilinearUnitInterior.Spans`
- Truth anchor: `D5/S3/Topology/PositiveBilinearUnitInterior.original_two_call_units_interior`
- Truth anchor: `D5/S3/Topology/PositiveBilinearUnitInterior.twiceReadback`
- Truth anchor: `D5/S3/Topology/PositiveBilinearUnitInterior.unit_image_interior`
- Dependency: [D5/S3/Topology/OrderUnitNorm](OrderUnitNorm.md)
