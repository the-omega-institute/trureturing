# Circular polygon endpoint chains

## Abstract

Marked endpoints in the actual circular polygon quotient: saturation and complete chain reflection.

**Definition 1.1 (Occurrence-sensitive endpoint instructions).**

$$\forall Face \in Type,\; \forall count \in Functions\left(Face, Nat\right),\; \forall I \in Set\left(Identification\left(Face, count\right)\right),\; \forall s \in Side\left(Face, count\right),\; \forall t \in Side\left(Face, count\right),\; (EndpointStep\left(I, s, t\right)) \iff (\exists a \in Identification\left(Face, count\right),\; \exists b \in Bool,\; (Member\left(a, I\right)) \land ((s = endSide\left(source\left(a\right), b\right)) \land (t = endSide\left(target\left(a\right), endDirection\left(direction\left(a\right), b\right)\right))))$$

*Formalization.* `D5/S3/Geometry/Gluing/PolygonMarkedEndpointChains.EndpointStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An endpoint occurrence is the initial endpoint of one labelled side. The terminal endpoint is the initial endpoint of its cyclic successor. Each supplied gluing instruction contributes its two endpoint identifications: the same parameter direction preserves the endpoint bit, and the opposite direction complements it. No quotient-vertex labels, distinct geometric vertices, regular action or manifold assumptions enter this definition.

**Theorem 1.2 (All intermediate point representatives remain marked endpoints).**

$$\forall Face \in Type,\; \forall count \in Functions\left(Face, Nat\right),\; \forall I \in Set\left(Identification\left(Face, count\right)\right),\; (\forall x \in PreRealization\left(Face, count\right),\; \forall y \in PreRealization\left(Face, count\right),\; (PolygonRelation\left(I, x, y\right)) \implies ((\exists s \in Side\left(Face, count\right),\; x = point\left(s, 0\right)) \iff (\exists s \in Side\left(Face, count\right),\; y = point\left(s, 0\right)))) \land (\forall s \in Side\left(Face, count\right),\; \forall t \in Side\left(Face, count\right),\; (PolygonRelation\left(I, point\left(s, 0\right), point\left(t, 0\right)\right)) \iff (EqvGen\left(EndpointStep\left(I\right), s, t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/PolygonMarkedEndpointChains.polygon_marked_endpoint_chains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every type of faces, every natural side-count function and every set of the actual PolygonGluing.Identification instructions, the marked locus is saturated under the full generated point relation. For every two marked vertices, the full polygon point relation holds exactly when the explicit EndpointStep instructions generate a chain between their side occurrences. Face types and instruction sets may be infinite. A face with zero sides contributes no marked endpoint; monogons, digons, loops, repeated incidences, unpaired sides and multiple instructions remain in scope.

The geometric input uses the original PolygonCell closed complex disk and its circular side parametrization. Circle.exp_eq_exp forces a side point equal to a marked vertex to have endpoint parameter zero or one. Circle.exp_injOn_Ico supplies uniqueness of the initial marked endpoint index. These facts lift each generator, and saturation supplies the intermediate marked representative at every transitive step. The reverse chain direction uses the actual two endpoint instances of each polygon generator.

The cell, side, instruction and generated-relation definitions are a minimal source selection from mccorvie/classification-of-surfaces at e3c7230fe78d7b056a415d9ecae6f77887046b32, PolygonalQuotient.lean, under Apache-2.0. Their original namespaces and definitions are preserved. Copied convenience theorems are omitted, and the consumed boundary calibration proof is reused at its source. This adaptation does not install or upgrade the donor project.

This is an independent endpoint core. It does not construct the original nu-restricted finite cyclic presentation, its list-word validity or connectivity certificate, the calibrated original Point pre-space homeomorphism, or either full-point generator correspondence. Those remain the required full-point and presentation interfaces for the chosen normalization result; the marked endpoint relation can be compared separately to the original return-cycle quotient. No Euler characteristic, genus, closed-manifold, orientation or full CFMP completion follows from this theorem alone.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/PolygonMarkedEndpointChains.EndpointStep`
- Truth anchor: `D5/S3/Geometry/Gluing/PolygonMarkedEndpointChains.polygon_marked_endpoint_chains`
