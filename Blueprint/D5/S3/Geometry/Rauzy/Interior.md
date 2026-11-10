# Interior from separated cylinder geometry

## Abstract

Separated shrinking upper cylinder covers turn positive planar area into interior.

**Definition 1.1 (Actual cylinder data).**

Lean statement: `D5/S3/Geometry/Rauzy/Interior.SeparatedCylinderSystem`

*Formalization.* `D5/S3/Geometry/Rauzy/Interior.SeparatedCylinderSystem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The data records a compact carrier of positive area, its disk bound, contraction, scale separation and actual upper covers. It contains neither a finite translate disk cover nor interior.

**Theorem 1.2 (A synchronized finite family covers a disk).**

Lean statement: `D5/S3/Geometry/Rauzy/Interior.interior_nonempty_of_separated_cylinders`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Rauzy/Interior.interior_nonempty_of_separated_cylinders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

K is a compact subset of the complex plane with positive area, bounded by a closed disk of radius R. At every natural scale n, the actual affine cylinders p + z^n K cover K from above. Their centers are separated by at least c times norm(z)^n, where c is positive and 0 < norm(z) < 1. No reverse cylinder inclusion or open-set condition is assumed.

Choose one density point. The relevant normalized centers lie in a fixed compact disk and are c-separated. A finite c/3-net represents every center, with at most one center per slot; unused slots contain zero. Compactness of the finite product gives one subsequence on which all slots converge simultaneously.

The limiting translates cover the open unit disk. A missing point would have a whole ball missing from the closed finite union. Uniform convergence of all slots preserves a smaller hole in every sufficiently late cluster. The upper cylinder cover then produces an actual K-free ball whose relative area is fixed and positive, contradicting density one. A finite union of closed nowhere-dense translates cannot cover an open disk, so K has nonempty interior.

The argument is an unbounded analytic existence construction. It asserts no numerical inner disk, tiling, connectedness, or original-research novelty.

## References

- Truth anchor: `D5/S3/Geometry/Rauzy/Interior.SeparatedCylinderSystem`
- Truth anchor: `D5/S3/Geometry/Rauzy/Interior.interior_nonempty_of_separated_cylinders`
- Dependency: [D5/S0/Tower/Tribonacci/RauzyFractal](../../../S0/Tower/Tribonacci/RauzyFractal.md)
