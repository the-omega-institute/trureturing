# Integral cancellation of matched incidences

## Abstract

Finite integral Morse cancellation from a rank on oriented incidences.

**Theorem 1.1 (The integral chains retract onto their unmatched coordinates).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteMorseCancellation.finite_morse_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteMorseCancellation.finite_morse_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite set of basis labels, each with a natural-number size, and an integer matrix D whose columns are inputs. D squares to zero and each nonzero entry decreases size by one. An involution pairs labels of consecutive sizes, with fixed points denoting unmatched labels. Every matched entry is an integer unit. All fixed points have one common size.

Choose a positive integer N strictly above the rank of every label. The rank decreases along every unmatched nonzero entry of D and every matched edge traversed upward. Put the matched entries in A, set h to its transpose, and write E for D minus A. Each nonzero entry of hE follows both kinds of arrows in succession. Its Nth power vanishes by strict rank decrease.

The finite perturbation lemma corrects the coordinate inclusion and projection using the sums of the first N powers of minus hE and the first N + 1 powers of minus Eh, respectively. The corrected homotopy is the first polynomial times h. The inclusion and projection preserve size and the homotopy raises it by one. The transferred differential lowers size and hence vanishes on the fixed-point coordinates. The composite on those coordinates is the identity. The uncorrected coordinate restriction of each corrected inclusion column gives its original basis element. The other composite differs from the identity by the differential of the homotopy.

Square zero makes D a differential. The unit hypothesis gives an integral inverse for each pair. Strict rank decrease supplies the finite termination bound. A common fixed-point size ensures zero transfer, since a differential could otherwise map between unmatched coordinates of adjacent sizes.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteMorseCancellation.finite_morse_cancellation`
- Dependency: [D5/S3/HomologicalAlgebra/FinitePerturbation](FinitePerturbation.md)
