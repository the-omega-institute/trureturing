# Finite A5 twelve-coset certificate

## Abstract

A finite twelve-point permutation certificate computes the A5 boundary counts.

This document records the concrete twelve-point input from the A5 noncommutative transport example. The two permutations are given both by their image tables and by disjoint cycle products. The return permutations use the displayed right-action convention through low squared times high inverse and low times high squared.

The kernel computation certifies only this finite data: the two return cycle types, the four endpoint orbit counts, and the resulting (V,E,F)=(20,72,48), Euler characteristic -4, and genus 3. It does not formalize the general noncommutative face-transport theorem, A5 generation, or a geometric realization of every group action.

**Theorem 1.1 (Finite A5 cycle and link certificate).**

$$\left(\left(\forall i \in Fin\left(12\right),\; lowGenerator\left(i\right) = lowImageTable\left(i\right)\right) \land \left(\forall i \in Fin\left(12\right),\; highGenerator\left(i\right) = highImageTable\left(i\right)\right)\right) \land \left(\left(cycleType\left(lowGenerator\right) = \{3, 3, 3, 3\} \land \left(cycleType\left(highGenerator\right) = \{5, 5\} \land \left(cycleType\left(lowReturn\left(\right)\right) = \{2, 2, 2, 2, 2, 2\} \land cycleType\left(highReturn\left(\right)\right) = \{3, 3, 3, 3\}\right)\right)\right) \land \left(vertexCount\left(\right) = 20 \land \left(edgeCount\left(\right) = 72 \land \left(faceCount\left(\right) = 48 \land \left(eulerCharacteristic\left(\right) = - 4 \land boundaryGenus\left(\right) = 3\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/A5TwelveCosetFiniteCertificate.a5_finite_cycle_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit Fin(12) table is checked pointwise by the kernel. The cycleType equalities are a bounded permutation computation, and the count definitions then evaluate to the stated link data.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/A5TwelveCosetFiniteCertificate.a5_finite_cycle_certificate`
