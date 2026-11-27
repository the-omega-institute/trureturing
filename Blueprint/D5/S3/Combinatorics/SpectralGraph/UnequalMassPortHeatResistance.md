# One-port heat on unequal-mass triangles

## Abstract

Positive triangles of known unequal masses have equal full port heat and distinct hidden responses.

The triangle construction and resistance comparison are from Sections 4 and 8 of Positive complete networks with the same port heat. Its labels 1, 2 and 3 correspond to 0, 1 and 2 here.

**Definition 1.1 (Matrix space).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.Mat`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.Mat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Real matrices on the three vertex labels 0, 1 and 2.

**Definition 1.2 (Conductance space).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.Weights`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.Weights` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real value on each unordered vertex pair.

**Definition 1.3 (Complete triangle).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.triangle`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.triangle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete graph on 0, 1 and 2, with port 0 and hidden vertices 1 and 2.

**Definition 1.4 (Mass square roots).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.rootMass`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.rootMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vector z = (1, 1, 2) gives the positive square roots of the masses (1, 1, 4).

**Definition 1.5 (Inverse square root of mass).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.inverseRootMass`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.inverseRootMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal matrix J has entries 1, 1 and 1/2.

**Definition 1.6 (Physical stiffness).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.stiffness`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.stiffness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix K(w) has the sum of incident conductances on the diagonal and the negative conductance off the diagonal.

**Definition 1.7 (Mass-normalized stiffness).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.normalized`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.normalized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix L(w) = JK(w)J governs the heat flow in mass-normalized coordinates.

**Definition 1.8 (Physical impulse response).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.physicalHeat`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.physicalHeat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For time t ≥ 0, the entry H(w,t,i,j) of J exp(−tL(w)) J gives the temperature at i per unit impulse at j. The matrix exponential extends the formula to all real t. The function cross(w) is this response from input 0 to output 1.

**Definition 1.9 (Positive conductances).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.PositiveWeights`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.PositiveWeights` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every edge of the complete triangle has strictly positive conductance.

**Definition 1.10 (Two positive conductance assignments).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.conductances`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.conductances` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In edge order 01, 02, 12, the vector w(true) is (4/15, 17/30, 91/150) and w(false) is (1/15, 23/30, 109/150).

**Definition 1.11 (Reflection).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.reflection`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.reflection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q has rows (1, 0, 0), (0, −3/5, 4/5), and (0, 4/5, 3/5).

**Definition 1.12 (Grounded unit-current potential).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.groundedPotential`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.groundedPotential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The voltage g(true) is (352/197, 0, 170/197) and g(false) is (448/197, 0, 230/197). Both use vertex 1 as the ground.

**Definition 1.13 (Identification from the port curve).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.claim`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every pair of positive conductance assignments on the triangle with the prescribed masses, equality of their port curves for all real times would force equality of their hidden curves for all real times or equality of their resistances from 0 to 1.

**Theorem 1.14 (Exact certificate for the two triangles).**

$$\forall b \in \operatorname{Bool},\; \operatorname{R}\left(\operatorname{w}\left(b\right), 0, 1\right) = \operatorname{r}\left(b\right) \land \left(\operatorname{PositiveWeights}\left(\operatorname{w}\left(b\right)\right) \land \left(Q^{T} = Q \land \left(Q \cdot Q = \operatorname{I} \land \left(Q \cdot z = z \land \left(Q \cdot \operatorname{e}\left(0\right) = \operatorname{e}\left(0\right) \land \left(\operatorname{L}\left(\operatorname{w}\left(\operatorname{false}\right)\right) = Q \cdot \operatorname{L}\left(\operatorname{w}\left(\operatorname{true}\right)\right) \cdot Q^{T} \land \left(\left(\forall t \in \operatorname{Real},\; \operatorname{H}\left(\operatorname{w}\left(\operatorname{true}\right), t, 0, 0\right) = \operatorname{H}\left(\operatorname{w}\left(\operatorname{false}\right), t, 0, 0\right)\right) \land \left(\operatorname{HasDerivAt}\left(\operatorname{cross}\left(\operatorname{w}\left(b\right)\right), \operatorname{s}\left(b\right), 0\right) \land \left(\forall v \in \operatorname{Voltage},\; \left(\operatorname{K}\left(\operatorname{w}\left(b\right)\right) \cdot v = (1,-1,0) \land \operatorname{v}\left(1\right) = 0\right) \Leftrightarrow v = \operatorname{g}\left(b\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.triangle_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Florian Dörfler; Francesco Bullo (2013). *Kron Reduction of Graphs With Applications to Electrical Networks*. DOI: [10.1109/TCSI.2012.2215780](https://doi.org/10.1109/TCSI.2012.2215780). URL: <https://arxiv.org/abs/1102.2950>.

*Commentary.*

The symmetric involution Q fixes the port vector and the mass square roots. Conjugation by Q takes the plus normalized stiffness to the minus one. Matrix exponentiation respects this conjugation at every real time, so the physical port entries coincide.

The initial derivatives s(true) = 4/15 and s(false) = 1/15 follow from the derivative of the matrix exponential at zero. For every voltage vector v, the unit-current equations with vertex 1 grounded hold exactly when v is the displayed g(b). The native effective resistance R is the reciprocal of the current at 0 for the unique unit-voltage harmonic extension. Direct solution gives r(true) = 352/197 and r(false) = 448/197, the same voltage drops as in the unit-current solutions.

**Theorem 1.15 (Refutation of hidden-response identification).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Florian Dörfler; Francesco Bullo (2013). *Kron Reduction of Graphs With Applications to Electrical Networks*. DOI: [10.1109/TCSI.2012.2215780](https://doi.org/10.1109/TCSI.2012.2215780). URL: <https://arxiv.org/abs/1102.2950>.

*Commentary.*

The common port curve belongs to both actual networks. Their right derivatives at zero from 0 to 1 differ by 1/5, so their hidden curves differ at positive times. Their effective resistances from 0 to 1 differ by −96/197 in plus-minus order.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.Mat`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.PositiveWeights`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.Weights`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.conductances`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.groundedPotential`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.inverseRootMass`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.normalized`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.physicalHeat`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.reflection`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.rootMass`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.stiffness`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.triangle`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalMassPortHeatResistance.triangle_certificate`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation](FiedlerResistanceInvariantWeightsRefutation.md)
