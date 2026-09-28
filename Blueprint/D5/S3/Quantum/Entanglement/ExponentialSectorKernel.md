# The Ordered Exponential Kernel

## Abstract

An ordered exponential kernel has explicit nonnegative equilibrium weights and an attained simplex minimum, including coincident sites.

Let loss be a nondecreasing real sequence and take its first n+1 sites. The kernel between sites i and j is exp(-abs(loss(i)-loss(j))/2). Its adjacent coefficients are exp(-(loss(i+1)-loss(i))/2). The quadratic energy is the sum over all ordered site pairs of p(i) p(j) times their kernel entry. A simplex weight is nonnegative at every site and has total mass one.

**Definition 1.1 (Kernel).**

Lean statement: `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.kernel`

*Formalization.* `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kernel is the exponential of minus half the absolute separation of the real sites.

**Definition 1.2 (Adjacent coefficient).**

Lean statement: `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.edge`

*Formalization.* `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An adjacent coefficient lies in (0,1] for nondecreasing sites; equality to one allows repeated sites.

**Definition 1.3 (Quadratic energy).**

Lean statement: `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.energy`

*Formalization.* `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite quadratic form is defined for arbitrary signed real weights, as well as simplex weights.

**Definition 1.4 (Equilibrium weights).**

Lean statement: `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.equilibriumWeight`

*Formalization.* `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.equilibriumWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The singleton weight is one. On adjoining a site with adjacent coefficient a, subtract a/(1+a) from the former last weight, retain the other old weights, and give the new endpoint weight 1/(1+a).

**Definition 1.5 (Normalizing mass).**

Lean statement: `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.normalizer`

*Formalization.* `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.normalizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalizer Z is one plus the sum of (1-a)/(1+a) over the n adjacent coefficients.

**Theorem 1.6 (Equilibrium, minimum and range bounds).**

Lean statement: `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic form is nonnegative on every signed weight vector. The equilibrium weights v are nonnegative, satisfy Kv=1, and sum to the positive normalizer Z. Thus p*=v/Z is a simplex weight, its energy is 1/Z, and every simplex weight has energy at least 1/Z. Strictly increasing sites give strictly positive equilibrium weights.

Write T for the sum of tanh((loss(i+1)-loss(i))/4) over adjacent sites. Then Z=1+T. With R=loss(n)-loss(0), the quantity 2(1-1/Z) lies between 1-exp(-R/2) and 2R/(4+R). For every real epsilon<2, the inequality 2(1-1/Z)<=epsilon is equivalent to T<=epsilon/(2-epsilon).

Adjoining the last site completes a square: the enlarged energy is the old energy at a corrected endpoint weight plus (1-a*a) times the square of the new weight. The equilibrium recursion proves the row equations. Subtracting p* from a competitor makes the mixed energy term vanish, leaving a nonnegative quadratic form. No inverse kernel is needed, so repeated sites are included. For n=0, Z=1 and the minimum energy is one.

This statement concerns the finite kernel and its simplex energy. A channel distance requires an additional identification of the physical channel with this kernel.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.edge`
- Truth anchor: `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.energy`
- Truth anchor: `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.equilibriumWeight`
- Truth anchor: `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.kernel`
- Truth anchor: `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.normalizer`
- Truth anchor: `D5/S3/Quantum/Entanglement/ExponentialSectorKernel.result`
- Dependency: [D5/S3/Observer/Fluctuation/ThermalCoefficientFloor](../../Observer/Fluctuation/ThermalCoefficientFloor.md)
