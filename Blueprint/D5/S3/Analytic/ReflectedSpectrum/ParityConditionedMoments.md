# Parity-Conditioned Product Moments

## Abstract

Uniform laws on the two parity fibers of a binary cube agree on every proper marginal and differ exactly at the full product.

**Definition 1.1 (Binary coordinates as signs).**

$$\forall b: \operatorname{Fin}(2), \operatorname{paritySign}(b) = \operatorname{ite}(b = 0, -1, 1).$$

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.paritySign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The binary value zero represents minus one and the binary value one represents plus one.

**Definition 1.2 (The fiber of a prescribed total sign).**

$$\forall d \in \mathbb{N}, \varepsilon \in \mathbb{Z},\\\operatorname{parityFiber}(d, \varepsilon) = \operatorname{filter}(\operatorname{univ}(\operatorname{Fin}(2)^{\operatorname{Fin}(d)}), x \mapsto \prod_{i \in \operatorname{Fin}(d)} \operatorname{paritySign}(x\left(i\right)) = \varepsilon).$$

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.parityFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fiber consists of all binary strings whose coordinate-sign product equals the specified integer parity.

**Definition 1.3 (The uniform rational law on a parity fiber).**

$$\forall d \in \mathbb{N}, \varepsilon \in \mathbb{Z}, x \in \operatorname{Fin}(2)^{\operatorname{Fin}(d)},\\\operatorname{parityLaw}(d, \varepsilon, x) = \operatorname{ite}(x \in \operatorname{parityFiber}(d, \varepsilon), {2^{d - 1}}^{-1}, 0).$$

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.parityLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point in the selected fiber receives mass 2 to the negative (d minus 1), and every point outside receives zero.

**Definition 1.4 (Mass of a coordinate restriction).**

$$\forall d \in \mathbb{N}, \varepsilon \in \mathbb{Z}, A: \operatorname{Finset}(\operatorname{Fin}(d)), y \in \operatorname{Fin}(2)^{\operatorname{Fin}(d)},\\\operatorname{parityMarginalMass}(d, \varepsilon, A, y) = \sum_{x \in \operatorname{Fin}(2)^{\operatorname{Fin}(d)}} \operatorname{ite}({\forall i \in A, x\left(i\right) = y\left(i\right)}, \operatorname{parityLaw}(d, \varepsilon, x), 0).$$

*Formalization.* `D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.parityMarginalMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This finite sum is the mass of the event that a binary string agrees with y at every coordinate in A.

**Theorem 1.5 (Cardinality and product moments on one parity fiber).**

$$\begin{aligned}\forall k \in \mathbb{N}, \varepsilon \in \mathbb{Z},\\(\varepsilon = -1) \lor (\varepsilon = 1) \Rightarrow\\\operatorname{card}(\operatorname{parityFiber}(k + 1, \varepsilon)) = 2^{k} \land\\(\forall A: \operatorname{Finset}(\operatorname{Fin}(k + 1)), A \neq \emptyset \Rightarrow A \neq univ \Rightarrow\\\sum_{x \in \operatorname{parityFiber}(k + 1, \varepsilon)} \prod_{i \in A} \operatorname{paritySign}(x\left(i\right)) = 0) \land\\\sum_{x \in \operatorname{parityFiber}(k + 1, \varepsilon)} \prod_{i \in \operatorname{Fin}(k + 1)} \operatorname{paritySign}(x\left(i\right)) = \varepsilon \cdot \operatorname{card}(\operatorname{parityFiber}(k + 1, \varepsilon)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.parity_conditioned_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For d = k+1 and parity epsilon equal to minus one or plus one, the fiber has 2^k elements. Every nonempty proper-coordinate product sums to zero, while every full-coordinate product equals epsilon.

The proper-moment cancellation pairs each string with the result of flipping one coordinate in A and one outside A. This is a fixed-point-free involution of the same parity fiber and negates the A-product. A single-coordinate flip bijects the two fibers, giving the cardinality after partitioning the full cube.

**Theorem 1.6 (The two parity laws have identical proper marginals).**

$$\begin{aligned}\forall k \in \mathbb{N},\\((\sum_{x \in \operatorname{Fin}(2)^{\operatorname{Fin}(k + 1)}} \operatorname{parityLaw}(k + 1, -1, x) = 1) \land (\sum_{x \in \operatorname{Fin}(2)^{\operatorname{Fin}(k + 1)}} \operatorname{parityLaw}(k + 1, 1, x) = 1)) \land\\(\forall A: \operatorname{Finset}(\operatorname{Fin}(k + 1)), A \neq \emptyset \Rightarrow A \neq univ \Rightarrow\\(\sum_{x \in \operatorname{Fin}(2)^{\operatorname{Fin}(k + 1)}} \operatorname{parityLaw}(k + 1, -1, x) \cdot \prod_{i \in A} \operatorname{paritySign}(x\left(i\right)) = 0) \land\\(\sum_{x \in \operatorname{Fin}(2)^{\operatorname{Fin}(k + 1)}} \operatorname{parityLaw}(k + 1, 1, x) \cdot \prod_{i \in A} \operatorname{paritySign}(x\left(i\right)) = 0)) \land\\(\sum_{x \in \operatorname{Fin}(2)^{\operatorname{Fin}(k + 1)}} \operatorname{parityLaw}(k + 1, -1, x) \cdot \prod_{i \in \operatorname{Fin}(k + 1)} \operatorname{paritySign}(x\left(i\right)) = -1) \land\\(\sum_{x \in \operatorname{Fin}(2)^{\operatorname{Fin}(k + 1)}} \operatorname{parityLaw}(k + 1, 1, x) \cdot \prod_{i \in \operatorname{Fin}(k + 1)} \operatorname{paritySign}(x\left(i\right)) = 1) \land\\(\forall A: \operatorname{Finset}(\operatorname{Fin}(k + 1)), A \neq univ \Rightarrow \forall y \in \operatorname{Fin}(2)^{\operatorname{Fin}(k + 1)},\\\operatorname{parityMarginalMass}(k + 1, -1, A, y) = \operatorname{parityMarginalMass}(k + 1, 1, A, y)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.parity_conditioned_probability_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both rational laws have total mass one. Every nonempty proper product has expectation zero under both laws, their full-product expectations are respectively minus one and plus one, and every proper marginal, including the empty marginal, is identical.

The mass and moment clauses use the preceding parity-fiber calculation. For marginal equality, flipping one coordinate outside A is a bijection between the two fibers and preserves the restriction event on A.

## References

- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.parityFiber`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.parityLaw`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.parityMarginalMass`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.paritySign`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.parity_conditioned_moments`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.parity_conditioned_probability_form`
