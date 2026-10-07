# FiberLift

## Abstract

Faithful GHZ–Mermin measurement dependence: FiberLift

**Definition 1.1 (AlphaFiber).**

$$\forall n \in \mathbb{N},\; \forall P \in ZMod\left(2\right),\; AlphaFiber\left(n, P\right) = \{alpha:(Fin\left(n\right) \to ZMod\left(2\right)) \mid \sum_{i:Fin\left(n\right)} (apply\left(alpha, i\right)) = P\}$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.AlphaFiber` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The parity fiber consists of all output vectors with the prescribed total parity. Under the complementary binary sign encoding, parity_conditioned_moments gives zero expectation for every nonempty proper subset.

**Definition 1.2 (tableOfAlphaGamma).**

$$\forall n \in \mathbb{N},\; \forall alpha \in (Fin\left(n\right) \to ZMod\left(2\right)),\; \forall gamma \in (Fin\left(n\right) \to ZMod\left(2\right)),\; tableOfAlphaGamma\left(alpha, gamma\right) = (i:Fin\left(n\right)) \mapsto ((decide\left(apply\left(alpha, i\right) = 1\right),decide\left(apply\left(alpha, i\right) + apply\left(gamma, i\right) = 1\right)))$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.tableOfAlphaGamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.3 (fiberEquiv).**

$$\forall d \in \mathbb{N},\; \forall P \in ZMod\left(2\right),\; fiberEquiv\left(d, P\right) = Equiv\left((alpha:AlphaFiber\left(d + 1, P\right)) \mapsto ((i:Fin\left(d\right)) \mapsto (apply\left(val\left(alpha\right), castSucc\left(i\right)\right))), (x:(Fin\left(d\right) \to ZMod\left(2\right))) \mapsto (Subtype\left(snoc\left(x, P + \sum_{i:Fin\left(d\right)} (apply\left(x, i\right))\right)\right))\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.fiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

A parity vector is determined by its first d coordinates; the final coordinate is P plus their sum. Both inverse laws are verified.

**Definition 1.4 (fiberMixture).**

$$\forall d \in \mathbb{N},\; \forall C \in Type,\; [Fintype\left(C\right)] \forall P \in (C \to ZMod\left(2\right)),\; \forall p \in (C \to \mathbb{R}),\; \forall z \in Sigma\left((c:C) \mapsto (AlphaFiber\left(d + 1, apply\left(P, c\right)\right))\right),\; fiberMixture\left(P, p, z\right) = \frac{apply\left(p, fst\left(z\right)\right)}{(2)^{d}}$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.fiberMixture` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Uniformly distribute each class weight over its parity fiber.

**Definition 1.5 (liftClassTable).**

$$\forall d \in \mathbb{N},\; \forall C \in Type,\; \forall P \in (C \to ZMod\left(2\right)),\; \forall gamma \in (C \to (Fin\left(d + 1\right) \to ZMod\left(2\right))),\; \forall z \in Sigma\left((c:C) \mapsto (AlphaFiber\left(d + 1, apply\left(P, c\right)\right))\right),\; liftClassTable\left(P, gamma, z\right) = tableOfAlphaGamma\left(val\left(snd\left(z\right)\right), apply\left(gamma, fst\left(z\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.liftClassTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The deterministic table associated with a class and an output parity vector.

**Definition 1.6 (liftedDensity).**

$$\forall d \in \mathbb{N},\; \forall C \in Type,\; [Fintype\left(C\right)] \forall P \in (C \to ZMod\left(2\right)),\; \forall gamma \in (C \to (Fin\left(d + 1\right) \to ZMod\left(2\right))),\; \forall p \in (C \to \mathbb{R}),\; liftedDensity\left(P, gamma, p\right) = channelOutput\left((z:Sigma\left((c:C) \mapsto (AlphaFiber\left(d + 1, apply\left(P, c\right)\right))\right)) \mapsto ((lambda:Strategy\left(d + 1\right)) \mapsto (If\left(liftClassTable\left(P, gamma, z\right) = lambda, 1, 0\right))), fiberMixture\left(P, p\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.liftedDensity` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Push class weights through ClassicalDPI.channelOutput with the deterministic indicator channel. Contributions from classes mapping to the same table are summed.

**Definition 1.7 (classResponse).**

$$\forall d \in \mathbb{N},\; \forall C \in Type,\; \forall P \in (C \to ZMod\left(2\right)),\; \forall gamma \in (C \to (Fin\left(d + 1\right) \to ZMod\left(2\right))),\; \forall x \in Setting\left(d + 1\right),\; \forall c \in C,\; classResponse\left(P, gamma, x, c\right) = bitSign\left(apply\left(P, c\right)\right) \cdot bitSign\left(\sum_{i:Fin\left(d + 1\right)} (apply\left(gamma, c, i\right) \cdot ZModCast\left(toNat\left(apply\left(val\left(x\right), i\right)\right)\right))\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.classResponse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The class full response in parity and relative-output coordinates.

## References

- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.AlphaFiber`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.classResponse`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.fiberEquiv`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.fiberMixture`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.liftClassTable`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.liftedDensity`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift.tableOfAlphaGamma`
- Dependency: [D5/S3/Divergence/ClassicalDPI](../../Divergence/ClassicalDPI.md)
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates](Coordinates.md)
