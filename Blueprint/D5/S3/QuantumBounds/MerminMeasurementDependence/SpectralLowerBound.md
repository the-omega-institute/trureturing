# SpectralLowerBound

## Abstract

Faithful GHZ–Mermin measurement dependence: SpectralLowerBound

**Definition 1.1 (spectralRow).**

$$\forall k \in \mathbb{N},\; \forall x \in (Fin\left(2 \cdot k\right) \to ZMod\left(2\right)),\; \forall a \in (Fin\left(2 \cdot k\right) \to ZMod\left(2\right)),\; spectralRow\left(k, x, a\right) = bitSign\left(qFree\left(x\right)\right) \cdot bitSign\left(walshParity\left(k, a\right)\right) \cdot character\left(a, x\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/SpectralLowerBound.spectralRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.2 (capValue).**

$$\forall k \in \mathbb{N},\; capValue\left(k\right) = NatDiv\left((2)^{2 \cdot k} + (2)^{k}, 2\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/SpectralLowerBound.capValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Theorem 1.3 (staircase_lower).**

$$\forall n \in \mathbb{N},\; (3 \le n) \Rightarrow (\forall rho \in (Setting\left(n\right) \to (Strategy\left(n\right) \to \mathbb{R})),\; (Faithful\left(rho\right)) \Rightarrow (floorValue\left(n\right) \le F\left(rho\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/SpectralLowerBound.staircase_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

For odd n use all even settings. For even n embed the odd-size subset by appending X. Affine agreement bounds its satisfaction cap, and the finite overlap estimate forces a distant pair of densities.

## References

- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/SpectralLowerBound.capValue`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/SpectralLowerBound.spectralRow`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/SpectralLowerBound.staircase_lower`
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/OverlapBound](OverlapBound.md)
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh](Walsh.md)
