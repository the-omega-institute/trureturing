# OddConstruction

## Abstract

Faithful GHZ–Mermin measurement dependence: OddConstruction

**Theorem 1.1 (odd_construction).**

$$\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\exists rho \in (Setting\left(2 \cdot k + 1\right) \to (Strategy\left(2 \cdot k + 1\right) \to \mathbb{R})),\; (Faithful\left(rho\right)) \land (F\left(rho\right) = floorValue\left(2 \cdot k + 1\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/OddConstruction.odd_construction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Construct mass on the positive rows of the flat-spectrum sign design and lift through parity fibers. The parity_conditioned_moments theorem gives cancellation of every nonempty proper-subset correlator in the lift. Its total variation is bounded by the class-level variation via the frozen data-processing theorem; the universal lower bound gives equality.

**Definition 1.2 (oddGamma).**

$$\forall k \in \mathbb{N},\; \forall a \in (Fin\left(2 \cdot k\right) \to ZMod\left(2\right)),\; oddGamma\left(k, a\right) = snoc\left(a, 0\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/OddConstruction.oddGamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.3 (oddRow).**

$$\forall k \in \mathbb{N},\; \forall x \in Setting\left(2 \cdot k + 1\right),\; \forall a \in (Fin\left(2 \cdot k\right) \to ZMod\left(2\right)),\; oddRow\left(k, x, a\right) = spectralRow\left(k, freeSetting\left(x\right), a\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/OddConstruction.oddRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

## References

- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/OddConstruction.oddGamma`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/OddConstruction.oddRow`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/OddConstruction.odd_construction`
- Dependency: [D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments](../../Analytic/ReflectedSpectrum/ParityConditionedMoments.md)
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/FiberLift](FiberLift.md)
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/SignDesign](SignDesign.md)
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/SpectralLowerBound](SpectralLowerBound.md)
- Dependency: [D5/S3/TotalVariation/DataProcessing](../../TotalVariation/DataProcessing.md)
