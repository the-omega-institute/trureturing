# Coordinates

## Abstract

Faithful GHZ–Mermin measurement dependence: Coordinates

**Definition 1.1 (bitSign).**

$$\forall z \in ZMod\left(2\right),\; bitSign\left(z\right) = boolSign\left(decide\left(z = 1\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.bitSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.2 (tableParity).**

$$\forall n \in \mathbb{N},\; \forall lambda \in Strategy\left(n\right),\; tableParity\left(lambda\right) = \sum_{i:Fin\left(n\right)} (ZModCast\left(toNat\left(fst\left(apply\left(lambda, i\right)\right)\right)\right))$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.tableParity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.3 (tableGamma).**

$$\forall n \in \mathbb{N},\; \forall lambda \in Strategy\left(n\right),\; \forall i \in Fin\left(n\right),\; tableGamma\left(lambda, i\right) = ZModCast\left(toNat\left(fst\left(apply\left(lambda, i\right)\right)\right)\right) + ZModCast\left(toNat\left(snd\left(apply\left(lambda, i\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.tableGamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.4 (evenExtension).**

$$\forall d \in \mathbb{N},\; \forall x \in (Fin\left(d\right) \to ZMod\left(2\right)),\; evenExtension\left(x\right) = snoc\left((i:Fin\left(d\right)) \mapsto (decide\left(apply\left(x, i\right) = 1\right)), decide\left(\sum_{i:Fin\left(d\right)} (apply\left(x, i\right)) = 1\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.5 (evenSetting).**

$$\forall d \in \mathbb{N},\; \forall x \in (Fin\left(d\right) \to ZMod\left(2\right)),\; evenSetting\left(x\right) = Subtype\left(evenExtension\left(x\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenSetting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The defining underlying string is evenExtension x; its parity proof is supplied in Lean.

**Definition 1.6 (lastAdjustedFrequency).**

$$\forall d \in \mathbb{N},\; \forall lambda \in Strategy\left(d + 1\right),\; \forall i \in Fin\left(d\right),\; lastAdjustedFrequency\left(lambda, i\right) = tableGamma\left(lambda, castSucc\left(i\right)\right) + tableGamma\left(lambda, last\left(d\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.lastAdjustedFrequency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.7 (freeSetting).**

$$\forall d \in \mathbb{N},\; \forall x \in Setting\left(d + 1\right),\; freeSetting\left(x\right) = (i:Fin\left(d\right)) \mapsto (ZModCast\left(toNat\left(apply\left(val\left(x\right), castSucc\left(i\right)\right)\right)\right))$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.freeSetting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.8 (settingEquiv).**

$$\forall d \in \mathbb{N},\; settingEquiv\left(d\right) = Equiv\left(freeSetting, evenSetting\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.settingEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The two maps are freeSetting and evenSetting at dimension d. The Lean definition verifies both inverse laws.

**Definition 1.9 (addX).**

$$\forall d \in \mathbb{N},\; \forall x \in Setting\left(d\right),\; addX\left(x\right) = Subtype\left(snoc\left(val\left(x\right), false\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.addX` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.10 (flipSetting).**

$$\forall n \in \mathbb{N},\; \forall hn \in Even\left(n\right),\; \forall x \in Setting\left(n\right),\; flipSetting\left(hn, x\right) = Subtype\left((i:Fin\left(n\right)) \mapsto (not\left(apply\left(val\left(x\right), i\right)\right))\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.flipSetting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Complement every setting bit. Even n ensures the complement remains an even-Y setting.

**Definition 1.11 (evenRepresentative).**

$$\forall k \in \mathbb{N},\; \forall x \in Setting\left(2 \cdot k + 2\right),\; evenRepresentative\left(k, x\right) = If\left(apply\left(val\left(x\right), last\left(2 \cdot k + 1\right)\right), flipSetting\left(proofOf\left(Even\left(2 \cdot k + 2\right)\right), x\right), x\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenRepresentative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.12 (evenReduced).**

$$\forall k \in \mathbb{N},\; \forall x \in Setting\left(2 \cdot k + 2\right),\; evenReduced\left(k, x\right) = Subtype\left((i:Fin\left(2 \cdot k + 1\right)) \mapsto (apply\left(val\left(evenRepresentative\left(k, x\right)\right), castSucc\left(i\right)\right))\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenReduced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.13 (evenFactor).**

$$\forall k \in \mathbb{N},\; \forall x \in Setting\left(2 \cdot k + 2\right),\; evenFactor\left(k, x\right) = If\left(apply\left(val\left(x\right), last\left(2 \cdot k + 1\right)\right), bitSign\left(ZModCast\left(k + 1\right)\right), 1\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

## References

- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.addX`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.bitSign`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenExtension`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenFactor`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenReduced`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenRepresentative`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenSetting`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.flipSetting`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.freeSetting`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.lastAdjustedFrequency`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.settingEquiv`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.tableGamma`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.tableParity`
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Model](Model.md)
