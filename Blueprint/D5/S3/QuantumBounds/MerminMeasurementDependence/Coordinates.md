# Coordinates

## Abstract

Faithful GHZ–Mermin measurement dependence: Coordinates

**Theorem 1.1 (bit_cases).**

$$\forall z \in ZMod\left(2\right),\; (z = 0) \lor (z = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.bit_cases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Every element of ZMod 2 is zero or one.

**Theorem 1.2 (bitSign_add).**

$$\forall a \in ZMod\left(2\right),\; \forall b \in ZMod\left(2\right),\; bitSign\left(a + b\right) = bitSign\left(a\right) \cdot bitSign\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.bitSign_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Addition of parity bits multiplies their real signs.

**Theorem 1.3 (bitSign_boolBit).**

$$\forall b \in Bool\left(\right),\; bitSign\left(ZModCast\left(toNat\left(b\right)\right)\right) = boolSign\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.bitSign_boolBit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The natural-number encoding of a Boolean preserves its sign.

**Theorem 1.4 (boolBit_bitBool).**

$$\forall z \in ZMod\left(2\right),\; ZModCast\left(toNat\left(decide\left(z = 1\right)\right)\right) = z$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.boolBit_bitBool` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Deciding whether a parity bit is one and encoding that Boolean recovers the bit.

**Theorem 1.5 (prod_boolSign).**

$$\forall T \in Type,\; \forall x \in (T \to Bool\left(\right)),\; \forall I \in Finset\left(T\right),\; \prod_{i \in I} (boolSign\left(apply\left(x, i\right)\right)) = bitSign\left(\sum_{i \in I} (ZModCast\left(toNat\left(apply\left(x, i\right)\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.prod_boolSign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

A finite product of Boolean signs is the sign of the sum of their parity bits. The index type may be arbitrary.

**Theorem 1.6 (settingWeight_eq_sum).**

$$\forall n \in \mathbb{N},\; \forall x \in (Fin\left(n\right) \to Bool\left(\right)),\; hammingDist\left(x, (i:Fin\left(n\right)) \mapsto (false)\right) = \sum_{i:Fin\left(n\right)} (toNat\left(apply\left(x, i\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.settingWeight_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The Hamming distance from the all-false string counts the true bits.

**Theorem 1.7 (parity_sum).**

$$\forall n \in \mathbb{N},\; \forall x \in (Fin\left(n\right) \to Bool\left(\right)),\; \sum_{i:Fin\left(n\right)} (ZModCast\left(toNat\left(apply\left(x, i\right)\right)\right)) = ZModCast\left(hammingDist\left(x, (i:Fin\left(n\right)) \mapsto (false)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.parity_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The sum of encoded bits is the Hamming weight reduced modulo two.

**Theorem 1.8 (setting_parity).**

$$\forall n \in \mathbb{N},\; \forall x \in Setting\left(n\right),\; \sum_{i:Fin\left(n\right)} (ZModCast\left(toNat\left(apply\left(val\left(x\right), i\right)\right)\right)) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.setting_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

An even-Y setting has zero sum in ZMod 2.

**Theorem 1.9 (settingWeight_snoc).**

$$\forall d \in \mathbb{N},\; \forall x \in (Fin\left(d\right) \to Bool\left(\right)),\; \forall b \in Bool\left(\right),\; hammingDist\left(snoc\left(x, b\right), (i:Fin\left(d + 1\right)) \mapsto (false)\right) = hammingDist\left(x, (i:Fin\left(d\right)) \mapsto (false)\right) + toNat\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.settingWeight_snoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Appending a bit adds its natural-number value to the Hamming weight.

**Theorem 1.10 (weight_not_add_weight).**

$$\forall n \in \mathbb{N},\; \forall x \in (Fin\left(n\right) \to Bool\left(\right)),\; hammingDist\left((i:Fin\left(n\right)) \mapsto (not\left(apply\left(x, i\right)\right)), (i:Fin\left(n\right)) \mapsto (false)\right) + hammingDist\left(x, (i:Fin\left(n\right)) \mapsto (false)\right) = n$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.weight_not_add_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

A Boolean string and its complement have total Hamming weight equal to their length.

**Theorem 1.11 (evenSetting_freeSetting).**

$$\forall d \in \mathbb{N},\; \forall x \in Setting\left(d + 1\right),\; evenSetting\left(freeSetting\left(x\right)\right) = x$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenSetting_freeSetting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Reconstructing the even extension of the free coordinates recovers the setting.

**Theorem 1.12 (freeSetting_evenSetting).**

$$\forall d \in \mathbb{N},\; \forall x \in (Fin\left(d\right) \to ZMod\left(2\right)),\; freeSetting\left(evenSetting\left(x\right)\right) = x$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.freeSetting_evenSetting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Taking the free coordinates of an even extension recovers the parity vector.

**Theorem 1.13 (evenRepresentative_last).**

$$\forall k \in \mathbb{N},\; \forall x \in Setting\left(2 \cdot k + 2\right),\; apply\left(val\left(evenRepresentative\left(k, x\right)\right), last\left(2 \cdot k + 1\right)\right) = false$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenRepresentative_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The chosen representative has final setting bit false.

**Definition 1.14 (bitSign).**

$$\forall z \in ZMod\left(2\right),\; bitSign\left(z\right) = boolSign\left(decide\left(z = 1\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.bitSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.15 (tableParity).**

$$\forall n \in \mathbb{N},\; \forall lambda \in Strategy\left(n\right),\; tableParity\left(lambda\right) = \sum_{i:Fin\left(n\right)} (ZModCast\left(toNat\left(fst\left(apply\left(lambda, i\right)\right)\right)\right))$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.tableParity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.16 (tableGamma).**

$$\forall n \in \mathbb{N},\; \forall lambda \in Strategy\left(n\right),\; \forall i \in Fin\left(n\right),\; tableGamma\left(lambda, i\right) = ZModCast\left(toNat\left(fst\left(apply\left(lambda, i\right)\right)\right)\right) + ZModCast\left(toNat\left(snd\left(apply\left(lambda, i\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.tableGamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.17 (evenExtension).**

$$\forall d \in \mathbb{N},\; \forall x \in (Fin\left(d\right) \to ZMod\left(2\right)),\; evenExtension\left(x\right) = snoc\left((i:Fin\left(d\right)) \mapsto (decide\left(apply\left(x, i\right) = 1\right)), decide\left(\sum_{i:Fin\left(d\right)} (apply\left(x, i\right)) = 1\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.18 (evenSetting).**

$$\forall d \in \mathbb{N},\; \forall x \in (Fin\left(d\right) \to ZMod\left(2\right)),\; evenSetting\left(x\right) = Subtype\left(evenExtension\left(x\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenSetting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The defining underlying string is evenExtension x; its parity proof is supplied in Lean.

**Definition 1.19 (lastAdjustedFrequency).**

$$\forall d \in \mathbb{N},\; \forall lambda \in Strategy\left(d + 1\right),\; \forall i \in Fin\left(d\right),\; lastAdjustedFrequency\left(lambda, i\right) = tableGamma\left(lambda, castSucc\left(i\right)\right) + tableGamma\left(lambda, last\left(d\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.lastAdjustedFrequency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.20 (freeSetting).**

$$\forall d \in \mathbb{N},\; \forall x \in Setting\left(d + 1\right),\; freeSetting\left(x\right) = (i:Fin\left(d\right)) \mapsto (ZModCast\left(toNat\left(apply\left(val\left(x\right), castSucc\left(i\right)\right)\right)\right))$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.freeSetting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.21 (settingEquiv).**

$$\forall d \in \mathbb{N},\; settingEquiv\left(d\right) = Equiv\left(freeSetting, evenSetting\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.settingEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The two maps are freeSetting and evenSetting at dimension d. The Lean definition verifies both inverse laws.

**Definition 1.22 (addX).**

$$\forall d \in \mathbb{N},\; \forall x \in Setting\left(d\right),\; addX\left(x\right) = Subtype\left(snoc\left(val\left(x\right), false\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.addX` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.23 (flipSetting).**

$$\forall n \in \mathbb{N},\; \forall hn \in Even\left(n\right),\; \forall x \in Setting\left(n\right),\; flipSetting\left(hn, x\right) = Subtype\left((i:Fin\left(n\right)) \mapsto (not\left(apply\left(val\left(x\right), i\right)\right))\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.flipSetting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Complement every setting bit. Even n ensures the complement remains an even-Y setting.

**Definition 1.24 (evenRepresentative).**

$$\forall k \in \mathbb{N},\; \forall x \in Setting\left(2 \cdot k + 2\right),\; evenRepresentative\left(k, x\right) = If\left(apply\left(val\left(x\right), last\left(2 \cdot k + 1\right)\right), flipSetting\left(proofOf\left(Even\left(2 \cdot k + 2\right)\right), x\right), x\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenRepresentative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.25 (evenReduced).**

$$\forall k \in \mathbb{N},\; \forall x \in Setting\left(2 \cdot k + 2\right),\; evenReduced\left(k, x\right) = Subtype\left((i:Fin\left(2 \cdot k + 1\right)) \mapsto (apply\left(val\left(evenRepresentative\left(k, x\right)\right), castSucc\left(i\right)\right))\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenReduced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.26 (evenFactor).**

$$\forall k \in \mathbb{N},\; \forall x \in Setting\left(2 \cdot k + 2\right),\; evenFactor\left(k, x\right) = If\left(apply\left(val\left(x\right), last\left(2 \cdot k + 1\right)\right), bitSign\left(ZModCast\left(k + 1\right)\right), 1\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

## References

- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.addX`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.bitSign`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.bitSign_add`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.bitSign_boolBit`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.bit_cases`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.boolBit_bitBool`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenExtension`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenFactor`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenReduced`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenRepresentative`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenRepresentative_last`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenSetting`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.evenSetting_freeSetting`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.flipSetting`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.freeSetting`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.freeSetting_evenSetting`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.lastAdjustedFrequency`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.parity_sum`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.prod_boolSign`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.settingEquiv`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.settingWeight_eq_sum`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.settingWeight_snoc`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.setting_parity`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.tableGamma`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.tableParity`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates.weight_not_add_weight`
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Model](Model.md)
