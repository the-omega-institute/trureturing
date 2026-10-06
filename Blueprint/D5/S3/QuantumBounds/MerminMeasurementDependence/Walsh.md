# Walsh

## Abstract

Faithful GHZ–Mermin measurement dependence: Walsh

**Definition 1.1 (qFree).**

$$\forall d \in \mathbb{N},\; \forall x \in (Fin\left(d\right) \to ZMod\left(2\right)),\; qFree\left(x\right) = ZModCast\left(choose\left(hammingDist\left((i:Fin\left(d\right)) \mapsto (decide\left(apply\left(x, i\right) = 1\right)), const\left(Fin\left(d\right), false\right)\right), 2\right)\right) + \sum_{i:Fin\left(d\right)} (apply\left(x, i\right))$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.qFree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.2 (walsh).**

$$\forall d \in \mathbb{N},\; \forall a \in (Fin\left(d\right) \to ZMod\left(2\right)),\; walsh\left(a\right) = \sum_{x:(Fin\left(d\right) \to ZMod\left(2\right))} (bitSign\left(qFree\left(x\right) + \sum_{i:Fin\left(d\right)} (apply\left(a, i\right) \cdot apply\left(x, i\right))\right))$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.walsh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Theorem 1.3 (qFree_polar).**

$$\forall d \in \mathbb{N},\; \forall x \in (Fin\left(d\right) \to ZMod\left(2\right)),\; \forall y \in (Fin\left(d\right) \to ZMod\left(2\right)),\; qFree\left(x + y\right) + qFree\left(x\right) + qFree\left(y\right) = \sum_{i:Fin\left(d\right)} (apply\left(x, i\right) \cdot apply\left(y, i\right)) + \sum_{i:Fin\left(d\right)} (apply\left(x, i\right)) \cdot \sum_{i:Fin\left(d\right)} (apply\left(y, i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.qFree_polar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Induction over the number of coordinates proves the polar identity. Arithmetic occurs in ZMod 2.

**Definition 1.4 (character).**

$$\forall d \in \mathbb{N},\; \forall a \in (Fin\left(d\right) \to ZMod\left(2\right)),\; \forall x \in (Fin\left(d\right) \to ZMod\left(2\right)),\; character\left(a, x\right) = bitSign\left(\sum_{i:Fin\left(d\right)} (apply\left(a, i\right) \cdot apply\left(x, i\right))\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.character` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Theorem 1.5 (qFree_walsh_square).**

$$\forall k \in \mathbb{N},\; \forall a \in (Fin\left(2 \cdot k\right) \to ZMod\left(2\right)),\; (walsh\left(a\right))^{2} = (2)^{2 \cdot k}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.qFree_walsh_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Translate one variable in the squared Walsh sum. Character orthogonality annihilates every translation outside the radical; the polar radical is trivial in even dimension.

**Definition 1.6 (walshParity).**

$$\forall k \in \mathbb{N},\; \forall a \in (Fin\left(2 \cdot k\right) \to ZMod\left(2\right)),\; walshParity\left(k, a\right) = If\left(walsh\left(a\right) < 0, 1, 0\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.walshParity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Theorem 1.7 (affine_agreement_bound).**

$$\forall k \in \mathbb{N},\; \forall b \in ZMod\left(2\right),\; \forall a \in (Fin\left(2 \cdot k\right) \to ZMod\left(2\right)),\; RealCast\left(card\left(filter\left(univ, (x:(Fin\left(2 \cdot k\right) \to ZMod\left(2\right))) \mapsto (qFree\left(x\right) = b + \sum_{i:Fin\left(2 \cdot k\right)} (apply\left(a, i\right) \cdot apply\left(x, i\right)))\right)\right)\right) \le \frac{(2)^{2 \cdot k} + (2)^{k}}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.affine_agreement_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Flat Walsh magnitude bounds the number of agreements with every affine function.

## References

- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.affine_agreement_bound`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.character`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.qFree`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.qFree_polar`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.qFree_walsh_square`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.walsh`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh.walshParity`
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates](Coordinates.md)
