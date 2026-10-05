# Construction

## Abstract

Faithful GHZ–Mermin measurement dependence: Construction

**Theorem 1.1 (even_construction).**

$$\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\exists rho \in (Setting\left(2 \cdot k + 2\right) \to (Strategy\left(2 \cdot k + 2\right) \to \mathbb{R})),\; (Faithful\left(rho\right)) \land (F\left(rho\right) = floorValue\left(2 \cdot k + 2\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/Construction.even_construction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Construct mass on the positive rows of the flat-spectrum sign design and lift through parity fibers. The parity_conditioned_moments theorem gives cancellation of every nonempty proper-subset correlator in the lift. Its total variation is bounded by the class-level variation via the frozen data-processing theorem; the universal lower bound gives equality.

## References

- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Construction.even_construction`
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/OddConstruction](OddConstruction.md)
