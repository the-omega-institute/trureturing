# SignDesign

## Abstract

Faithful GHZ–Mermin measurement dependence: SignDesign

**Definition 1.1 (designDensity).**

$$\forall X \in Type,\; \forall C \in Type,\; [Fintype\left(C\right)] \forall c \in (X \to (C \to \mathbb{R})),\; \forall R \in \mathbb{R},\; \forall x \in X,\; \forall a \in C,\; designDensity\left(c, R, x, a\right) = \frac{1 + apply\left(c, x, a\right)}{RealCast\left(card\left(C\right)\right) + R}$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/SignDesign.designDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The exact defining density is (1+c(x,a))/(card C+R). For sign-valued rows it vanishes on negative entries; normalization and variation bounds require the proved row-sum identities.

## References

- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/SignDesign.designDensity`
