# AlaiStaircase

## Abstract

Faithful GHZ–Mermin measurement dependence: AlaiStaircase

**Definition 1.1 (classicalS).**

$$\forall n \in \mathbb{N},\; classicalS\left(n\right) = \frac{RealCast\left(ratio\left(n\right)\right) + 1}{2 \cdot RealCast\left(ratio\left(n\right)\right)}$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.classicalS` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Section IX, PDF page 4 defines s(n) := (R+1)/(2R).

**Definition 1.2 (attainableF).**

$$\forall n \in \mathbb{N},\; attainableF\left(n\right) = \{z:\mathbb{R} \mid \exists rho \in (Setting\left(n\right) \to (Strategy\left(n\right) \to \mathbb{R})),\; (Faithful\left(rho\right)) \land (F\left(rho\right) = z)\}$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.attainableF` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Section II, PDF page 1: “The floors reported below are minima of F over all faithful models for the stated finite setting sets; richer scenarios containing them can only raise the values.” This is the set of attainable real F values, rather than a subtype carrier.

**Definition 1.3 (Fmin).**

$$\forall n \in \mathbb{N},\; Fmin\left(n\right) = sInf\left(attainableF\left(n\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.Fmin` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The infimum of attainable values. result proves it is attained and therefore is the minimum specified by the source.

**Definition 1.4 (claim).**

$$(claim) \Leftrightarrow (\forall n \in \mathbb{N},\; (3 \le n) \Rightarrow ((Fmin\left(n\right) = \frac{RealCast\left(ratio\left(n\right)\right)}{2 \cdot \left(RealCast\left(ratio\left(n\right)\right) + 1\right)}) \land ((Fmin\left(n\right) = \frac{1}{4 \cdot classicalS\left(n\right)}) \land ((Fmin\left(n\right) \cdot classicalS\left(n\right) = \frac{1}{4}) \land ((\exists rho \in (Setting\left(n\right) \to (Strategy\left(n\right) \to \mathbb{R})),\; (Faithful\left(rho\right)) \land (F\left(rho\right) = Fmin\left(n\right))) \land (\forall rho \in (Setting\left(n\right) \to (Strategy\left(n\right) \to \mathbb{R})),\; (Faithful\left(rho\right)) \Rightarrow (Fmin\left(n\right) \le F\left(rho\right))))))))$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.claim` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Section IX, Conjecture 1 (Staircase), PDF page 4: “With R(n) := 2^{⌊(n−1)/2⌋} the Mermin violation ratio and s(n) := (R+1)/(2R) the classical satisfiability, F_min(n) = R/(2(R+1)) = 1/(4 s(n)), F_min·s = 1/4.” The Library note quotes the literal source TeX, including the displayed equation. The quantifier n ≥ 3 comes from the scenario in Section II, PDF page 1. Fin n labels parties, ratio is R(n), classicalS is s(n), and Fmin is the infimum of F over faithful models. The assertion includes attainment by a faithful model and the lower bound for every faithful model.

**Theorem 1.5 (result).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.result` (`✓ std3`). ∎

*Resolves.* `Problems/alai-2026-ghz-mermin-staircase` (proved) by `D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"alai-2026-ghz-mermin-staircase","declaration_gid":"D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The odd and even faithful constructions attain the lower bound. The attained infimum is the minimum; real algebra gives its classical-satisfiability form and product identity.

## References

- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.Fmin`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.attainableF`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.claim`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.classicalS`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/AlaiStaircase.result`
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Construction](Construction.md)
