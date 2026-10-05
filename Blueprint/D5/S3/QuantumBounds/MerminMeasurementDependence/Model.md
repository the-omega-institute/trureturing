# Model

## Abstract

Faithful GHZ–Mermin measurement dependence: Model

**Definition 1.1 (boolSign).**

$$\forall b \in Bool,\; boolSign\left(b\right) = If\left(b, -1, 1\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.boolSign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Boolean encoding of ±1.

**Definition 1.2 (Setting).**

$$\forall n \in \mathbb{N},\; Setting\left(n\right) = \{x:(Fin\left(n\right) \to Bool) \mid NatMod\left(hammingDist\left(x, const\left(Fin\left(n\right), false\right)\right), 2\right) = 0\}$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.Setting` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Section II, PDF page 1: “The Mermin settings are strings s ∈ {X,Y}^n with an even number of Y's; there are 2^{n−1} of them.” Each setting occurs once.

**Definition 1.3 (Strategy).**

$$\forall n \in \mathbb{N},\; Strategy\left(n\right) = (Fin\left(n\right) \to Prod\left(Bool, Bool\right))$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.Strategy` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Section II, PDF page 1: “A local deterministic model assigns each hidden state λ pre-set answers (a_i, b_i) ∈ {±1}² per party—4^n deterministic strategies—and, for each settings string s, a probability density ρ_s(λ).”

**Definition 1.4 (target).**

$$\forall n \in \mathbb{N},\; \forall x \in Setting\left(n\right),\; target\left(x\right) = boolSign\left(decide\left(NatMod\left(NatDiv\left(hammingDist\left(val\left(x\right), const\left(Fin\left(n\right), false\right)\right), 2\right), 2\right) = 1\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.target` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Section II, PDF page 1: “Quantum mechanics predicts with certainty” E(s)=+1 when #Y(s)≡0 (mod 4), and E(s)=−1 when #Y(s)≡2 (mod 4), “with every proper-subset correlator vanishing.” The two-case displayed source equation appears verbatim in the Library note.

**Definition 1.5 (responseBit).**

$$\forall n \in \mathbb{N},\; \forall lambda \in Strategy\left(n\right),\; \forall x \in Setting\left(n\right),\; \forall i \in Fin\left(n\right),\; responseBit\left(lambda, x, i\right) = If\left(apply\left(val\left(x\right), i\right), snd\left(apply\left(lambda, i\right)\right), fst\left(apply\left(lambda, i\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.responseBit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.6 (response).**

$$\forall n \in \mathbb{N},\; \forall lambda \in Strategy\left(n\right),\; \forall x \in Setting\left(n\right),\; \forall I \in Finset\left(Fin\left(n\right)\right),\; response\left(lambda, x, I\right) = \prod_{i:Fin\left(n\right) \in I} (boolSign\left(responseBit\left(lambda, x, i\right)\right))$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.response` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

A subset correlator is the product of the selected deterministic outcomes.

**Definition 1.7 (IsDensity).**

$$\forall n \in \mathbb{N},\; \forall rho \in (Setting\left(n\right) \to (Strategy\left(n\right) \to \mathbb{R})),\; (IsDensity\left(rho\right)) \Leftrightarrow ((\forall x \in Setting\left(n\right),\; \forall lambda \in Strategy\left(n\right),\; 0 \le apply\left(rho, x, lambda\right)) \land (\forall x \in Setting\left(n\right),\; \sum_{lambda:Strategy\left(n\right)} (apply\left(rho, x, lambda\right)) = 1))$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.IsDensity` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The probability density at each setting is nonnegative and normalized.

**Definition 1.8 (correlator).**

$$\forall n \in \mathbb{N},\; \forall rho \in (Setting\left(n\right) \to (Strategy\left(n\right) \to \mathbb{R})),\; \forall x \in Setting\left(n\right),\; \forall I \in Finset\left(Fin\left(n\right)\right),\; correlator\left(rho, x, I\right) = \sum_{lambda:Strategy\left(n\right)} (apply\left(rho, x, lambda\right) \cdot response\left(lambda, x, I\right))$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.correlator` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Defining expression.

**Definition 1.9 (Faithful).**

$$\forall n \in \mathbb{N},\; \forall rho \in (Setting\left(n\right) \to (Strategy\left(n\right) \to \mathbb{R})),\; (Faithful\left(rho\right)) \Leftrightarrow ((IsDensity\left(rho\right)) \land ((\forall x \in Setting\left(n\right),\; correlator\left(rho, x, univ\right) = target\left(x\right)) \land (\forall x \in Setting\left(n\right),\; \forall I \in Finset\left(Fin\left(n\right)\right),\; (Nonempty\left(I\right)) \Rightarrow ((I \ne univ) \Rightarrow (correlator\left(rho, x, I\right) = 0)))))$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.Faithful` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Section II, PDF page 1: “A model is faithful if it reproduces every full correlator E(s) and every vanishing proper-subset correlator.” Nonempty proper subsets may contain arbitrary mixtures of X and Y measurements.

**Definition 1.10 (M).**

$$\forall n \in \mathbb{N},\; \forall rho \in (Setting\left(n\right) \to (Strategy\left(n\right) \to \mathbb{R})),\; M\left(rho\right) = sSup\left(range\left((xy:Prod\left(Setting\left(n\right), Setting\left(n\right)\right)) \mapsto (\sum_{lambda:Strategy\left(n\right)} (\lvert(apply\left(rho, fst\left(xy\right), lambda\right) - apply\left(rho, snd\left(xy\right), lambda\right))\rvert))\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.M` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Section II, PDF page 1 defines M := max_{s,s′} ∑_λ |ρ_s(λ) − ρ_s′(λ)|. The range is finite and nonempty for n ≥ 3, so sSup equals its maximum.

**Definition 1.11 (F).**

$$\forall n \in \mathbb{N},\; \forall rho \in (Setting\left(n\right) \to (Strategy\left(n\right) \to \mathbb{R})),\; F\left(rho\right) = \frac{M\left(rho\right)}{2}$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.F` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Section II, PDF page 1: “and the fraction of measurement independence surrendered is F := M/2 ∈ [0,1].” F is the surrendered fraction.

**Definition 1.12 (ratio).**

$$\forall n \in \mathbb{N},\; ratio\left(n\right) = (2)^{NatDiv\left(NatSub\left(n, 1\right), 2\right)}$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.ratio` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Section IX, PDF page 4 defines R(n) := 2^{⌊(n−1)/2⌋}.

**Definition 1.13 (floorValue).**

$$\forall n \in \mathbb{N},\; floorValue\left(n\right) = \frac{RealCast\left(ratio\left(n\right)\right)}{2 \cdot \left(RealCast\left(ratio\left(n\right)\right) + 1\right)}$$

*Formalization.* `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.floorValue` (`✓ std3`).

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

The conjectured value R/(2(R+1)), as a real number.

## References

- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.F`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.Faithful`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.IsDensity`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.M`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.Setting`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.Strategy`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.boolSign`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.correlator`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.floorValue`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.ratio`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.response`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.responseBit`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/Model.target`
