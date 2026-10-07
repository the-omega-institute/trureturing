# OverlapBound

## Abstract

Faithful GHZ–Mermin measurement dependence: OverlapBound

**Theorem 1.1 (pointwise_min_sum).**

$$\forall S \in Type,\; [Fintype\left(S\right)] [DecidableEq\left(S\right)] \forall r \in (S \to \mathbb{R}),\; \forall m \in \mathbb{N},\; (\forall x \in S,\; 0 \le apply\left(r, x\right)) \Rightarrow ((card\left(filter\left(univ, (x:S) \mapsto (apply\left(r, x\right) \ne 0)\right)\right) \le m) \Rightarrow (\sum_{x:S} (\sum_{y:S} (If\left(x = y, 0, min\left(apply\left(r, x\right), apply\left(r, y\right)\right)\right))) \le \left(RealCast\left(m\right) - 1\right) \cdot \sum_{x:S} (apply\left(r, x\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/OverlapBound.pointwise_min_sum` (`✓ std3`). ∎

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Restrict to the support and erase the diagonal. Each inner overlap sum is bounded by (support size−1) times the row mass; summation gives the cap estimate.

**Theorem 1.2 (finite_overlap_lower_bound).**

$$\forall S \in Type,\; \forall A \in Type,\; [Fintype\left(S\right)] [Fintype\left(A\right)] [DecidableEq\left(S\right)] \forall rho \in (S \to (A \to \mathbb{R})),\; \forall m \in \mathbb{N},\; (2 \le card\left(S\right)) \Rightarrow ((\forall x \in S,\; \forall a \in A,\; 0 \le apply\left(rho, x, a\right)) \Rightarrow ((\forall x \in S,\; \sum_{a:A} (apply\left(rho, x, a\right)) = 1) \Rightarrow ((\forall a \in A,\; card\left(filter\left(univ, (x:S) \mapsto (apply\left(rho, x, a\right) \ne 0)\right)\right) \le m) \Rightarrow (\exists x \in S,\; \exists y \in S,\; (x \ne y) \land (\frac{RealCast\left(card\left(S\right)\right) - RealCast\left(m\right)}{RealCast\left(card\left(S\right)\right) - 1} \le totalVariation\left(apply\left(rho, x\right), apply\left(rho, y\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/OverlapBound.finite_overlap_lower_bound` (`✓ std3`). ∎

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Sum all off-diagonal density overlaps and use pointwise_min_sum. At least one pair has overlap at most the average; its total variation is at least (number of settings−cap)/(number of settings−1).

**Theorem 1.3 (literal_index_lower).**

$$\forall n \in \mathbb{N},\; \forall S \in Type,\; [Fintype\left(S\right)] \forall embed \in (S \to Setting\left(n\right)),\; \forall m \in \mathbb{N},\; (2 \le card\left(S\right)) \Rightarrow ((\forall lambda \in Strategy\left(n\right),\; card\left(filter\left(univ, (x:S) \mapsto (response\left(lambda, apply\left(embed, x\right), univ\right) = target\left(apply\left(embed, x\right)\right))\right)\right) \le m) \Rightarrow (\forall rho \in (Setting\left(n\right) \to (Strategy\left(n\right) \to \mathbb{R})),\; (Faithful\left(rho\right)) \Rightarrow (\frac{RealCast\left(card\left(S\right)\right) - RealCast\left(m\right)}{RealCast\left(card\left(S\right)\right) - 1} \le F\left(rho\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminMeasurementDependence/OverlapBound.literal_index_lower` (`✓ std3`). ∎

*Citation.* Aaron Alai (2026). *Exact minimum measurement dependence for faithful local deterministic models of multipartite GHZ–Mermin correlations*. DOI: [10.48550/arXiv.2608.00124](https://doi.org/10.48550/arXiv.2608.00124). URL: <https://arxiv.org/abs/2608.00124v1>.

*Commentary.*

Fin n labels parties; false means X and true means Y. Output bits false and true encode +1 and −1. NatDiv is natural-number division rounded down; NatMod is remainder; NatSub is truncated subtraction. RealCast denotes the embedding into ℝ. All sums and products are finite over the indicated types. const is Function.const, val is subtype projection, fst and snd are pair projections, and apply is function application. ZModCast is the natural-number cast into ZMod 2. toNat is Bool.toNat, and decide turns a decidable proposition into Bool. Subtype displays the underlying value with its verified proof field suppressed. Equiv(toFun,invFun) displays the two maps of the defined equivalence; subtype proof fields are suppressed.

Section VIII, Theorem 5, PDF page 4: the general satisfaction-cap lower bound. Extreme targets force every violating table to have zero density. The pairwise lower bound therefore applies to any chosen finite index set of settings.

## References

- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/OverlapBound.finite_overlap_lower_bound`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/OverlapBound.literal_index_lower`
- Truth anchor: `D5/S3/QuantumBounds/MerminMeasurementDependence/OverlapBound.pointwise_min_sum`
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Model](Model.md)
- Dependency: [D5/S3/TotalVariation/Pinsker](../../TotalVariation/Pinsker.md)
