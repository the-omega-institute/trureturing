# Iterated Defect Accumulation

## Abstract

Orbitwise naturality defects accumulate with Lipschitz weights.

**Theorem 1.1 (Iterated naturality defect bound).**

$$\forall n \in \mathbb{N}, \forall y \in Y,\ d_{Z}(\pi(\tau^{n}(y)), \sigma^{n}(\pi(y))) \leq \sum_{k=0}^{n-1} L^{n-1-k} d_{Z}(\pi(\tau(\tau^{k}(y))), \sigma(\pi(\tau^{k}(y)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Naturality/IteratedDefectAccumulation.iterated_naturality_defect_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let tau update the concrete state space Y, let sigma be an L-Lipschitz update of the observed space Z, and let pi project concrete states into Z.

After n updates, the distance between projecting the concrete orbit and following the abstract orbit is bounded by the sum of the one-step naturality defects along the concrete orbit. A defect at step k is weighted by the remaining n minus 1 minus k abstract updates.

The proof is by induction. At a successor step, the triangle inequality separates the newest local defect from the previous accumulated error, and Lipschitz continuity multiplies the latter by L.

Repository search found only a weaker uniform-defect bound. Local mathlib search found no complete nonuniform accumulation theorem; the proof applies LipschitzWith.edist_le_mul, the successor rule for function iterates, and Finset.sum_range_succ.

## References

- Truth anchor: `D5/S3/Observer/Naturality/IteratedDefectAccumulation.iterated_naturality_defect_bound`
