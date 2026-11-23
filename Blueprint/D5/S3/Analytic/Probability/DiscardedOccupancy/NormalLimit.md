# Gaussian limit for occupancy with discarded throws

## Abstract

The count of distinct ordinary bins hit has a standard Gaussian weak limit after exact row standardization.

**Theorem 1.1 (Gaussian limit of literal occupancy).**

$$\forall (k: \mathbb{N}), 2 \leq k \implies \operatorname{Tendsto}\left((N: \mathbb{N} \mapsto \operatorname{literalLaw}\left(k, N\right)), atTop, \operatorname{nhds}\left(\operatorname{gaussianReal}\left(0, 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.exact_occupancy_normal_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Row N has N plus one ordinary bins and N independent throws. The ordinary-bin masses are one divided by k times the number of bins, and each remaining mass belongs to the discard outcome. Standardization uses the expectation and variance under the product measure in that row. The proof telescopes the conditional characteristic-function comparisons and applies Lévy continuity.

**Definition 1.2 (Deterministic Variance).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (m: \mathbb{N}), (\mathit{deterministicVariance} n p m : \mathbb{R}) = \sum j \in \mathit{Finset}.\mathit{range} m, \mathit{weight} n p m (j + 1) ^ 2 \cdot \mathit{predictableVariance} n p j$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.deterministicVariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.3 (Gaussian Product).**

$$\forall (n: \mathbb{N}), \forall (p: \mathbb{R}), \forall (m: \mathbb{N}), \forall (\tau: \mathbb{R}), \forall (j: \mathbb{N}), (\mathit{gaussianProduct} n p m \tau j : \mathbb{C}) = \prod i \in \mathit{Finset}.\mathit{range} j, \mathit{gaussianFactor} (\mathit{weight} n p m (i + 1) \cdot \tau) (\mathit{predictableVariance} n p i)$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.gaussianProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.4 (Inst Is Probability Measure Forall Fin Option Literal Measure).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (k: \mathbb{N}), \forall (\mathit{hk}: 2 \leq k), \forall (m: \mathbb{N}), \mathit{MeasureTheory}.\mathit{IsProbabilityMeasure} (\mathit{literalMeasure} \mathit{hn} \mathit{hk} m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.instIsProbabilityMeasureForallFinOptionLiteralMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.5 (Literal Count).**

$$\forall (n: \mathbb{N}), \forall (m: \mathbb{N}), \forall (\omega: \mathit{Fin} m \to \mathit{Option} (\mathit{Fin} n)), (\mathit{literalCount} n m \omega : \mathbb{R}) = \mathit{val} \{i : \mathit{Fin} n | \exists (t : \mathit{Fin} m), \omega t = \mathit{some} i\}.\mathit{card}$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literalCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.6 (Literal Law).**

$$\forall (k: \mathbb{N}), \forall (\mathit{hk}: 2 \leq k), \forall (N: \mathbb{N}), \mathit{val} (\mathit{literalLaw} k \mathit{hk} N) = \mathit{Measure}.\mathit{map} (\mathit{literalStandardized} (N + 1) k N) (\mathit{literalMeasure} (N + 1) k N)$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literalLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The standardized occupancy law is the pushforward of the independent throw product measure.

**Definition 1.7 (Literal Measure).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (k: \mathbb{N}), \forall (\mathit{hk}: 2 \leq k), \forall (m: \mathbb{N}), \mathit{literalMeasure} \mathit{hn} \mathit{hk} m = \mathit{Measure}.\mathit{pi} (\mathit{fun} (i : \mathit{Fin} m) \mapsto (\mathit{throwPMF} n (\mathit{paletteP} k)).\mathit{toMeasure})$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literalMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each coordinate has the same one-throw measure. The row measure is the product of these coordinates.

**Definition 1.8 (Literal Standardized).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (k: \mathbb{N}), \forall (\mathit{hk}: 2 \leq k), \forall (m: \mathbb{N}), \forall (\omega: \mathit{Fin} m \to \mathit{Option} (\mathit{Fin} n)), (\mathit{literalStandardized} n \mathit{hn} k \mathit{hk} m \omega : \mathbb{R}) = (\mathit{literalCount} n m \omega - \int (y : \mathit{Fin} m \to \mathit{Option} (\mathit{Fin} n)), \mathit{literalCount} n m y d \mathit{literalMeasure} \mathit{hn} \mathit{hk} m) / \operatorname{sqrt} (\mathit{ProbabilityTheory}.\mathit{variance} (\mathit{literalCount} n m) (\mathit{literalMeasure} \mathit{hn} \mathit{hk} m))$$

*Formalization.* `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literalStandardized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.9 (Literal moments).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 0 < n), \forall (k: \mathbb{N}), \forall (\mathit{hk}: 2 \leq k), \forall (m: \mathbb{N}), \int (\omega : \mathit{Fin} m \to \mathit{Option} (\mathit{Fin} n)), \mathit{literalCount} n m \omega d \mathit{literalMeasure} \mathit{hn} \mathit{hk} m = \mathit{mean} n (\mathit{paletteP} k) m \land \mathit{ProbabilityTheory}.\mathit{variance} (\mathit{literalCount} n m) (\mathit{literalMeasure} \mathit{hn} \mathit{hk} m) = \mathit{variance} n (\mathit{paletteP} k) m$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literal_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a word of m independent throws on n ordinary bins, the real-valued count has the mean and variance of the occupancy recurrence at retention probability one over k.

**Theorem 1.10 (Literal variance eventually positive).**

$$\forall (k: \mathbb{N}), \forall (\mathit{hk}: 2 \leq k), \mathit{Eventually} (N : \mathbb{N}) \mathit{in} \mathit{Filter}.\mathit{atTop}, 0 < \mathit{ProbabilityTheory}.\mathit{variance} (\mathit{literalCount} (N + 1) N) (\mathit{literalMeasure} (N + 1) k N)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literal_variance_eventually_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.11 (Literal variance positive).**

$$\forall (n: \mathbb{N}), \forall (\mathit{hn}: 2 \leq n), \forall (k: \mathbb{N}), \forall (\mathit{hk}: 2 \leq k), 0 < \mathit{ProbabilityTheory}.\mathit{variance} (\mathit{literalCount} n (n - 1)) (\mathit{literalMeasure} n k (n - 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literal_variance_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

## References

- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.deterministicVariance`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.exact_occupancy_normal_limit`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.gaussianProduct`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.instIsProbabilityMeasureForallFinOptionLiteralMeasure`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literalCount`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literalLaw`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literalMeasure`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literalStandardized`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literal_moments`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literal_variance_eventually_positive`
- Truth anchor: `D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit.literal_variance_positive`
- Dependency: [D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic](Characteristic.md)
