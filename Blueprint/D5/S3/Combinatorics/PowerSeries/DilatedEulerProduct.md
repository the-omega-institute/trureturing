# Dilated Euler products

## Abstract

Euler products at multiples of a positive degree.

A dilated Euler series has constant coefficient one, so it defines a unit. Its finite products converge coefficientwise over discrete coefficient rings. Changing the coefficient ring preserves the unit because the undilated coefficients are signed pentagonal indicators.

**Definition 1.1 (euler).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.euler`

*Formalization.* `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.euler` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

Dilate the pentagonal series by a positive natural degree.

**Definition 1.2 (etaUnit).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.etaUnit`

*Formalization.* `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.etaUnit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The corresponding unit, with inverse at constant coefficient one.

**Theorem 1.3 (tendsto_expand_discrete).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.tendsto_expand_discrete`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.tendsto_expand_discrete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

Dilation is continuous for coefficientwise convergence over a discrete ring.

**Theorem 1.4 (euler_tendsto).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.euler_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.euler_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The finite Euler products with exponents d(i+1) converge to the dilated series.

**Theorem 1.5 (euler_const).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.euler_const`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.euler_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The constant coefficient of a dilated Euler product is one.

**Theorem 1.6 (map_eta).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.map_eta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.map_eta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

A ring homomorphism on the coefficients preserves the dilated Euler unit.

**Theorem 1.7 (expand_eta).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.expand_eta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.expand_eta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

Dilating an Euler unit again multiplies its dilation index.

**Theorem 1.8 (prod_split_two).**

Lean statement: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.prod_split_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.prod_split_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

A product through 2N consecutive indices is the product through the N even and the N odd indices.

## References

- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.etaUnit`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.euler`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.euler_const`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.euler_tendsto`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.expand_eta`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.map_eta`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.prod_split_two`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/DilatedEulerProduct.tendsto_expand_discrete`
