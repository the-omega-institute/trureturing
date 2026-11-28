# Two-level orientation scalar minimum

## Abstract

The exact scalar minimum used by the two-mode Wu orientation reduction.

The source defines axisQuadratic and productQuadratic on real variables, with the minimum theorems imposing nonnegative squared-length hypotheses. axisArg selects the clipped scalar optimizer, axisMinimum evaluates that optimizer, and twoModeMinimum is the smaller of the two axis minima.

**Theorem 1.1 (Axis minimum lower bound).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.axis_minimum_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.axis_minimum_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For nonnegative A and b, axisMinimum is at most axisQuadratic at every u in [0,1].

**Theorem 1.2 (Closed axis minimum formula).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.axis_minimum_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.axis_minimum_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For nonnegative A and b, axisMinimum equals C−b when A=0, C+A/2−b²/(2A) when b≤A and A is nonzero, and C+A−b when b>A.

**Theorem 1.3 (Exact product-simplex minimum).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.twoMode_exact_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.twoMode_exact_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For nonnegative mode coefficients and fields, twoModeMinimum lower-bounds every admissible productQuadratic. An admissible product point attains equality, every admissible axis is above twoModeMinimum, and one of the two axes attains it.

**Theorem 1.4 (Two-plane determinant bound).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.real_two_plane_determinant_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.real_two_plane_determinant_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The squared determinant of two real coordinate pairs is at most the product of their squared lengths.

**Theorem 1.5 (Weighted physical two-plane bound).**

Lean statement: `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.real_two_plane_physical_weight_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.real_two_plane_physical_weight_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For nonnegative A₁ and A₂, twice the weighted sum of the absolute determinants of two real coordinate blocks is at most the corresponding weighted sum of the four squared coordinate lengths.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.axis_minimum_formula`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.axis_minimum_lower`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.real_two_plane_determinant_bound`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.real_two_plane_physical_weight_bound`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuTwoLevelOrientationMinimum.twoMode_exact_minimum`
