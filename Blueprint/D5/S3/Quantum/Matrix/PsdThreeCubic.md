# PsdThreeCubic

## Abstract

Complex PSD3 cubic geometry and exact scalar coefficients.

**Definition 1.1 (root3).**

Lean statement: `D5/S3/Quantum/Matrix/PsdThreeCubic.root3`

*Formalization.* `D5/S3/Quantum/Matrix/PsdThreeCubic.root3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real power t^(1/3), used only on nonnegative products in the estimates.

**Definition 1.2 (allowance).**

Lean statement: `D5/S3/Quantum/Matrix/PsdThreeCubic.allowance`

*Formalization.* `D5/S3/Quantum/Matrix/PsdThreeCubic.allowance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonnegative edge weights a,b,c, the bound is 2(sqrt(a)sqrt(b)+sqrt(b)sqrt(c)+sqrt(c)sqrt(a))+6(abc)^(1/3).

**Definition 1.3 (pairEnergy).**

Lean statement: `D5/S3/Quantum/Matrix/PsdThreeCubic.pairEnergy`

*Formalization.* `D5/S3/Quantum/Matrix/PsdThreeCubic.pairEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weighted real pair energy a(d+e)x^2+b(e+f)y^2+c(f+d)z^2.

**Theorem 1.4 (negative pair bound).**

Lean statement: `D5/S3/Quantum/Matrix/PsdThreeCubic.negative_pair_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PsdThreeCubic.negative_pair_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative weights a,b,c and edges x,y,z, if the single real quadratic form with diagonal d,e,f and off-diagonal -x,-y,-z is nonnegative on every real vector, its weighted pair energy dominates allowance(a,b,c)xyz. All weights and edges may vanish. A Gram test vector and three-term AM-GM supply the estimate.

**Theorem 1.5 (allowance of p396).**

Lean statement: `D5/S3/Quantum/Matrix/PsdThreeCubic.allowance_of_p396`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PsdThreeCubic.allowance_of_p396` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative a,b,c,k with positive sum of weights, the polynomial bound (a+b+c)k^2 <= 4(a+b+c)(ab+bc+ca)+396abc implies k <= allowance(a,b,c). This is a sufficient comparison and asserts no necessity.

The statements concern the explicitly defined closed algebraic kernels. The commutant equality classification, identification with the original integrals, dominated differentiation and original HSF derivative/source bridge remain outside these results. No assertion about arbitrary matrix dimension or literature novelty follows.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/PsdThreeCubic.allowance`
- Truth anchor: `D5/S3/Quantum/Matrix/PsdThreeCubic.allowance_of_p396`
- Truth anchor: `D5/S3/Quantum/Matrix/PsdThreeCubic.negative_pair_bound`
- Truth anchor: `D5/S3/Quantum/Matrix/PsdThreeCubic.pairEnergy`
- Truth anchor: `D5/S3/Quantum/Matrix/PsdThreeCubic.root3`
