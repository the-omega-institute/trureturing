# All-State Skew Symmetry and Supported Formal Reversal

## Abstract

All-State Skew Symmetry and Supported Formal Reversal

Let V be any complex module and A a StateFieldVertexAlgebra. The normalized mode a_n is the coefficient at Laurent exponent -n-1. Vacuum covariance determines the whole creation series. In Borcherds, take p=-1, q=0, r=n and c=vacuum, retain the three finite supports, and use creativity to kill the first branch and every positive-index term in the second. The remaining factor is -(-1)^n. Swapping the states yields skew symmetry with the integer exponent n+j+1, including negative n.

The reversal construction uses the original Hahn-series support: at exponent k, only finitely many j can have s_(k-j) nonzero, and the result is zero below the original order. Thus exp(zT) means the coefficient convolution with T^j/j!, never a numerical exponential or a nilpotence premise.

For the actual lattice construction use A=actualVertexAlgebra(D), its original state-field Y, vacuum and charge-sensitive translation. For charges alpha,beta and arbitrary oscillator descendants u,v, canonical(D,alpha,beta,u)_n v equals the finite sum of (-1)^(n+j+1)/j! times sectorT(D,alpha+beta)^j applied to canonical(D,beta,alpha,v)_(n+j) u. The equality beta+alpha=alpha+beta identifies the output label. Inclusion into the full carrier, single_canonical, and induction from single_sectorT transport the entire translation power, then projection recovers the charge-sector statement. This exact specialization is compiled transient evidence and introduces no orphan binding declaration. It preserves the actual canonical field rather than replacing it by a cocycle model.

No positivity, nonsingularity, homogeneous or primary restriction is imposed. Rank zero, zero states, the vacuum and arbitrary translation descendants remain in scope. This standard algebraic law is not a claim of literature novelty, coherent tensor-category braiding, a Monster realization, analytic CFT, string theory or AdS/CFT completion.

**Theorem 1.1 (The entire vacuum creation series).**

Lean statement: `D5/S3/VertexAlgebra/StateField/SkewSymmetry.creation_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/StateField/SkewSymmetry.creation_coeff` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Induction from translation covariance and creation proves the factorial divided powers for every natural degree.

**Definition 1.2 (Supported exponential reversal coefficient).**

Lean statement: `D5/S3/VertexAlgebra/StateField/SkewSymmetry.reversalTerm`

*Formalization.* `D5/S3/VertexAlgebra/StateField/SkewSymmetry.reversalTerm` (`✓ std3`).

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The jth contribution to exp(zT)s(-z) at Laurent exponent k.

**Theorem 1.3 (Each coefficient has finite convolution support).**

Lean statement: `D5/S3/VertexAlgebra/StateField/SkewSymmetry.reversal_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/StateField/SkewSymmetry.reversal_finite` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The order of the original Hahn series bounds the natural summation index. Zero terms stay zero under all powers of translation.

**Theorem 1.4 (The output retains a lower support bound).**

Lean statement: `D5/S3/VertexAlgebra/StateField/SkewSymmetry.reversal_bounded`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/StateField/SkewSymmetry.reversal_bounded` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Every coefficient below the original series order vanishes.

**Definition 1.5 (Statewise formal reversal).**

Lean statement: `D5/S3/VertexAlgebra/StateField/SkewSymmetry.reversal`

*Formalization.* `D5/S3/VertexAlgebra/StateField/SkewSymmetry.reversal` (`✓ std3`).

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

A Hahn series with the supported convolution coefficients. This uses no numerical operator exponential or local nilpotence.

**Theorem 1.6 (All-state skew symmetry).**

Lean statement: `D5/S3/VertexAlgebra/StateField/SkewSymmetry.skew_symmetry`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/StateField/SkewSymmetry.skew_symmetry` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

For arbitrary signed n and arbitrary states, a_n b is the finite sum of (-1)^(n+j+1)/j! times T^j(b_(n+j) a). Equivalently Y(a,z)b=exp(zT)Y(b,-z)a as Hahn series.

The source-owner Reg mirror attempts the full source reconstruction. Information-escape registration remains unfinished: complete full-family realization, interventions, dependence and current binding evidence are missing. The precise encoding gap is recorded at https://github.com/the-omega-institute/trureturing/issues/21836 under the repository linked-issue exception; neither kernel compilation nor this issue asserts declared_validated registration.

Sources are Matsuo-Nagatomo, hep-th/9706118, and Bakalov-Kac, math/0402315. The underlying actual Borcherds and residue implementations preserve Scott Carnahan source attribution and Apache licensing.

## References

- Truth anchor: `D5/S3/VertexAlgebra/StateField/SkewSymmetry.creation_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/StateField/SkewSymmetry.reversal`
- Truth anchor: `D5/S3/VertexAlgebra/StateField/SkewSymmetry.reversalTerm`
- Truth anchor: `D5/S3/VertexAlgebra/StateField/SkewSymmetry.reversal_bounded`
- Truth anchor: `D5/S3/VertexAlgebra/StateField/SkewSymmetry.reversal_finite`
- Truth anchor: `D5/S3/VertexAlgebra/StateField/SkewSymmetry.skew_symmetry`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualVertexAlgebra](../LatticeActualVertexAlgebra.md)
