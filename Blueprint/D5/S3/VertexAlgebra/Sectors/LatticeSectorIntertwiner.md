# LatticeSectorIntertwiner

## Abstract

LatticeSectorIntertwiner

Construction uses arbitrary ordinary symmetric even integral lattice data, including degenerate forms, zero charges and rank zero. Classification and universality require an explicit two-sided complex inverse Gram matrix, with no positivity or integer unimodularity.

**Definition 1.1 (chargeSpace).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.chargeSpace`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.chargeSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original charge submodule at delta is the range of Finsupp.lsingle delta on oscillator polynomials.

**Theorem 1.2 (word_charge).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.word_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.word_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every lattice D, charges alpha and beta, original oscillator word w, signed integer mode n and oscillator polynomial v, wordField(alpha,w)[n] applied to single(beta,v) lies in chargeSpace(alpha+beta). The original proof covers both actual normal-product branches without a nonsingularity or nonzero-charge hypothesis. It supports charge_homogeneity and the OriginalWord zero-mode calculation; its exposure adds no independently new BPZ result.

**Definition 1.3 (Sector).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.Sector`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.Sector` (`✓ std3`).

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Sector on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement.

**Definition 1.4 (inclusion).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.inclusion`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.inclusion` (`✓ std3`).

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

inclusion on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement.

**Definition 1.5 (projection).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.projection`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.projection` (`✓ std3`).

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

projection on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement.

**Theorem 1.6 (charge_homogeneity).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.charge_homogeneity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.charge_homogeneity` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Every actual ordinary field mode on arbitrary original oscillator inputs has output charge equal to the sum of its two input charges. Both normal-product branches and the polynomial linear extension are covered.

**Definition 1.7 (canonical).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.canonical`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.canonical` (`✓ std3`).

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

canonical on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement.

**Theorem 1.8 (inclusion_canonical).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.inclusion_canonical`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.inclusion_canonical` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

inclusion_canonical on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement.

Classical sources are Bakalov-Kac, arXiv math/0402315v1, section 4.1, and Matsuo-Nagatomo free-boson reconstruction. Imported residue/Pascal and Sugawara suppliers retain Scott Carnahan and Kalle Kytola source attribution and licenses. No literature novelty is claimed.

The category is the neutral Heisenberg sector category. Full charged lattice-VOA modules, dual-lattice coset fusion, coherent associativity and braiding, pentagon and hexagon, Monster or twisted anomaly, CFT, string theory and AdS/CFT remain additional unproved edges. Rank zero has one charge and a one-dimensional IO space; it is not the zero theory.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.Sector`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.canonical`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.chargeSpace`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.charge_homogeneity`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.inclusion`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.inclusion_canonical`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.projection`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner.word_charge`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualStateDerivative](../LatticeActualStateDerivative.md)
