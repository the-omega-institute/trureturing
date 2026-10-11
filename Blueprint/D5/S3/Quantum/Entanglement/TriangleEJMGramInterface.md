# Exact EJM Gram probabilities and independent-source noise

## Abstract

The finite exact bridge for PR #15164 has been formalized over rational weights. The regular tetrahedron Gram entries produce the three EJM probability classes 25/256, 1/256 and 5/256, and the three independent source visibilities produce an explicit eight-term multi-affine mixture. These declarations are probability identities only. They do not assert that the EJM table is triangle-local, and they do not provide an inflation certificate.

**Definition 1.1 (Regular tetrahedron Gram entry).**

Lean statement: `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.tetrahedralGram`

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.tetrahedralGram` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv/2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

The exact rational inner product is 1 for equal tetrahedral vertices and -1/3 for distinct vertices.

**Definition 1.2 (EJM Gram probability).**

Lean statement: `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.ejmGramProbability`

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.ejmGramProbability` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv/2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

P(a,b,c) is defined as (4 + S + 6R)/256, where S is the pairwise Gram sum and R is the symmetric quadratic cycle term in the three pairwise Gram entries.

**Theorem 1.3 (Exact EJM probability table).**

Lean statement: `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.ejmGramProbability_table`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.ejmGramProbability_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv/2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

All equal outputs have probability 25/256, exactly two equal outputs have probability 1/256, and all distinct outputs have probability 5/256. The accompanying mass theorem proves that the 64 entries sum to one and nonnegativity is proved separately.

**Definition 1.4 (Finite probability carrier).**

Lean statement: `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.ejmFiniteLaw`

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.ejmFiniteLaw` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv/2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

The EJM table is packaged as Erdos7.FiniteLaw over the three-party output type. This reuses the repository finite rational probability structure.

**Definition 1.5 (Independent-source noise weights).**

Lean statement: `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.sourceNoiseWeight`

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.sourceNoiseWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv/2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

The eight weights correspond to the eight choices of ideal or maximally mixed state on the alpha, beta and gamma source edges.

**Definition 1.6 (Independent-source noise map).**

Lean statement: `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.independentSourceNoise`

*Formalization.* `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.independentSourceNoise` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv/2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

The noisy table is the exact weighted sum of eight component tables. The theorem independentSourceNoise_eight_terms expands this definition into the eight-term multi-affine polynomial from the theory supplement.

**Theorem 1.7 (Noise coefficient normalization).**

Lean statement: `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.sourceNoiseWeight_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.sourceNoiseWeight_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv/2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

The eight source weights sum to one for arbitrary rational visibilities. This is the normalization identity for the source-typed mixture.

**Theorem 1.8 (Edge-wise affinity).**

Lean statement: `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.independentSourceNoise_affine_alpha`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.independentSourceNoise_affine_alpha` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Elisa Bäumer; Victor Gitton; Tamás Kriváchy; Nicolas Gisin; Renato Renner (2024). *Exploring the local landscape in the triangle network*. DOI: [10.48550/arXiv.2405.08939](https://doi.org/10.48550/arXiv/2405.08939). URL: <https://arxiv.org/abs/2405.08939v1>.

*Commentary.*

The source-specific map is affine in each edge visibility. This is a polynomial identity and is not a locality or nonlocality result.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.ejmGramProbability_table`
- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleEJMGramInterface.independentSourceNoise_eight_terms`
- Existing classical anchor: `D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.IsTriangleLocal`
