# ZverykIdealRigidityRefutation

## Abstract

Virasoro and Borcherds presentation, action, and ideal structure.

**Theorem 1.1 (result).**

$$\neg (\forall (I J H V : \operatorname{Type}) [\operatorname{AddCommGroup} H] [\operatorname{Module} \mathbb{C} H] [\operatorname{AddCommGroup} V] [\operatorname{Module} \mathbb{C} V] (F : \operatorname{EnhancedCartanData} I J H V), \operatorname{F}.\operatorname{IsEnhanced} \to \operatorname{F}.\operatorname{Symmetrizable} \to \forall s t : \mathbb{C} , (s \neq 0 \lor t \neq 0) \to (\operatorname{if} s = 0 \operatorname{then} (\operatorname{F}.\operatorname{heisenberg}).\operatorname{IdealRigidity} \operatorname{else} (\operatorname{F}.\operatorname{deform} s t).\operatorname{Condition43} \to (\operatorname{F}.\operatorname{deform} s t).\operatorname{IdealRigidity}))$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/ZverykIdealRigidityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-zveryk2609c48` (refuted) by `D5/S3/VertexAlgebra/Sectors/ZverykIdealRigidityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-zveryk2609c48","declaration_gid":"D5/S3/VertexAlgebra/Sectors/ZverykIdealRigidityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The rational rank-two datum satisfies (4.3). Its level-four Virasoro singular vector survives the presentation and generates a nonzero ideal disjoint from Cartan. The local relations vanish for this datum.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/ZverykIdealRigidityRefutation.result`
- Dependency: [D5/S3/VertexAlgebra/Sectors/VBKMPresentation](VBKMPresentation.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/VBKMPrimitiveKernel](VBKMPrimitiveKernel.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/VBKMRecursiveAction](VBKMRecursiveAction.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/VBKMSingularVector](VBKMSingularVector.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/VBKMWeightIdeal](VBKMWeightIdeal.md)
