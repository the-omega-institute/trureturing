# GirardPlagneBoxLimit

## Abstract

Fixed-support box Davenport ratios converge to the largest augmented sign determinant in every positive dimension.

**Definition 1.1 (D).**

$$\forall (d m k : \mathbb{N}), D d m k = (\operatorname{sSup} (\operatorname{lengths} d m k))$$

*Formalization.* `D5/S3/Arith/Lattices/GirardPlagneBoxLimit.D` (`✓ std3`).

*Citation.* Benjamin Girard and Alain Plagne (2026). *The Davenport constant of low-dimensional boxes*. DOI: [10.48550/arXiv.2610.16562](https://doi.org/10.48550/arXiv.2610.16562). URL: <https://arxiv.org/abs/2610.16562v1>.

*Commentary.*

Section 2, printed page 2: "we study the quantity D^(d+1)(⟦−m, m⟧^d) which is defined as the maximal length of a minimal zero-sum sequence over ⟦−m, m⟧^d having a support of size d + 1." Multiplicity functions use pointwise subsequence order; support cardinality counts distinct vectors.

**Definition 1.2 (claim).**

$$\operatorname{claim} = (\forall d : \mathbb{N} , 1 \le d \to (\forall m : \mathbb{N} , 1 \le m \to (\operatorname{lengths} d m (d + 1)) . \operatorname{Nonempty} \land \operatorname{BddAbove} (\operatorname{lengths} d m (d + 1))) \land \exists L : \mathbb{R} , \operatorname{Filter} . \operatorname{Tendsto} (\operatorname{fun} m : \mathbb{N} \mapsto (D d m (d + 1) : \mathbb{R}) /  (m : \mathbb{R})^{d}) \operatorname{Filter} . \operatorname{atTop} (\operatorname{nhds} L))$$

*Formalization.* `D5/S3/Arith/Lattices/GirardPlagneBoxLimit.claim` (`✓ std3`).

*Citation.* Benjamin Girard and Alain Plagne (2026). *The Davenport constant of low-dimensional boxes*. DOI: [10.48550/arXiv.2610.16562](https://doi.org/10.48550/arXiv.2610.16562). URL: <https://arxiv.org/abs/2610.16562v1>.

*Commentary.*

Section 2, printed page 4: "It appears tempting to conjecture that for every integer d ≥ 1, the ratio D^(d+1)(⟦−m, m⟧^d)/m^d has a limit when m tends to infinity. This is clear when d = 1, and it follows from Theorems 1 and 5 when d ∈ {2, 3}. However, this problem remains open when d ≥ 4." The natural-number parameter tends to infinity. The length set is nonempty and bounded for every m ≥ 1.

**Theorem 1.3 (girard plagne box limit).**

$$\forall (d : \mathbb{N}), (1 \le d) \to \operatorname{Tendsto} (\operatorname{fun} m : \mathbb{N} \mapsto (D d m (d + 1) : \mathbb{R}) /  (m : \mathbb{R})^{d}) \operatorname{atTop} (\operatorname{nhds} (\operatorname{delta} d : \mathbb{R}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/GirardPlagneBoxLimit.girard_plagne_box_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixed-support box Davenport ratios converge to the largest augmented sign determinant in every positive dimension.

**Theorem 1.4 (result).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/GirardPlagneBoxLimit.result` (`✓ std3`). ∎

*Resolves.* `Problems/girard-plagne-2026-box-davenport-limit` (proved) by `D5/S3/Arith/Lattices/GirardPlagneBoxLimit.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"girard-plagne-2026-box-davenport-limit","declaration_gid":"D5/S3/Arith/Lattices/GirardPlagneBoxLimit.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Girard and Alain Plagne (2026). *The Davenport constant of low-dimensional boxes*. DOI: [10.48550/arXiv.2610.16562](https://doi.org/10.48550/arXiv.2610.16562). URL: <https://arxiv.org/abs/2610.16562v1>.

*Commentary.*

Fixed-support box Davenport ratios converge to the largest augmented sign determinant in every positive dimension.

## References

- Truth anchor: `D5/S3/Arith/Lattices/GirardPlagneBoxLimit.D`
- Truth anchor: `D5/S3/Arith/Lattices/GirardPlagneBoxLimit.claim`
- Truth anchor: `D5/S3/Arith/Lattices/GirardPlagneBoxLimit.girard_plagne_box_limit`
- Truth anchor: `D5/S3/Arith/Lattices/GirardPlagneBoxLimit.result`
- Dependency: [D5/S3/Arith/Lattices/CubeSimplexDeterminant](CubeSimplexDeterminant.md)
- Dependency: [D5/S3/Arith/Lattices/MinimalKernelPacking](MinimalKernelPacking.md)
- Dependency: [D5/S3/Arith/Lattices/PrimitivePencil](PrimitivePencil.md)
