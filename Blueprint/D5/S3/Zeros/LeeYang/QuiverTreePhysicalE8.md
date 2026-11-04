# An all-vertex physical tree polynomial with off-circle roots

## Abstract

The all-vertex physical tree Lee-Yang claim has an eight-edge counterexample at tau=-1.

**Definition 1.1 (The number of endpoint incidences).**

Lean statement: `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.deg`

*Formalization.* `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.deg` (`✓ std3`).

*Citation.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

For finite edge type E, deg src tgt v counts every source and target incidence. On the explicit witness the degrees are (2,4,4,1,1,1,1,1,1).

**Definition 1.2 (Endpoint factorial factor).**

Lean statement: `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.fEnd`

*Formalization.* `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.fEnd` (`✓ std3`).

*Citation.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

For a natural number a, fEnd a = (2a)!/((a−1)!a!), with real casts and natural subtraction. This is the endpoint factor from (2.15) on the positive split domain.

**Definition 1.3 (Vertex factorial ratio).**

Lean statement: `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.cVert`

*Formalization.* `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.cVert` (`✓ std3`).

*Citation.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

For natural d and α, cVert d α = (d−1)!/(d−α+2)!, with real casts and natural subtraction. It is the remaining vertex factor in (2.15).

**Definition 1.4 (The all-vertex physical split weight).**

Lean statement: `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.physRho`

*Formalization.* `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.physRho` (`✓ std3`).

*Citation.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

physRho is the unfactorized product over every edge and every vertex: edge binomials, all cVert factors, and the actual fEnd factors at both endpoint incidences. Frozen mass, splits and treePoly are reused; source and target follow the frozen orientation convention.

**Definition 1.5 (The all-vertex physical FMR-P claim).**

Lean statement: `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.claim`

*Formalization.* `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.claim` (`✓ std3`).

*Citation.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

This closed proposition quantifies over finite named spanning trees with at least two edges, all edge totals at least two, and the physical weight physRho at τ=−1. It asserts that every complex root of the frozen tree polynomial has norm one. It uses the all-vertex (2.19) reading; the shorter printed (2.31) expression remains distinct.

**Theorem 1.6 (The all-vertex physical FMR-P claim is false).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Fiol; J. Martínez-Montoya; A. Rios Fukelman (2020). *The planar limit of N=2 superconformal quiver theories*. DOI: [10.1007/JHEP08(2020)161](https://doi.org/10.1007/JHEP08(2020)161). URL: <https://arxiv.org/abs/2006.06379v2>.

*Commentary.*

The explicit nine-vertex, eight-edge witness has all totals equal to three. The proof retains all 256 complementary splits and all 512 spin states per split, keeps all nine actual cVert factors, proves the exact physical normalization (360⁸·36/512), and reduces to the reciprocal polynomial certificate with a nonreal root. Reciprocal lifting yields roots inside and outside the unit circle, so this is a literal closed refutation of the exact physical claim. The readable automorphism factor 72 and source prefactor 120⁸/4 are correspondence only; the kernel result uses the proved nonzero normalization. No claim is made about printed (2.31), an erratum, author intent, priority, other τ, the full tree ensemble or Conjecture 2.

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.cVert`
- Truth anchor: `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.claim`
- Truth anchor: `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.deg`
- Truth anchor: `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.fEnd`
- Truth anchor: `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.physRho`
- Truth anchor: `D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.result`
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
