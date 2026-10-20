# Regularity of the qudit CHSH graph

## Abstract

For every prime p, the qudit CHSH projectors are distinct trace-one idempotents and their orthogonality graph has degree (2p-1)(p-1).

Let p be prime. All matrices have complex entries, and local basis indices and measurement labels lie in ZMod p. The map val takes the representative in {0,...,p-1}. The symbol i is the imaginary unit. Write omega_p for windowRoot(p), X for shiftMatrix(p), and Z for clockMatrix(p), the phase, shift and clock of WindowRegister. Explicitly:

$$
\forall (p: \mathbb{N}), ([\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] ((\omega_{p} = \operatorname{windowRoot}\left(p\right)) \land (\omega_{p} = \exp\left(\frac{2 \cdot \pi \cdot i}{(p: \mathbb{C})}\right))))
$$

$$
\forall (p: \mathbb{N}), ([\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] (\forall (x: \operatorname{ZMod}\left(p\right)), (\forall (y: \operatorname{ZMod}\left(p\right)), (\operatorname{shiftMatrix}\left(p\right)\left(x, y\right) = \begin{cases}1&x = y + 1\\0&\text{otherwise}\end{cases}))))
$$

$$
\forall (p: \mathbb{N}), ([\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] (\forall (x: \operatorname{ZMod}\left(p\right)), (\forall (y: \operatorname{ZMod}\left(p\right)), (\operatorname{clockMatrix}\left(p\right)\left(x, y\right) = \begin{cases}\left(\omega_{p}\right)^{\operatorname{val}\left(x\right)}&x = y\\0&\text{otherwise}\end{cases}))))
$$

Matrix multiplication is the usual product, scalar multiplication acts entrywise, and kronecker denotes the tensor product. Vertex labels are triples (j,k,a), represented as (j,(k,a)). The graph joins distinct labels when the product of their projectors is zero. These are the measurement operators and the orthogonality convention of Howard, Brennan and Vala, Sections 2, 3 and 5.

**Definition 1.1 (Alice's measurement operators).**

$$\forall (p: \mathbb{N}), ([\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] (\forall (j: \operatorname{ZMod}\left(p\right)), (\operatorname{aliceOp}\left(p, j\right) = \begin{cases}\begin{cases}\operatorname{shiftMatrix}\left(p\right)&j = 0\\i \cdot (\operatorname{shiftMatrix}\left(p\right) \cdot \operatorname{clockMatrix}\left(p\right))&\text{otherwise}\end{cases}&p = 2\\\left(\omega_{p}\right)^{\operatorname{val}\left(j \cdot (j + 1)\right)} \cdot (\operatorname{shiftMatrix}\left(p\right) \cdot \operatorname{clockMatrix}\left(p\right)^{\operatorname{val}\left(j\right)})&\text{otherwise}\end{cases})))$$

*Formalization.* `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.aliceOp` (`✓ std3`).

*Citation.* Mark Howard; Eoin Brennan; Jiri Vala (2013). *Quantum Contextuality with Stabilizer States*. DOI: [10.3390/e15062340](https://doi.org/10.3390/e15062340). URL: <https://arxiv.org/abs/1501.04342v1>.

*Commentary.*

Write A_j = aliceOp(p,j). For p=2 the operators are X and Y=iXZ. For odd primes, A_j is the Weyl operator of slope j with phase offset j(j+1). Every exponent of omega or Z is a natural-number representative of a residue.

**Definition 1.2 (Bob's measurement operators).**

$$\forall (p: \mathbb{N}), ([\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] (\forall (k: \operatorname{ZMod}\left(p\right)), (\operatorname{bobOp}\left(p, k\right) = \begin{cases}\begin{cases}\operatorname{shiftMatrix}\left(p\right)&k = 0\\i \cdot (\operatorname{shiftMatrix}\left(p\right) \cdot \operatorname{clockMatrix}\left(p\right))&\text{otherwise}\end{cases}&p = 2\\\left(\omega_{p}\right)^{\operatorname{val}\left(((2: \operatorname{ZMod}\left(p\right))^{-1})^{2} \cdot (k^{2} + 2 \cdot k)\right)} \cdot (\operatorname{shiftMatrix}\left(p\right) \cdot \operatorname{clockMatrix}\left(p\right)^{\operatorname{val}\left((2: \operatorname{ZMod}\left(p\right))^{-1} \cdot k\right)})&\text{otherwise}\end{cases})))$$

*Formalization.* `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.bobOp` (`✓ std3`).

*Citation.* Mark Howard; Eoin Brennan; Jiri Vala (2013). *Quantum Contextuality with Stabilizer States*. DOI: [10.3390/e15062340](https://doi.org/10.3390/e15062340). URL: <https://arxiv.org/abs/1501.04342v1>.

*Commentary.*

Write B_k = bobOp(p,k). For p=2 Bob also uses X and Y=iXZ. For odd primes put h=2 inverse in ZMod p. The slope is hk and the phase offset is h squared times (k squared plus 2k). Multiplication by h permutes the slopes.

**Definition 1.3 (The normalized spectral sum).**

$$\forall (p: \mathbb{N}), ([\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] (\forall (M: \operatorname{Matrix}\left(\operatorname{ZMod}\left(p\right), \operatorname{ZMod}\left(p\right), \mathbb{C}\right)), (\forall (a: \operatorname{ZMod}\left(p\right)), (\operatorname{eigenProj}\left(p, M, a\right) = (p: \mathbb{C})^{-1} \cdot \sum_{(m: \operatorname{Fin}\left(p\right))} (\left(\omega_{p}\right)^{\operatorname{val}\left(-(\operatorname{val}\left(m\right): \operatorname{ZMod}\left(p\right)) \cdot a\right)} \cdot M^{\operatorname{val}\left(m\right)})))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.eigenProj` (`✓ std3`).

*Citation.* Mark Howard; Eoin Brennan; Jiri Vala (2013). *Quantum Contextuality with Stabilizer States*. DOI: [10.3390/e15062340](https://doi.org/10.3390/e15062340). URL: <https://arxiv.org/abs/1501.04342v1>.

*Commentary.*

The sum runs over Fin p, so the matrix powers range from zero to p-1. The displayed definition applies to every complex matrix M of this size. For the measurement operators it is the projector onto the eigenvalue omega raised to a.val. It is the spectral sum of Section 2, Equation (Qproj), with the normalization factor 1/p, which is omitted in the printed equation.

**Definition 1.4 (The projector at a vertex).**

$$\forall (p: \mathbb{N}), ([\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] (\forall (j: \operatorname{ZMod}\left(p\right)), (\forall (k: \operatorname{ZMod}\left(p\right)), (\forall (a: \operatorname{ZMod}\left(p\right)), (\operatorname{vertexProj}\left(p, (j,k,a)\right) = \operatorname{kronecker}\left(\operatorname{eigenProj}\left(p, \operatorname{aliceOp}\left(p, j\right), a\right), \operatorname{eigenProj}\left(p, \operatorname{bobOp}\left(p, k\right), -\left(j \cdot k\right) - a\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.vertexProj` (`✓ std3`).

*Citation.* Mark Howard; Eoin Brennan; Jiri Vala (2013). *Quantum Contextuality with Stabilizer States*. DOI: [10.3390/e15062340](https://doi.org/10.3390/e15062340). URL: <https://arxiv.org/abs/1501.04342v1>.

*Commentary.*

The outcome labels a and b=-jk-a sum to -jk. The product projector is the rank-one summand selected by the CHSH decomposition and Equation (SumRank1). For p=2, -jk equals jk, so the same selection applies.

**Definition 1.5 (Distinctness, projector laws and degree).**

$$\operatorname{claim} \Leftrightarrow (\forall (p: \mathbb{N}), ([\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] ((\operatorname{Injective}\left(\operatorname{vertexProj}\left(p\right)\right)) \land ((\forall (v: \operatorname{Prod}\left(\operatorname{ZMod}\left(p\right), \operatorname{Prod}\left(\operatorname{ZMod}\left(p\right), \operatorname{ZMod}\left(p\right)\right)\right)), ((\operatorname{trace}\left(\operatorname{vertexProj}\left(p, v\right)\right) = 1) \land (\operatorname{vertexProj}\left(p, v\right) \cdot \operatorname{vertexProj}\left(p, v\right) = \operatorname{vertexProj}\left(p, v\right)))) \land (\forall (v: \operatorname{Prod}\left(\operatorname{ZMod}\left(p\right), \operatorname{Prod}\left(\operatorname{ZMod}\left(p\right), \operatorname{ZMod}\left(p\right)\right)\right)), (\operatorname{card}\left(\operatorname{filter}\left(\lambda (w: \operatorname{Prod}\left(\operatorname{ZMod}\left(p\right), \operatorname{Prod}\left(\operatorname{ZMod}\left(p\right), \operatorname{ZMod}\left(p\right)\right)\right)) \mapsto ((w \ne v) \land (\operatorname{vertexProj}\left(p, v\right) \cdot \operatorname{vertexProj}\left(p, w\right) = 0)), (\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{ZMod}\left(p\right), \operatorname{Prod}\left(\operatorname{ZMod}\left(p\right), \operatorname{ZMod}\left(p\right)\right)\right)\right))\right)\right) = (2 \cdot p - 1) \cdot (p - 1)))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.claim` (`✓ std3`).

*Citation.* Mark Howard; Eoin Brennan; Jiri Vala (2013). *Quantum Contextuality with Stabilizer States*. DOI: [10.3390/e15062340](https://doi.org/10.3390/e15062340). URL: <https://arxiv.org/abs/1501.04342v1>.

*Commentary.*

The first conjunct asserts injectivity on all p cubed labels. The second asserts trace one and idempotence for every projector. The third counts all distinct labels whose projector product with a fixed vertex is zero. It states the regularity conjecture of Section 5 together with the distinctness and projector properties of its construction. The displayed subtractions in the degree are in the natural numbers.

**Theorem 1.6 (The qudit CHSH graph is regular).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.result` (`✓ std3`). ∎

*Resolves.* `Problems/howard-brennan-vala-2013-chsh-graph-regularity` (proved) by `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"howard-brennan-vala-2013-chsh-graph-regularity","declaration_gid":"D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mark Howard; Eoin Brennan; Jiri Vala (2013). *Quantum Contextuality with Stabilizer States*. DOI: [10.3390/e15062340](https://doi.org/10.3390/e15062340). URL: <https://arxiv.org/abs/1501.04342v1>.

*Commentary.*

Fix a prime p and write omega=omega_p and chi(t)=omega raised to t.val. For odd p, let h be the inverse of 2. The chirp eigenvector of omega raised to c.val times X Z raised to s.val, with eigenvalue omega raised to a.val, has x component p raised to -1/2 times chi((c-a)x+s h x(x-1)). Successive phase differences give the Weyl operator. Summing its powers shows that the normalized spectral projector is the outer product of this vector with its conjugate. The vector has squared length one, so the projector has trace one and is idempotent. Alice uses s=j and c=j(j+1); Bob uses s=hk and c=h squared times (k squared plus 2k).

Within a basis, character orthogonality gives zero overlap between different outcomes. For odd p, across different bases the overlap is a quadratic character sum. Multiply that sum by its conjugate and set x=y+t. For every nonzero t the remaining linear character in y sums to zero; the zero shift contributes p. After normalization the squared overlap is 1/p. At p=2 the normalized vectors have x components 2 raised to -1/2 times chi(-a x), multiplied by 1 for setting zero and by i raised to x.val for setting one. Direct calculation gives the same orthogonality and squared overlap 1/2 for the X and Y bases.

Write v=(j,k,a), w=(j',k',a'), b=-jk-a and b'=-j'k'-a'. A tensor product of matrices is zero exactly when a factor is zero. Consequently the adjacency rule is: j=j' and a differs from a', or k=k' and b differs from b'. For a fixed v, the first set has p(p-1) elements. The second also has p(p-1), because each choice of j' excludes exactly one a'. Their intersection has j'=j and k'=k, leaving p-1 choices of a'. Inclusion-exclusion therefore gives 2p(p-1)-(p-1)=(2p-1)(p-1). Neither set contains v.

For distinctness, take the trace of the product of two vertex projectors. It is the product of the two local squared overlaps. Each local value is 1 for equal settings and outcomes, 0 for equal settings and different outcomes, and 1/p for different settings. Equal vertex projectors have product trace one by trace one and idempotence. Since p is at least two, this forces both settings and Alice's outcome to agree, and hence the labels are identical. The graph thus has p cubed distinct vertices and the asserted degree.

## References

- Truth anchor: `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.aliceOp`
- Truth anchor: `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.bobOp`
- Truth anchor: `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.claim`
- Truth anchor: `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.eigenProj`
- Truth anchor: `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.result`
- Truth anchor: `D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.vertexProj`
- Dependency: [D5/S3/Fourier/SparseGeneratorFamily](../../Fourier/SparseGeneratorFamily.md)
- Dependency: [D5/S3/Observer/BornReduction](../../Observer/BornReduction.md)
- Dependency: [D5/S3/Observer/MatrixUnitCertificate](../../Observer/MatrixUnitCertificate.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
