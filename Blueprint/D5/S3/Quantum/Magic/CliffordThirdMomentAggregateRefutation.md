# An isotropic aggregate below six

## Abstract

The isotropic aggregate in Zhu, Mao and Yi's Conjecture 2 sums the third-moment expectations over stochastic orthogonal graph subspaces. A normalized two-qudit state in prime dimension five has aggregate 140241723/24017978, strictly below six.

**Definition 1.1 (The oriented graph subspace).**

$$\forall d : \mathbb{N}, \forall O : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \operatorname{ZMod}\left(d\right)\right), \operatorname{graphSubspace}\left(O\right) = \operatorname{range}\left((y : (\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right) \mapsto (\operatorname{mulVec}\left(O, y\right), y))\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.graphSubspace` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

For a three by three matrix O over ZMod d, the graph consists of pairs (Oy,y). The first component is the output and the second component is the input, as in the source operator r(T).

**Theorem 1.2 (Graph subspaces determine their matrices).**

$$\forall d : \mathbb{N}, \operatorname{Injective}\left(\operatorname{graphSubspace}\left((d := d)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.graphSubspace_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the oriented graphs forces equality of the output for every input. Applying this to the three coordinate vectors recovers every matrix column, so graphSubspace is injective.

**Definition 1.3 (Stochastic orthogonal matrices).**

$$\forall d : \mathbb{N}, [\operatorname{NeZero}\left(d\right)] \operatorname{stochasticOrthogonal}\left(d\right) = \operatorname{filter}\left((O : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \operatorname{ZMod}\left(d\right)\right) \mapsto (\forall x : (\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right), \operatorname{dotProduct}\left(\operatorname{mulVec}\left(O, x\right), \operatorname{mulVec}\left(O, x\right)\right) = \operatorname{dotProduct}\left(x, x\right)) \land (\operatorname{mulVec}\left(O, (_ : \operatorname{Fin}\left(3\right) \mapsto 1)\right) = (_ : \operatorname{Fin}\left(3\right) \mapsto 1))), \operatorname{univ}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \operatorname{ZMod}\left(d\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.stochasticOrthogonal` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

The source stochastic orthogonal group consists of matrices preserving x dot x for every vector x and fixing the all-ones vector.

**Theorem 1.4 (Polarization in dimension five).**

$$\forall O : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \operatorname{ZMod}\left(5\right)\right), ((\forall x : (\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(5\right), \operatorname{dotProduct}\left(\operatorname{mulVec}\left(O, x\right), \operatorname{mulVec}\left(O, x\right)\right) = \operatorname{dotProduct}\left(x, x\right)) \land (\operatorname{mulVec}\left(O, (_ : \operatorname{Fin}\left(3\right) \mapsto 1)\right) = (_ : \operatorname{Fin}\left(3\right) \mapsto 1))) \Leftrightarrow ((\operatorname{transpose}\left(O\right) \cdot O = 1) \land (\operatorname{mulVec}\left(O, (_ : \operatorname{Fin}\left(3\right) \mapsto 1)\right) = (_ : \operatorname{Fin}\left(3\right) \mapsto 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.stochasticOrthogonal_five_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over ZMod 5, two is invertible. Expanding the preserved quadratic expression at x+y and subtracting the expressions at x and y proves preservation of x dot y. On coordinate vectors this is transpose(O) O = I. Conversely, that matrix identity preserves x dot x. The all-ones condition is the same on both sides.

**Definition 1.5 (The collection of isotropic graph subspaces).**

$$\forall d : \mathbb{N}, [\operatorname{NeZero}\left(d\right)] \operatorname{isoSubspaces}\left(d\right) = \operatorname{image}\left(\operatorname{graphSubspace}, \operatorname{stochasticOrthogonal}\left(d\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.isoSubspaces` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

The source collection is the image of the stochastic orthogonal group under graphSubspace. Injectivity ensures that summing over this collection counts each matrix graph exactly once.

**Definition 1.6 (The aggregate isotropic expectation).**

$$\forall d : \mathbb{N}, \forall n : \mathbb{N}, [\operatorname{NeZero}\left(d\right)] \forall Psi : ((\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right)) \to \mathbb{C}, \operatorname{kappaIso}\left(d, n, Psi\right) = \sum_{T : \operatorname{Submodule}\left(\operatorname{ZMod}\left(d\right), (((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)) \times ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)))\right), T \in \operatorname{isoSubspaces}\left(d\right)} (\operatorname{kappa}\left(d, n, Psi, T\right))$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.kappaIso` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

The collection of isotropic subspaces is the set of graphs of stochastic orthogonal matrices. Its aggregate is the sum of kappa over exactly those graphs. The expectation kappa, the tensor operator R and the density tensor stateCube use the source trace convention.

**Definition 1.7 (The aggregate lower bound in Conjecture 2).**

$$(claim) \Leftrightarrow (\forall d : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Prime}\left(d\right)\right)] (d \ne 2) \Rightarrow (\forall n : \mathbb{N}, \forall Psi : ((\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right)) \to \mathbb{C}, (\sum_{x : (\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right)} (\left\lVert Psi\left(x\right) \right\rVert^{2}) = 1) \Rightarrow ((6 : \mathbb{C}) \le \operatorname{kappaIso}\left(d, n, Psi\right))))$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.claim` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

The assertion quantifies over every prime dimension other than two, every number of qudits and every normalized complex state. The complex order requires that the aggregate have zero imaginary part and real part at least six.

**Theorem 1.8 (A two-qudit state refutes the bound).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhu-2024-clifford-third-moment-aggregate-lower-bound` (refuted) by `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhu-2024-clifford-third-moment-aggregate-lower-bound","declaration_gid":"D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Take d = 5 and n = 2. The row labels the first qudit and the column labels the second. The integer amplitude matrix has rows (8,-5,0,4,5), (0,3,6,4,-4), (-2,-5,-3,0,3), (-3,0,5,-8,-6), (5,-4,2,-5,0). Divide each amplitude by sqrt(458); the sum of squared amplitudes is 458. The stochastic orthogonal group has twelve matrices: the six permutation matrices and the six row permutations of the matrix with rows (3,4,4), (4,3,4), (4,4,3). For a graph, the trace collapses to a sum over three input copies, with O acting separately on each qudit column. Permuting the rows leaves this expectation unchanged. Each permutation matrix gives one, while each of the other six matrices gives -2577430/(458^3). The latter numerator is the exact integer sum of 15625 products of six amplitudes. Thus the aggregate is 140241723/24017978, and six times the denominator exceeds the numerator by 3866145.

## References

- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.graphSubspace`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.graphSubspace_injective`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.isoSubspaces`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.kappaIso`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.result`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.stochasticOrthogonal`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.stochasticOrthogonal_five_iff`
- Dependency: [D5/S3/Quantum/Magic/CliffordThirdMomentNegativity](CliffordThirdMomentNegativity.md)
