# The stochastic Lagrangian and nonsymmetric aggregates

## Abstract

In dimension five, the stochastic Lagrangian subspaces are exactly the stochastic orthogonal graphs. The same normalized two-qudit state has total aggregate 140241723/24017978 and nonsymmetric aggregate -3866145/24017978, refuting both lower bounds in Zhu, Mao and Yi's Conjecture 2.

**Definition 1.1 (Stochastic Lagrangian subspaces).**

$$\forall d : \mathbb{N}, [\operatorname{NeZero}\left(d\right)] \operatorname{sigmaSubspaces}\left(d\right) = \operatorname{toFinset}\left(\{ T : \operatorname{Submodule}\left(\operatorname{ZMod}\left(d\right), (((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)) \times ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)))\right) | \operatorname{IsStochasticLagrangian}\left(d, T\right) \}\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.sigmaSubspaces` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

The collection contains every submodule satisfying the quadratic condition, dimension three and membership of the all-ones pair. No additional graph condition is imposed.

**Definition 1.2 (Permutation graph subspaces).**

$$\forall d : \mathbb{N}, \operatorname{symSubspaces}\left(d\right) = \operatorname{image}\left((e : \operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right) \mapsto \operatorname{graphSubspace}\left(\operatorname{permMatrix}\left(e, \operatorname{ZMod}\left(d\right)\right)\right)), \operatorname{univ}\left(\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.symSubspaces` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

The symmetric collection consists of the graphs of the permutation matrices of S three, with the source orientation of output followed by input.

**Definition 1.3 (Nonsymmetric subspaces).**

$$\forall d : \mathbb{N}, [\operatorname{NeZero}\left(d\right)] \operatorname{nsSubspaces}\left(d\right) = \operatorname{sigmaSubspaces}\left(d\right) \setminus \operatorname{symSubspaces}\left(d\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.nsSubspaces` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

Remove precisely the permutation graph subspaces from the stochastic Lagrangian collection.

**Definition 1.4 (The full aggregate).**

$$\forall d : \mathbb{N}, \forall n : \mathbb{N}, [\operatorname{NeZero}\left(d\right)] \forall Psi : ((\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right)) \to \mathbb{C}, \operatorname{kappaSigma}\left(d, n, Psi\right) = \sum_{T : \operatorname{Submodule}\left(\operatorname{ZMod}\left(d\right), (((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)) \times ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)))\right), T \in \operatorname{sigmaSubspaces}\left(d\right)} (\operatorname{kappa}\left(d, n, Psi, T\right))$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.kappaSigma` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

Sum the source trace expectation kappa over all members of the stochastic Lagrangian collection.

**Definition 1.5 (The nonsymmetric aggregate).**

$$\forall d : \mathbb{N}, \forall n : \mathbb{N}, [\operatorname{NeZero}\left(d\right)] \forall Psi : ((\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right)) \to \mathbb{C}, \operatorname{kappaNs}\left(d, n, Psi\right) = \sum_{T : \operatorname{Submodule}\left(\operatorname{ZMod}\left(d\right), (((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)) \times ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)))\right), T \in \operatorname{nsSubspaces}\left(d\right)} (\operatorname{kappa}\left(d, n, Psi, T\right))$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.kappaNs` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

Sum the same trace expectation over the nonsymmetric collection.

**Definition 1.6 (The two universal lower bounds).**

$$(claim) \Leftrightarrow ((\forall d : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Prime}\left(d\right)\right)] (d \ne 2) \Rightarrow (\forall n : \mathbb{N}, \forall Psi : ((\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right)) \to \mathbb{C}, (\sum_{x : (\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right)} (\left\lVert Psi\left(x\right) \right\rVert^{2}) = 1) \Rightarrow ((6 : \mathbb{C}) \le \operatorname{kappaSigma}\left(d, n, Psi\right)))) \lor (\forall d : \mathbb{N}, [\operatorname{Fact}\left(\operatorname{Prime}\left(d\right)\right)] (d \ne 2) \Rightarrow (\forall n : \mathbb{N}, \forall Psi : ((\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right)) \to \mathbb{C}, (\sum_{x : (\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right)} (\left\lVert Psi\left(x\right) \right\rVert^{2}) = 1) \Rightarrow ((0 : \mathbb{C}) \le \operatorname{kappaNs}\left(d, n, Psi\right)))))$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.claim` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

The disjunction asserts either the full aggregate lower bound six or the nonsymmetric aggregate lower bound zero, each for every normalized state, every number of qudits and every prime dimension other than two. The order is the complex order.

**Theorem 1.7 (All subspaces are graphs in dimension five).**

$$\operatorname{sigmaSubspaces}\left(5\right) = \operatorname{isoSubspaces}\left(5\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.sigmaSubspaces_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A vector in ZMod 5 cubed with zero coordinate sum and zero sum of squares is zero. In a stochastic Lagrangian subspace this makes the second projection injective: apply the quadratic condition to a pair with second component zero and to its sum with the all-ones pair. Both domain and codomain have dimension three, so the projection is a linear equivalence. Its inverse gives a matrix whose graph is the subspace; the quadratic condition makes this matrix an isometry, and the all-ones pair makes it stochastic. Conversely, every stochastic orthogonal graph satisfies all three defining conditions.

**Theorem 1.8 (Both lower bounds fail).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhu-2024-clifford-third-moment-sigma-lower-bounds` (refuted) by `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhu-2024-clifford-third-moment-sigma-lower-bounds","declaration_gid":"D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Use the normalized two-qudit state psi in dimension five. The graph classification identifies the full aggregate with the isotropic aggregate 140241723/24017978. There are six distinct permutation graphs, each with expectation one, so their removal gives nonsymmetric aggregate -3866145/24017978. The first value is less than six and the second is negative. Thus both universally quantified lower bounds fail.

## References

- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.kappaNs`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.kappaSigma`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.nsSubspaces`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.result`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.sigmaSubspaces`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.sigmaSubspaces_five`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.symSubspaces`
- Dependency: [D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation](CliffordThirdMomentAggregateRefutation.md)
