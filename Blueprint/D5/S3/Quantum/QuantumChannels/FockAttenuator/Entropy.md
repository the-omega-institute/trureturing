# Entropy

## Abstract

The full bosonic attenuator and the coherent-state output-entropy question.

The one-mode space is lp(Function.const(Nat,Complex),2) and the two-mode space is lp(Function.const(Nat,lp(Function.const(Nat,Complex),2)),2). The occupation vector at n is lp.single 2 n (Complex.ofReal 1). All state and environment supports are unrestricted. conjStarAlgEquiv is Mathlib LinearIsometryEquiv.conjStarAlgEquiv, mapping T to U composed with T and U inverse. Function names are the displayed Lean definitions or the explicitly stated Mathlib operations. Application parentheses retain grouping; NatSub is truncated natural subtraction, val is the natural value of a finite index, toReal is the natural-to-real cast and Complex.ofReal is the real-to-complex cast. Fields carrying proofs are omitted from constructor formulas; when a named proof parameter occurs in a function signature it appears as an argument of that function.

**Definition 1.1 (finiteDiagonal).**

$$\forall N : \mathbb{N}, (\forall p : \operatorname{Fin}\left(N\right) \to \mathbb{R}, (\operatorname{finiteDiagonal}\left(N, p\right) = \sum_{k:\operatorname{Fin}\left(N\right)}(\operatorname{smul}\left(\operatorname{ComplexofReal}\left(p\left(k\right)\right), \operatorname{rankOne}\left(\mathbb{C}, \operatorname{lpsingle}\left(2, \operatorname{val}\left(k\right), \operatorname{ComplexofReal}\left(1\right)\right), \operatorname{lpsingle}\left(2, \operatorname{val}\left(k\right), \operatorname{ComplexofReal}\left(1\right)\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Entropy.finiteDiagonal` (`✓ std3`).

*Citation.* Alfred Wehrl (1978). *General properties of entropy*. DOI: [10.1103/RevModPhys.50.221](https://doi.org/10.1103/RevModPhys.50.221). URL: <https://doi.org/10.1103/RevModPhys.50.221>.

*Commentary.*

The finite diagonal operator is the sum of p(k) times the occupation rank-one projector. Its definition allows arbitrary real entries; the entropy theorem supplies the bounds from zero to one.

**Definition 1.2 (basisEntropy).**

$$\forall T : \operatorname{ContinuousLinearMap}\left(\mathbb{C}, \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right), \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right)\right), (\forall b : \operatorname{HilbertBasis}\left(\mathbb{N}, \mathbb{C}, \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right)\right), (\operatorname{basisEntropy}\left(T, b\right) = \sum'_{n:\mathbb{N}}(\operatorname{ENNRealofReal}\left(\operatorname{negMulLog}\left(\operatorname{Re}\left(\operatorname{inner}\left(\mathbb{C}, b\left(n\right), T\left(b\left(n\right)\right)\right)\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Entropy.basisEntropy` (`✓ std3`).

*Citation.* Alfred Wehrl (1978). *General properties of entropy*. DOI: [10.1103/RevModPhys.50.221](https://doi.org/10.1103/RevModPhys.50.221). URL: <https://doi.org/10.1103/RevModPhys.50.221>.

*Commentary.*

negMulLog(x)=-x log(x), with its continuous value zero at x=0. ENNReal.ofReal embeds a nonnegative real in the extended nonnegative reals; Complex.ofReal embeds a real scalar in Complex; on a density operator every diagonal probability lies in [0,1]. Natural logarithms give nats.

**Definition 1.3 (vonNeumannEntropy).**

$$\forall T : \operatorname{ContinuousLinearMap}\left(\mathbb{C}, \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right), \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right)\right), (\operatorname{vonNeumannEntropy}\left(T\right) = \operatorname{iInf}\left((b:\operatorname{HilbertBasis}\left(\mathbb{N}, \mathbb{C}, \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right)\right))\mapsto(\operatorname{basisEntropy}\left(T, b\right))\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Entropy.vonNeumannEntropy` (`✓ std3`).

*Citation.* Alfred Wehrl (1978). *General properties of entropy*. DOI: [10.1103/RevModPhys.50.221](https://doi.org/10.1103/RevModPhys.50.221). URL: <https://doi.org/10.1103/RevModPhys.50.221>.

*Commentary.*

The definition is the infimum over complete countable orthonormal bases of the diagonal Shannon entropy. Its equality with spectral von Neumann entropy for every density operator is literature-attested, following the eigenbasis and concavity characterization in Wehrl. The infinite-dimensional equivalence is not kernel-proved here. The kernel proves the finite diagonal spectral formula; the final refutation supplies the needed unitary invariance by transporting all Hilbert bases.

**Theorem 1.4 (finiteDiagonal_entropy).**

$$\forall N : \mathbb{N}, (\forall p : \operatorname{Fin}\left(N\right) \to \mathbb{R}, (((\forall j : \operatorname{Fin}\left(N\right), (0 \le p\left(j\right))) \land (\forall j : \operatorname{Fin}\left(N\right), (p\left(j\right) \le 1))) \Rightarrow (\operatorname{vonNeumannEntropy}\left(\operatorname{finiteDiagonal}\left(N, p\right)\right) = \operatorname{ENNRealofReal}\left(\operatorname{shannonEntropy}\left(\operatorname{Fin}\left(N\right), p\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/Entropy.finiteDiagonal_entropy` (`✓ std3`). ∎

*Citation.* Alfred Wehrl (1978). *General properties of entropy*. DOI: [10.1103/RevModPhys.50.221](https://doi.org/10.1103/RevModPhys.50.221). URL: <https://doi.org/10.1103/RevModPhys.50.221>.

*Commentary.*

Concavity of -x log(x), the subprobability row bound and the Parseval column sums give the lower bound in every complete basis. The occupation basis attains it. shannonEntropy is the frozen finite Shannon functional, sum_j negMulLog(p_j). The result does not require the finite entries to sum to one.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Entropy.basisEntropy`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Entropy.finiteDiagonal`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Entropy.finiteDiagonal_entropy`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Entropy.vonNeumannEntropy`
- Dependency: [D5/S3/Entropy/MaxEntropy](../../../Entropy/MaxEntropy.md)
