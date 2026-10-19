# Relative entropy coherence is at most l1 coherence

## Abstract

The l1 norm of coherence bounds relative entropy coherence in every finite dimension.

**Definition 1.1 (Density matrices).**

$$\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{IsState}\left(rho\right) \Leftrightarrow \left((\operatorname{PosSemidef}\left(rho\right)) \land (\operatorname{trace}\left(rho\right) = 1)\right)$$

*Formalization.* `D5/S3/Divergence/CoherenceL1RelativeEntropyBound.IsState` (`✓ std3`).

*Citation.* Swapan Rana, Preeti Parashar, Maciej Lewenstein (2016). *Trace-distance measure of coherence*. DOI: [10.1103/PhysRevA.93.012110](https://doi.org/10.1103/PhysRevA.93.012110). URL: <https://arxiv.org/abs/1511.01854v2>.

*Commentary.*

A complex matrix is a quantum state exactly when it is positive semidefinite and has trace one.

**Definition 1.2 (Base-2 von Neumann entropy).**

$$\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{vonNeumann2}\left(rho\right) = - \operatorname{re}\left(\operatorname{trace}\left(\operatorname{cfc}\left(((x: \mathbb{R}) \mapsto x \cdot \operatorname{Real}.\operatorname{logb} (2, x)), rho\right)\right)\right)$$

*Formalization.* `D5/S3/Divergence/CoherenceL1RelativeEntropyBound.vonNeumann2` (`✓ std3`).

*Citation.* Swapan Rana, Preeti Parashar, Maciej Lewenstein (2016). *Trace-distance measure of coherence*. DOI: [10.1103/PhysRevA.93.012110](https://doi.org/10.1103/PhysRevA.93.012110). URL: <https://arxiv.org/abs/1511.01854v2>.

*Commentary.*

Entropy is the negative real trace of x log base two x applied by continuous functional calculus; the scalar function is zero at zero.

**Definition 1.3 (The l1 norm of coherence).**

$$\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{CorrelatedCoherenceMonogamyRefutation}.\operatorname{l1Coherence} (rho) = \sum_{i: \operatorname{Fin}\left(n\right)} (\sum_{j: \operatorname{Fin}\left(n\right)} (\operatorname{if} i \ne j \operatorname{then} \Vert rho (i, j)\Vert \operatorname{else} 0))$$

*Formalization.* `D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.l1Coherence` (`✓ std3`).

*Citation.* Swapan Rana, Preeti Parashar, Maciej Lewenstein (2016). *Trace-distance measure of coherence*. DOI: [10.1103/PhysRevA.93.012110](https://doi.org/10.1103/PhysRevA.93.012110). URL: <https://arxiv.org/abs/1511.01854v2>.

*Commentary.*

Section II, Eq. (3b), p. 2 gives Cl1(X) as the sum of |Xij| over i different from j. The complex norm is that absolute value; both indices run through Fin n.

**Definition 1.4 (Relative entropy coherence).**

$$\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{coherenceRel}\left(rho\right) = \operatorname{vonNeumann2}\left(\operatorname{Matrix}.\operatorname{diagonal} (((i: \operatorname{Fin}\left(n\right)) \mapsto rho (i, i)))\right) - \operatorname{vonNeumann2}\left(rho\right)$$

*Formalization.* `D5/S3/Divergence/CoherenceL1RelativeEntropyBound.coherenceRel` (`✓ std3`).

*Citation.* Swapan Rana, Preeti Parashar, Maciej Lewenstein (2016). *Trace-distance measure of coherence*. DOI: [10.1103/PhysRevA.93.012110](https://doi.org/10.1103/PhysRevA.93.012110). URL: <https://arxiv.org/abs/1511.01854v2>.

*Commentary.*

Section III, after Eq. (13), p. 4: “The minimization could be solved analytically [2], leading to Cr(ρ) = S(ρdiag)−S(ρ), where S(ρ) = − Tr(ρ log₂ ρ) is the von Neuman entropy.” The scalar functional calculus uses base-two logarithms.

**Definition 1.5 (Conjecture 7).**

$$claim \Leftrightarrow \forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{IsState}\left(rho\right)) \Rightarrow (\operatorname{coherenceRel}\left(rho\right) \le \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{CorrelatedCoherenceMonogamyRefutation}.\operatorname{l1Coherence} (rho))$$

*Formalization.* `D5/S3/Divergence/CoherenceL1RelativeEntropyBound.claim` (`✓ std3`).

*Citation.* Swapan Rana, Preeti Parashar, Maciej Lewenstein (2016). *Trace-distance measure of coherence*. DOI: [10.1103/PhysRevA.93.012110](https://doi.org/10.1103/PhysRevA.93.012110). URL: <https://arxiv.org/abs/1511.01854v2>.

*Commentary.*

Section III.2, printed p. 5, verbatim: “Conjecture 7. For all states ρ, C_{l1}(ρ) ≥ C_r(ρ).” Here n ranges over every natural number and rho over every complex n by n matrix. The state predicate imposes positive semidefiniteness and unit trace, including singular states.

**Theorem 1.6 (The coherence inequality).**

$$\forall (n: \mathbb{N}), \forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{IsState}\left(rho\right)) \Rightarrow (\operatorname{coherenceRel}\left(rho\right) \le \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Information}.\operatorname{CorrelatedCoherenceMonogamyRefutation}.\operatorname{l1Coherence} (rho))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CoherenceL1RelativeEntropyBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/rana-parashar-lewenstein-2016-l1-relative-entropy-coherence` (proved) by `D5/S3/Divergence/CoherenceL1RelativeEntropyBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rana-parashar-lewenstein-2016-l1-relative-entropy-coherence","declaration_gid":"D5/S3/Divergence/CoherenceL1RelativeEntropyBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Swapan Rana, Preeti Parashar, Maciej Lewenstein (2016). *Trace-distance measure of coherence*. DOI: [10.1103/PhysRevA.93.012110](https://doi.org/10.1103/PhysRevA.93.012110). URL: <https://arxiv.org/abs/1511.01854v2>.

*Commentary.*

A binary pinching is the average of a state and its conjugate by the unitary reflection 2P minus the identity. The binary Holevo inequality bounds its entropy increase by twice the trace norm of the off-diagonal block. Sequential coordinate pinchings preserve positivity and trace and end at the diagonal matrix. Each block has one nonzero row, so its trace norm is the square root of the sum of squared absolute values in that row above the diagonal. Summing the entropy increments gives Cᵣ(rho) ≤ 2 sum over k of the upper-row l2 norms. Each row l2 norm is at most its l1 norm, and Hermitian symmetry makes twice the upper-triangular sum equal l1Coherence.

## References

- Truth anchor: `D5/S3/Divergence/CoherenceL1RelativeEntropyBound.IsState`
- Truth anchor: `D5/S3/Divergence/CoherenceL1RelativeEntropyBound.claim`
- Truth anchor: `D5/S3/Divergence/CoherenceL1RelativeEntropyBound.coherenceRel`
- Truth anchor: `D5/S3/Divergence/CoherenceL1RelativeEntropyBound.result`
- Truth anchor: `D5/S3/Divergence/CoherenceL1RelativeEntropyBound.vonNeumann2`
- Truth anchor: `D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.l1Coherence`
- Dependency: [D5/S3/Divergence/AudenaertBinaryHolevoBound](AudenaertBinaryHolevoBound.md)
- Dependency: [D5/S3/Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics](../Quantum/Dynamics/TridiagonalSweeps/FinitePathDynamics.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Quantum/Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation](../Quantum/Information/CorrelatedCoherenceMonogamyRefutation.md)
