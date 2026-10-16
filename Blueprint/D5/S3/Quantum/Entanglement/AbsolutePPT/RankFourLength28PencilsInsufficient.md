# Two boundary pencils are insufficient

## Abstract

An explicit counterexample to the length-28 purity implication with only two rank-three pencils.

**Definition 1.1 (The implication with rank-four information omitted).**

$$\forall (lambda:Fin\left(28\right)\Rightarrow\mathbb{R}), ((Antitone\left(lambda\right))\land (\forall (i:Fin\left(28\right)), 0\leq lambda\left(i\right))\land (sum\left(lambda\right)=1)\land (PosSemidef\left(K1\left(boundary\left(lambda\right)\right)\right))\land (PosSemidef\left(K2\left(boundary\left(lambda\right)\right)\right)))\Rightarrow sumSquares\left(lambda\right)\leq \frac{1}{25}$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28PencilsInsufficient.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim retains arbitrary ordered nonnegative length-28 real spectra, mass one, and both original pencils. It omits only the L4 hypothesis. Its type is literally Prop.

**Theorem 1.2 (Both rank-three pencils alone are insufficient).**

$$Not\left(claim\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28PencilsInsufficient.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spectrum with nine entries 2/37 and nineteen entries 1/37 is ordered, nonnegative and has mass one. Both boundary pencils equal (3I-J)/37 and are positive semidefinite. Its purity is 55/1369 = 1/25 + 6/34225, whereas L4=-2/37. Thus the rank-four hypothesis supplies information needed by the stated spectral implication. The result has the literal type Not claim. It refutes neither APPT nor the APPT purity conjecture.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28PencilsInsufficient.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28PencilsInsufficient.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/RankFourLength28Purity](RankFourLength28Purity.md)
