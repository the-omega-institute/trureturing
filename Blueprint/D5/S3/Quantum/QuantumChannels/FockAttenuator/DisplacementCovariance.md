# DisplacementCovariance

## Abstract

The full bosonic attenuator and the coherent-state output-entropy question.

The one-mode space is lp(Function.const(Nat,Complex),2) and the two-mode space is lp(Function.const(Nat,lp(Function.const(Nat,Complex),2)),2). The occupation vector at n is lp.single 2 n (Complex.ofReal 1). All state and environment supports are unrestricted. conjStarAlgEquiv is Mathlib LinearIsometryEquiv.conjStarAlgEquiv, mapping T to U composed with T and U inverse. Function names are the displayed Lean definitions or the explicitly stated Mathlib operations. Application parentheses retain grouping; NatSub is truncated natural subtraction, val is the natural value of a finite index, toReal is the natural-to-real cast and Complex.ofReal is the real-to-complex cast. Fields carrying proofs are omitted from constructor formulas; when a named proof parameter occurs in a function signature it appears as an argument of that function.

**Definition 1.1 (mixture).**

$$\forall iota : \operatorname{Type}\left(\right), (\forall v : iota \to \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right), (\operatorname{mixture}\left(iota, v\right) = \sum'_{i:iota}(\operatorname{rankOne}\left(\mathbb{C}, v\left(i\right), v\left(i\right)\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.mixture` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The operator is the unconditional sum of rank-one projectors. In every state construction below, summability follows from summability of squared vector norms.

**Definition 1.2 (purePartialTrace).**

$$\forall v : \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right)\right), 2\right), (\operatorname{purePartialTrace}\left(v\right) = \operatorname{mixture}\left(\mathbb{N}, (n:\mathbb{N})\mapsto(v\left(n\right))\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.purePartialTrace` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

For a two-mode pure vector the partial trace over the second mode is the sum of the projectors of all first-mode slices. Matrix elements are checked against the contraction by arbitrary first-mode test vectors.

**Definition 1.3 (pairWeyl).**

$$\forall a : \operatorname{Prod}\left(\mathbb{C}, \mathbb{C}\right), (\forall z : \operatorname{Prod}\left(\mathbb{C}, \mathbb{C}\right), (\operatorname{pairWeyl}\left(a, z\right) = \operatorname{tensor}\left(\operatorname{weylVector}\left(\operatorname{fst}\left(a\right), \operatorname{fst}\left(z\right)\right), \operatorname{weylVector}\left(\operatorname{snd}\left(a\right), \operatorname{snd}\left(z\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.pairWeyl` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displayed equation specifies the defining expression.

**Definition 1.4 (pairDisplacement).**

$$\forall a : \operatorname{Prod}\left(\mathbb{C}, \mathbb{C}\right), (\operatorname{pairDisplacement}\left(a\right) = \operatorname{extendOfIsometry}\left(\operatorname{LinearEquivrefl}\left(\mathbb{C}, \operatorname{Finsupp}\left(\operatorname{Prod}\left(\mathbb{C}, \mathbb{C}\right), \mathbb{C}\right)\right), \operatorname{linearCombination}\left(\mathbb{C}, exponentialPair\right), \operatorname{linearCombination}\left(\mathbb{C}, (z:\operatorname{Prod}\left(\mathbb{C}, \mathbb{C}\right))\mapsto(\operatorname{pairWeyl}\left(a, z\right))\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.pairDisplacement` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The product displacement is the dense isometric extension of the two-mode Weyl family, using the same extendOfIsometry convention.

**Theorem 1.5 (partialTrace_pairDisplacement).**

$$\forall a : \operatorname{Prod}\left(\mathbb{C}, \mathbb{C}\right), (\forall w : \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right)\right), 2\right), (\operatorname{purePartialTrace}\left(\operatorname{pairDisplacement}\left(a, w\right)\right) = \operatorname{conjStarAlgEquiv}\left(\operatorname{displacement}\left(\operatorname{fst}\left(a\right)\right), \operatorname{purePartialTrace}\left(w\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.partialTrace_pairDisplacement` (`✓ std3`). ∎

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

A displacement of the discarded mode cancels from every reduced matrix element, while the retained displacement conjugates the reduced operator.

**Theorem 1.6 (beam_displacement).**

$$\forall t : \mathbb{R}, (\forall r : \mathbb{R}, (\forall h : (t)^{2} + (r)^{2} = 1, (\forall a : \operatorname{Prod}\left(\mathbb{C}, \mathbb{C}\right), (\forall w : \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \operatorname{lp}\left(\operatorname{Functionconst}\left(\mathbb{N}, \mathbb{C}\right), 2\right)\right), 2\right), (\operatorname{beamUnitary}\left(t, r, h, \operatorname{pairDisplacement}\left(a, w\right)\right) = \operatorname{pairDisplacement}\left(\operatorname{rotate}\left(t, r, a\right), \operatorname{beamUnitary}\left(t, r, h, w\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.beam_displacement` (`✓ std3`). ∎

*Citation.* Zacharie Van Herstraeten; Saikat Guha; Nicolas J. Cerf (2024). *Classical capacity of quantum non-Gaussian attenuator and amplifier channels*. DOI: [10.1142/S0219749924400033](https://doi.org/10.1142/S0219749924400033). URL: <https://arxiv.org/abs/2312.15623v2>.

*Commentary.*

The displacement commutation identity holds on the entire two-mode Hilbert completion, by continuity from the total exponential family.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.beam_displacement`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.mixture`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.pairDisplacement`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.pairWeyl`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.partialTrace_pairDisplacement`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance.purePartialTrace`
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter](BeamSplitter.md)
