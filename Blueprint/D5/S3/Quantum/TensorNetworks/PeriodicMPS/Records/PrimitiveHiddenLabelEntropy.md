# The Umegaki information lost by a two-site observer

## Abstract

The Umegaki information lost by a two-site observer.

**Definition 1.1 (Von Neumann entropy in nats).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.entropy`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.entropy` (`✓ std3`).

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

On a finite density state P, the repository alias uses S(P) = −Re tr(P log P). A zero eigenvalue contributes zero. Watrous gives this entropy in bits and the conversion to the natural-log convention multiplies the value by log 2.

**Theorem 1.2 (The spectrum of an equal mixture of two pure states).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.fairMixture_nonzero_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.fairMixture_nonzero_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For unit vectors u and v put s = ∑ⱼ uⱼ conj(vⱼ). The nonzero spectral multiset of their equal mixture consists of (1+|s|)/2 and (1−|s|)/2 with zeros discarded. The weighted two-column Gram matrix gives the same nonzero roots with multiplicity, as in Jozsa and Schlienz, Section 2 (G1). Its characteristic polynomial also gives the coincident-root and proportional-vector cases.

**Theorem 1.3 (Binary entropy of the pure-state mixture).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.fairMixture_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.fairMixture_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

Writing h(t) = −t log t − (1−t) log(1−t), the entropy of the mixture is h((1+|s|)/2). Here h is Real.binEntropy and the endpoint terms use the zero convention.

**Theorem 1.4 (Each pure label has the same finite divergence).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.fairMixture_relativeEntropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.fairMixture_relativeEntropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For P = |u⟩⟨u|, Q = |v⟩⟨v| and M = (P+Q)/2, the support of each label is contained in the support of M. A phase adjustment and a Gram-preserving unitary exchange P and Q while fixing M. The two support-aware Umegaki divergences to M are therefore equal and both are S(M).

**Theorem 1.5 (The two positive weights of the collision mixture).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collisionMixture_nonzero_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collisionMixture_nonzero_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For m ≥ 5 hidden sites and total length n = 2+m, take the fair mixture Mₙ of the two normalized primitive periodic states P₀,ₙ and P₁,ₙ. Put sₙ = collisionNormalizedOverlap(n). The nonproportional rays give |sₙ| < 1. The two positive eigenvalues of Mₙ, counted with multiplicity, are (1±|sₙ|)/2.

**Theorem 1.6 (The primitive collision mixture has rank two).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collisionMixture_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collisionMixture_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

At each n ≥ 7 the nonzero spectral multiset has cardinality two, giving rank two on the full ring.

**Theorem 1.7 (Exact entropy on the full ring).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collisionMixture_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collisionMixture_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

At every n ≥ 7 the fair mixture has entropy h((1+|sₙ|)/2) nats.

**Theorem 1.8 (Both labels have the same literal two-site reduction).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_partialTrace_pure`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_partialTrace_pure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The trace over the last m sites sends each pure label Pᵦ,ₙ to R, the common positive definite trace-one marginal on the first two sites. The four observed eigenvalues are 1/25, 4/25, 4/25 and 16/25.

**Theorem 1.9 (The two-site reduction of the fair mixture).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_partialTrace_mixture`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_partialTrace_mixture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

Taking the literal partial trace of Mₙ gives the same R by linearity.

**Theorem 1.10 (Global and observed Umegaki divergences).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_relativeEntropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_relativeEntropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For either label b the extended divergence D(Pᵦ,ₙ ∥ Mₙ) is finite and equals h((1+|sₙ|)/2). The observed divergence is D(R ∥ R) = 0.

**Definition 1.11 (Definition of the two-site information loss).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collisionDefect`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collisionDefect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The defect is the finite trace-log Umegaki value D(Pᵦ,ₙ ∥ Mₙ) minus the finite trace-log value for their two literal partial traces.

**Theorem 1.12 (Exact loss for either label).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The defect equals S(Mₙ) = h((1+|sₙ|)/2) for every n ≥ 7. In the classical–quantum ensemble, the Holevo information on the full ring is S(Mₙ) because the labels are pure, and the Holevo information on the observed pair is zero because their reductions coincide.

**Theorem 1.13 (The loss tends to one bit).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_defect_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_defect_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The overlap bound |sₙ| ≤ 4(19/20)ⁿ gives sₙ → 0, so continuity of binary entropy gives the limit log 2 nats for each label as n = 7+k grows.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collisionDefect`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collisionMixture_entropy`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collisionMixture_nonzero_spectrum`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collisionMixture_rank`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_defect`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_defect_limit`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_partialTrace_mixture`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_partialTrace_pure`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.collision_relativeEntropy`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.entropy`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.fairMixture_entropy`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.fairMixture_nonzero_spectrum`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy.fairMixture_relativeEntropy`
- Dependency: [D5/S3/Quantum/Algebra/GramUnitaryExtension](../../../Algebra/GramUnitaryExtension.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](../../../Divergence/SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Resource/LogDet/PathSpectralClassical](../../../../Resource/LogDet/PathSpectralClassical.md)
