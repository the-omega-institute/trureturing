# Actual periodic two-site collisions

## Abstract

Two-site phase ambiguity for actual periodic binary matrix product states.

**Definition 1.1 (Raw two-site reduced density).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity.rawTwo`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity.rawTwo` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The raw Gram is the two-site amplitude flattening times its conjugate transpose.

**Theorem 1.2 (Rank-four collisions at every ring length at least four).**

$$\forall r \in Nat,\; \exists A \in Fin\left(2\right) \to Bond,\; \exists B \in Fin\left(2\right) \to Bond,\; rank\left(twoFlattening\left(A, r\right)\right) = 4 \land \left(rawTwo\left(B, r\right) = rawTwo\left(A, r\right) \land \left(\left(\forall c \in Complex,\; gamma\left(B, r + 4, 1\right) \ne smul\left(c, gamma\left(A, r + 4, 1\right)\right)\right) \land rawThree\left(B, r\right) \ne rawThree\left(A, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity.actual_two_site_ambiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The target pair has diagonal zero matrix diag(1,i/2) and a one matrix exchanging the virtual basis vectors. Its length-two products span the full bond matrix algebra, which gives rank four at every ring length r+4.

Parity separates the even and odd prefix blocks of the two-site Gram. Reversing the suffix interchanges the odd prefixes, so the odd off-diagonal entry is real. Entrywise conjugation of the pair and one unit phase on the one symbol preserve the entire Gram. The phase is chosen using the even off-diagonal entry.

Two selected words contain exactly two ones and differ in their separation. Their amplitudes have a nonreal projective ratio, so conjugation changes the full state up to every complex scalar despite applying the same phase at both words. Existing three-site recovery then distinguishes the two actual states.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity.actual_two_site_ambiguity`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity.rawTwo`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSParentIntersection](PeriodicMPSParentIntersection.md)
