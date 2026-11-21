# Support geometry for finite label reset

## Abstract

Isometric padding and support transfer for finite matrix marginals.

**Theorem 1.1 (Extension with prescribed column action).**

Lean statement: `D5/S3/Quantum/Decoherence/LabelResetSupport.exists_unitary_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/LabelResetSupport.exists_unitary_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If V and W are isometries from the same finite coordinate space to the same ambient space, an ambient unitary U satisfies UV = W. The proof first matches their projections by spectral conjugacy and then fixes the map on the columns.

**Theorem 1.2 (A positive joint state inherits the retained support).**

Lean statement: `D5/S3/Quantum/Decoherence/LabelResetSupport.supported_of_marginal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/LabelResetSupport.supported_of_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Hamed Mohammady, Masoud Mohseni and Yasser Omar (2016). *Minimising the heat dissipation of quantum information erasure*. DOI: [10.1088/1367-2630/18/1/015011](https://doi.org/10.1088/1367-2630/18/1/015011). URL: <https://arxiv.org/abs/1510.02062v2>.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Commentary.*

If the retained marginal of a positive semidefinite joint matrix is VσV*, its joint support lies in the image of I⊗V. Compression with I⊗V recovers the joint matrix in those support coordinates. The trace of the positive compression on the complementary subspace vanishes.

**Theorem 1.3 (A prescribed pure marginal factors off).**

Lean statement: `D5/S3/Quantum/Decoherence/LabelResetSupport.pure_marginal_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/LabelResetSupport.pure_marginal_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Hamed Mohammady, Masoud Mohseni and Yasser Omar (2016). *Minimising the heat dissipation of quantum information erasure*. DOI: [10.1088/1367-2630/18/1/015011](https://doi.org/10.1088/1367-2630/18/1/015011). URL: <https://arxiv.org/abs/1510.02062v2>.

*Commentary.*

A positive semidefinite matrix whose label marginal is the projector of the prescribed normalized vector factors as that projector tensored with its remaining marginal.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/LabelResetSupport.exists_unitary_extension`
- Truth anchor: `D5/S3/Quantum/Decoherence/LabelResetSupport.pure_marginal_factors`
- Truth anchor: `D5/S3/Quantum/Decoherence/LabelResetSupport.supported_of_marginal`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
