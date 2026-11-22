# Exact finite Gibbs-bath label reset

## Abstract

Feasibility and exact minimum Gibbs bandwidth for ambient label reset with the average record preserved.

**Theorem 1.1 (Support of the average record).**

Lean statement: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.average_support_eq_span`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/LabelResetBandwidth.average_support_eq_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Hamed Mohammady, Masoud Mohseni and Yasser Omar (2016). *Minimising the heat dissipation of quantum information erasure*. DOI: [10.1088/1367-2630/18/1/015011](https://doi.org/10.1088/1367-2630/18/1/015011). URL: <https://arxiv.org/abs/1510.02062v2>.

*Commentary.*

For a uniform finite family of pure records the support of the average operator is the span of the record vectors. Positive spectral coordinates on that span give the compressed record state.

**Theorem 1.2 (Dependent records obstruct every faithful-bath reset).**

Lean statement: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.reset_requires_independent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/LabelResetBandwidth.reset_requires_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Hamed Mohammady, Masoud Mohseni and Yasser Omar (2016). *Minimising the heat dissipation of quantum information erasure*. DOI: [10.1088/1367-2630/18/1/015011](https://doi.org/10.1088/1367-2630/18/1/015011). URL: <https://arxiv.org/abs/1510.02062v2>.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Commentary.*

The orthogonal classical labels give input rank db for any full-rank bath of dimension b. A prescribed pure output label and preservation of the average record constrain the output rank to at most rb, where r is the record support dimension. Since b > 0 and r ≤ d, a successful reset forces r = d.

**Theorem 1.3 (Equivalence with maximally mixed preparation).**

Lean statement: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.reset_unitary_orbit_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/LabelResetBandwidth.reset_unitary_orbit_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. E. Allahverdyan, K. V. Hovhannisyan, D. Janzing and G. Mahler (2011). *Thermodynamic limits of dynamic cooling*. DOI: [10.1103/PhysRevE.84.041109](https://doi.org/10.1103/PhysRevE.84.041109). URL: <https://arxiv.org/abs/1107.1044v1>.

*Acknowledgement.* M. Hamed Mohammady, Masoud Mohseni and Yasser Omar (2016). *Minimising the heat dissipation of quantum information erasure*. DOI: [10.1088/1367-2630/18/1/015011](https://doi.org/10.1088/1367-2630/18/1/015011). URL: <https://arxiv.org/abs/1510.02062v2>.

*Commentary.*

With label-sized orthonormal coordinates of the record support and a faithful bath, ambient reset is equivalent to preparation of the compressed record marginal from a maximally mixed memory with that same bath. The lifting theorem constructs a unitary on label, bath and ambient record and fixes its action on every input column.

**Theorem 1.4 (The aligned Gibbs bath and lifted swap attain the minimum).**

Lean statement: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.thermal_reset_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/LabelResetBandwidth.thermal_reset_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Commentary.*

The input is the uniform label ensemble of normalized pure record vectors, tensored with an independent bath. A bath with one basis element per label, in the aligned Gibbs state, and the lifted tensor swap reset the label to any prescribed normalized vector and retain the average record.

**Theorem 1.5 (Minimum bandwidth on the full ambient orbit).**

Lean statement: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.thermal_reset_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/LabelResetBandwidth.thermal_reset_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. E. Allahverdyan, K. V. Hovhannisyan, D. Janzing and G. Mahler (2011). *Thermodynamic limits of dynamic cooling*. DOI: [10.1103/PhysRevE.84.041109](https://doi.org/10.1103/PhysRevE.84.041109). URL: <https://arxiv.org/abs/1107.1044v1>.

*Acknowledgement.* David Reeb, Michael J. Kastoryano and Michael M. Wolf (2011). *Hilbert’s projective metric in quantum information theory*. DOI: [10.1063/1.3615729](https://doi.org/10.1063/1.3615729). URL: <https://arxiv.org/abs/1102.5170v2>.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Acknowledgement.* M. Hamed Mohammady, Masoud Mohseni and Yasser Omar (2016). *Minimising the heat dissipation of quantum information erasure*. DOI: [10.1088/1367-2630/18/1/015011](https://doi.org/10.1088/1367-2630/18/1/015011). URL: <https://arxiv.org/abs/1510.02062v2>.

*Acknowledgement.* Lidia del Rio, Johan Åberg, Renato Renner, Oscar Dahlsten and Vlatko Vedral (2011). *The thermodynamic meaning of negative entropy*. DOI: [10.1038/nature10123](https://doi.org/10.1038/nature10123). URL: <https://arxiv.org/abs/1009.1630v2>.

*Acknowledgement.* Fabien Clivaz, Ralph Silva, Géraldine Haack, Jonatan Bohr Brask, Nicolas Brunner and Marcus Huber (2019). *Unifying paradigms of quantum refrigeration: A universal and attainable bound on cooling*. DOI: [10.1103/PhysRevLett.123.170605](https://doi.org/10.1103/PhysRevLett.123.170605). URL: <https://arxiv.org/abs/1903.04970v2>.

*Commentary.*

For linearly independent normalized records, the exact minimum is β⁻¹ log(μ_max/μ_min) for β > 0. The eigenvalues are the positive eigenvalues of the ambient average record. Every admissible bath has b ≥ dμ_max, and a bath of dimension d attains the bandwidth minimum.

This is a retained-record corollary of the support reduction, the two spectral endpoint bounds and the aligned swap. The output unitary is unrestricted and the preserved quantity is the average record marginal.

**Theorem 1.6 (Linear independence characterizes Gibbs reset feasibility).**

Lean statement: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.independent_iff_exists_gibbs_reset`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/LabelResetBandwidth.independent_iff_exists_gibbs_reset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Hamed Mohammady, Masoud Mohseni and Yasser Omar (2016). *Minimising the heat dissipation of quantum information erasure*. DOI: [10.1088/1367-2630/18/1/015011](https://doi.org/10.1088/1367-2630/18/1/015011). URL: <https://arxiv.org/abs/1510.02062v2>.

*Commentary.*

At each positive inverse temperature, existence of an exact finite Gibbs reset is equivalent to linear independence of the records. The forward construction uses a bath indexed by the labels, and the rank obstruction holds for every finite faithful bath.

**Theorem 1.7 (Compatibility with the qubit erasure orbit).**

Lean statement: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.qubit_output_orbit_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/LabelResetBandwidth.qubit_output_orbit_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parent exact qubit erasure package supplies the characterization in its original register order. An admissible full output lies in the input orbit precisely when its label trace lies in the supported two-qubit orbit.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.average_support_eq_span`
- Truth anchor: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.independent_iff_exists_gibbs_reset`
- Truth anchor: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.qubit_output_orbit_iff`
- Truth anchor: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.reset_requires_independent`
- Truth anchor: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.reset_unitary_orbit_iff`
- Truth anchor: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.thermal_reset_attained`
- Truth anchor: `D5/S3/Quantum/Decoherence/LabelResetBandwidth.thermal_reset_minimum`
- Dependency: [D5/S3/Quantum/Decoherence/ExactQubitBathErasure](ExactQubitBathErasure.md)
- Dependency: [D5/S3/Quantum/Decoherence/GibbsBathBandwidth](GibbsBathBandwidth.md)
- Dependency: [D5/S3/Quantum/Decoherence/LabelResetSupport](LabelResetSupport.md)
