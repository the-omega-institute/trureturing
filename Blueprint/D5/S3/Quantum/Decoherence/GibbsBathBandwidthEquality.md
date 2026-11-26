# Equality at minimum Gibbs bath bandwidth

## Abstract

Exact bath sizes, output rigidity and heat at minimum Gibbs bandwidth for a two-eigenvalue record.

Consider d equally likely labels with linearly independent normalized pure records. Their average record state has d-dimensional support in the original record space. Write ρ for the state on that support and let its two distinct eigenvalues μ₊ > μ₋ > 0 have multiplicities p and q, with p + q = d.

One unrestricted unitary acts on the label, the bath and the original record space. The bath starts independently in a finite Gibbs state at inverse temperature β > 0. The output must have a prescribed pure label and the original average record marginal. The support reduction in `D5/S3/Quantum/Decoherence/LabelResetBandwidth` connects this reset to the Gibbs preparation bound in `D5/S3/Quantum/Decoherence/GibbsBathBandwidth`. The least bandwidth over finite baths is W = β⁻¹ log(μ₊/μ₋).

**Theorem 1.1 (The ambient output is a product).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality.minimumWidth_ambient_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality.minimumWidth_ambient_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Commentary.*

At bandwidth W every admissible unitary gives the prescribed pure label tensored with the maximally mixed bath I_b/b and the original average record. The ambient formula embeds ρ into its original support and retains the ambient zero modes.

The ratio equality saturates both marginal endpoint bounds. The positive slacks in the joint endpoint bounds annihilate the bath tensor each corresponding record eigenspace. The two record eigenspaces exhaust the support, forcing the product.

**Theorem 1.2 (The bath has two energies with fixed multiplicities).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality.minimumWidth_bath_multiplicities`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality.minimumWidth_bath_multiplicities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. E. Allahverdyan, K. V. Hovhannisyan, D. Janzing and G. Mahler (2011). *Thermodynamic limits of dynamic cooling*. DOI: [10.1103/PhysRevE.84.041109](https://doi.org/10.1103/PhysRevE.84.041109). URL: <https://arxiv.org/abs/1107.1044v1>.

*Commentary.*

In the reduced preparation orbit the bath has only its lowest and highest energies, of multiplicities bp/d and bq/d, respectively, where b is the bath dimension. Equality of the input and output spectra forces both counts. The corresponding Gibbs eigenweights are dμ₊/b and dμ₋/b.

**Theorem 1.3 (Exact bath dimensions at minimum bandwidth).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality.minimumWidth_ambient_dimension_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality.minimumWidth_ambient_dimension_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. E. Allahverdyan, K. V. Hovhannisyan, D. Janzing and G. Mahler (2011). *Thermodynamic limits of dynamic cooling*. DOI: [10.1103/PhysRevE.84.041109](https://doi.org/10.1103/PhysRevE.84.041109). URL: <https://arxiv.org/abs/1107.1044v1>.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Commentary.*

The smallest bath dimension at W is d/gcd(d,p). The admissible dimensions are exactly b = k·d/gcd(d,p) for integers k ≥ 1. Each such dimension admits a bath with energies 0 and W and the required multiplicities. The input and product output have matching spectra on the support, which gives a unitary and lifts to a single unitary on the original ambient space.

Allahverdyan et al., arXiv:1107.1044v1, §IV.B, Eqs. (31)–(32), give the even-bath binary cooling threshold and equal endpoint multiplicities. At zero target gap their population formula inverts to the d = 2 bandwidth threshold. Reeb and Wolf, arXiv:1306.4352v3, §3.3, Eqs. (29)–(32) and the construction on p. 12, give the finite-reservoir lower spectral bound and the engineered Gibbs swap.

**Theorem 1.4 (The actual ambient bath heat at the optimum).**

Lean statement: `D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality.minimumWidth_ambient_heat`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality.minimumWidth_ambient_heat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Reeb and Michael M. Wolf (2014). *An improved Landauer principle with finite-size corrections*. DOI: [10.1088/1367-2630/16/10/103011](https://doi.org/10.1088/1367-2630/16/10/103011). URL: <https://arxiv.org/abs/1306.4352v3>.

*Commentary.*

The heat is the bath energy increase, computed from the bath marginal of the actual ambient output. Every admissible dimension at W gives ΔQ = Wq(1/d − μ₋) = Wpq(μ₊ − μ₋)/d, including the smallest bath.

The high-energy weight increases from qμ₋ to q/d. The weights on the two energy spaces sum to one before and after the operation, so a common shift of the energies cancels.

## References

- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality.minimumWidth_ambient_dimension_iff`
- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality.minimumWidth_ambient_heat`
- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality.minimumWidth_ambient_product`
- Truth anchor: `D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality.minimumWidth_bath_multiplicities`
- Dependency: [D5/S3/Quantum/Decoherence/LabelResetBandwidth](LabelResetBandwidth.md)
- Dependency: [D5/S3/Quantum/Decoherence/ProductRecordBandwidth](ProductRecordBandwidth.md)
- Narrative reference: [D5/S3/Quantum/Decoherence/GibbsBathBandwidth](GibbsBathBandwidth.md)
- Narrative reference: [D5/S3/Quantum/Decoherence/LabelResetBandwidth](LabelResetBandwidth.md)
