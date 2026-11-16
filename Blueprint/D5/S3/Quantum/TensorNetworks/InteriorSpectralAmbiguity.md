# Canonical spectral exclusion

## Abstract

Canonical REAL13 spectral exclusion and actual ambiguity

**Theorem 1.1 (Nonzero canonical certificate with actual raw interior ambiguity).**

Lean statement: `D5/S3/Quantum/TensorNetworks/InteriorSpectralAmbiguity.canonical_exclusion_actual_ambiguity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralAmbiguity.canonical_exclusion_actual_ambiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For each p,q at least one, P(p,q) is nonzero and for every canonical real x with sigma positive, P(p,q)(x) nonzero, and every e squared=D(coreCoordinates x), there exists a nonzero actual binary bond-two MPS of length N=(p+2)+q with exactly the same ENTIRE raw two-site interior as the canonical state with left L, cores A0,A1 and physical right sqrt(sigma)(1,eta), and no unit complex phase relation to that state. The proof consumes certificate_native, BOTH true native target PosDef conclusions, and the actual public nonzero_locus_actual_ambiguity through the conditional native endpoint and raw_amplitude. Native right is u^N S inverse times the original right. The outer G squared congruence remains outside the right transfer iterate. This canonical supplier is consumed by observed_interior_ambiguity in this same substantive spectral exclusion unit.

**Theorem 1.2 (One observed polynomial for every interior two-site window).**

$$\forall m \in Nat,\; (1 \le m) \Rightarrow (\exists R \in MvPolynomial\left(Sum\left(ObsIndex, ObsIndex\right), Real\right),\; (((((R \neq 0) \land (Nonempty\left(actualPrincipalLocus\left(m, R\right)\right))) \land (IsOpen\left(actualPrincipalLocus\left(m, R\right)\right))) \land (Dense\left(actualPrincipalLocus\left(m, R\right)\right))) \land (\forall psi \in openBoundaryMPS\left(3 + m\right),\; \forall z \in Complex,\; (norm\left(z\right) = 1) \Rightarrow (\exists hz \in Member\left(smul\left(z, psi\right), openBoundaryMPS\left(3 + m\right)\right),\; (Member\left(mk\left(smul\left(z, psi\right), hz\right), actualPrincipalLocus\left(m, R\right)\right)) \Leftrightarrow (Member\left(psi, actualPrincipalLocus\left(m, R\right)\right))))) \land (\forall psi \in openBoundaryMPS\left(3 + m\right),\; (Member\left(psi, actualPrincipalLocus\left(m, R\right)\right)) \Rightarrow (\forall p \in Nat,\; \forall q \in Nat,\; (((1 \le p) \land (1 \le q)) \land (p + q = m + 1)) \Rightarrow (\forall h \in p + 2 + q = 3 + m,\; \exists phi \in openBoundaryMPS\left(3 + m\right),\; ((phi \neq 0) \land (rawInterior\left(p, 2, q, castState\left(h, phi\right)\right) = rawInterior\left(p, 2, q, castState\left(h, psi\right)\right))) \land (\neg (\exists eta \in Complex,\; (norm\left(eta\right) = 1) \land (phi = smul\left(eta, psi\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/InteriorSpectralAmbiguity.observed_interior_ambiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Fix m at least one and N=3+m. In the existing 128 real prefix-Q3 coordinates Omega=(Word3 times Word3) plus itself, clear P(i+1,m-i) through the existing quotient numerator and denominator families to H_i/B_i, for i in Fin m. The literal polynomial is R_m=rho_m times the product of H_i. The product of the canonical P_i is nonzero. Real-polynomial density intersects the existing open nonempty quotientValidityDomain at one common x. Its positive representative is an ACTUAL length-N MPS; quotient retraction recovers x, all actual denominators and B_i are nonzero, and clearing makes every H_i nonzero there. Thus R_m has an actual nonzero evaluation, proves R_m nonzero, and supplies actual_principal_genericity exactly once. Its principal locus is nonempty, relatively open and dense in the ENTIRE literal openBoundaryMPS N subtype, and invariant under U(1). No claim about the Zariski closure is substituted.

For EVERY target psi in this locus, EVERY p,q at least one with p+q=m+1, and EVERY length equality h:((p+2)+q)=3+m, there EXISTS a nonzero phi in the SAME actual image with rawInterior p 2 q (castState h phi)=rawInterior p 2 q (castState h psi), and no unit phase phi=eta times psi. The competitor can depend on the window and has no chart, Regular or locus restriction. In the displayed formula mk is the subtype constructor and amplitude variables use their underlying state functions. The proof obtains the target's positive quotient representative modulo a unit scalar, uses clearing to recover the appropriate P_i nonvanishing, chooses an actual complex square root with IsAlgClosed.exists_pow_nat_eq, and invokes canonical_exclusion_actual_ambiguity. Exact state-length casts and the same unit scalar transport the competitor; scalar cancellation preserves nonphase and nonzero. The live normg_nonzero proof supplies the finite product's nonvanishing through P_nonzero. Generic composition is proof organization, with no separate novelty claim.

The case m=1 is included: N=4 has the single interior pair p=q=1. This is pointwise ambiguity, not a competitor in every neighborhood, and not one competitor with all windows jointly equal. N=3 boundary-only composition, right reversal, one-site partial-trace adapters, full window composition and normalized readings remain obligations. Full C9 remains open and solved-open-problem KPI is zero.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralAmbiguity.canonical_exclusion_actual_ambiguity`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/InteriorSpectralAmbiguity.observed_interior_ambiguity`
- Dependency: [D5/S3/Quantum/TensorNetworks/InteriorSpectralEnvironments](InteriorSpectralEnvironments.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/InteriorSpectralWitness](InteriorSpectralWitness.md)
