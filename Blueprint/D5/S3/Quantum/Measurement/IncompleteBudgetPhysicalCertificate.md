# Incomplete Budget Physical Certificate

## Abstract

A nonzero invisible Hermitian direction gives an explicit physical readout certificate.

**Theorem 1.1 (An invisible direction yields two indistinguishable physical states).**

$$\forall d: Nat, \operatorname{NeZero}(d),\\{}A: \operatorname{Type},\\{}E: A \to \{F: \operatorname{HermitianSpace}(d) \mid \operatorname{PosSemidef}(\operatorname{matrix}(F)) \land \operatorname{PosSemidef}(1 - \operatorname{matrix}(F))\},\\{}D: \operatorname{HermitianSpace}(d),\\{}\operatorname{let} V = \operatorname{span}(\mathbb{R}, \operatorname{insert}(\operatorname{identityHermitian}(d), \{\operatorname{hermitian}(E(i)): i \in A\})), N = \operatorname{orthogonal}(V);\\{}(D \in N \land D \ne 0) \Rightarrow\\{}\exists epsilon: \mathbb{R}, 0 < epsilon \land\\{}\operatorname{let} rho_{+}: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}) = \operatorname{inv}(\operatorname{complex}(d)) \cdot \operatorname{identityMatrix}(d) + \operatorname{complex}(epsilon) \cdot \operatorname{matrix}(D),\\{}rho_{-}: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}) = \operatorname{inv}(\operatorname{complex}(d)) \cdot \operatorname{identityMatrix}(d) - \operatorname{complex}(epsilon) \cdot \operatorname{matrix}(D);\\{}0 \le \operatorname{ofMatrix}(rho_{+}) \land \left(0 \le \operatorname{ofMatrix}(rho_{-}) \land \left(\operatorname{Tr}(rho_{+}) = 1 \land \left(\operatorname{Tr}(rho_{-}) = 1 \land \left(rho_{+} \ne rho_{-} \land \left(\forall i \in A,\; \operatorname{Tr}(rho_{+} \cdot \operatorname{matrix}(E(i))) = \operatorname{Tr}(rho_{-} \cdot \operatorname{matrix}(E(i)))\right)\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/IncompleteBudgetPhysicalCertificate.incomplete_budget_physical_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The visible space is constructed from the identity and the declared positive effects. The supplied nonzero Hermitian direction lies in its Hilbert--Schmidt orthogonal residual.

A norm-controlled positive epsilon perturbs the maximally mixed state in both directions. The public statement records positivity, both trace-one identities, distinction, and equality of every declared Born readout.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/IncompleteBudgetPhysicalCertificate.incomplete_budget_physical_certificate`
- Dependency: [D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence](../Tomography/InformationalCompletenessEquivalence.md)
