# Transport-Certificate Validity

## Abstract

Valid transport certificates need locked receipts and nonempty failures.

**Theorem 1.1 (The four claim-bound validity clauses).**

$$\operatorname{ValidTransportCert}(\kappa, c, J, Jprime, nu) \iff \operatorname{ReceiptMatches}(\kappa.Receipt, \operatorname{ClaimAddress}(c), J, nu) \land\\{}((\operatorname{GivenPremises}(\kappa) \land \operatorname{Holds}(\kappa.TransportAssumption)) \Rightarrow \operatorname{ClaimOn}(c, Jprime)) \land\\{}(\forall z \in Jprime \setminus J, \operatorname{PredictionDefined}(\kappa, z)) \land\\{}(\exists z \in Jprime \setminus J, \operatorname{PredictionDefined}(\kappa, z) \land \operatorname{PredictionFails}(\kappa, z) \land \operatorname{Refutes}(z, \kappa, c)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/TransportCertificateValidity.valid_transport_cert_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A transport certificate is the triple consisting of a source receipt, an explicit transport assumption, and a falsifiable prediction. The prediction type itself requires a nonempty failure event in the target-minus-source domain, so constant-false failure data cannot be packaged as a certificate.

Receipt matching binds the original record's source domain, version, error, and transported claim content address. The second clause is conditional: the given premises together with every declared preservation obligation imply that the same claim holds on the target domain.

Selection mechanisms, intervention consistency, covariate transformations, and loss stability each have an explicit dependency flag and preservation obligation in the transport assumption. None is hidden behind an undifferentiated similarity premise.

The last two conjuncts require preregistration over the entire new-domain difference and a concrete point where the prediction is defined, fails, and refutes this certificate's transported claim. The existential closure HasValidTransportCert fixes the version to Version(c) and calls this same predicate, with no Boolean gate.

This formalizes definition-escape-completion-theory atom generic-residual-1e2a241367ada0b7e8670ff4fdba1b0b420500208eb80369635bd5c9bfdb2ff3.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/TransportCertificateValidity.valid_transport_cert_criterion`
