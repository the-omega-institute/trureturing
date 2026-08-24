# Transport Licensing and Scope Overreach

## Abstract

Licensed reports retain transport conditions and expansion reopens completion.

**Theorem 1.1 (Unlicensed scope expansion is overreach).**

$$\begin{gathered}{\operatorname{LicensedReport}\left(q, J, J'\right) \iff \operatorname{reportedScope}\left(q\right) = J' \land \exists \kappa, \operatorname{ValidTransportCert}\left(\kappa, r, \operatorname{concept}\left(q\right), J, J', \operatorname{Version}\left(\operatorname{concept}\left(q\right)\right)\right) \land {\operatorname{condition}\left(q\right) \iff \operatorname{GivenPremises}\left(\kappa\right) \land \operatorname{Holds}\left(\operatorname{TransportAssumption}\left(\kappa\right)\right)}} \land\\{}{\operatorname{LicensedReport}\left(q, J, J'\right) \land \operatorname{condition}\left(q\right) \Rightarrow \exists \kappa, \operatorname{ValidTransportCert}\left(\kappa, r, \operatorname{concept}\left(q\right), J, J', \operatorname{Version}\left(\operatorname{concept}\left(q\right)\right)\right) \land \operatorname{GivenPremises}\left(\kappa\right) \land \operatorname{Holds}\left(\operatorname{TransportAssumption}\left(\kappa\right)\right)} \land\\{}{\operatorname{LicensedReport}\left(q, J, J'\right) \Rightarrow \exists \kappa, \operatorname{ValidTransportCert}\left(\kappa, r, \operatorname{concept}\left(q\right), J, J', \operatorname{Version}\left(\operatorname{concept}\left(q\right)\right)\right) \land {\operatorname{condition}\left(q\right) \iff \operatorname{GivenPremises}\left(\kappa\right) \land \operatorname{Holds}\left(\operatorname{TransportAssumption}\left(\kappa\right)\right)} \land ((\neg\operatorname{GivenPremises}\left(\kappa\right) \lor \neg\operatorname{Holds}\left(\operatorname{TransportAssumption}\left(\kappa\right)\right)) \Rightarrow \neg\operatorname{condition}\left(q\right))} \land\\{}{\operatorname{Overreach}\left(q, J, J'\right) \iff {J \subset J' \land J \neq J'} \land \operatorname{Scope}\left(\operatorname{concept}\left(q\right)\right) = J \land \operatorname{reportedScope}\left(q\right) = J' \land \neg\operatorname{LicensedReport}\left(q, J, J'\right)} \land\\{}{{J \subset J' \land J \neq J'} \land (\forall r, \operatorname{delta}\left(r, r\right) \leq \varepsilon) \land (\exists a, b, \varepsilon < \operatorname{delta}\left(a, b\right)) \Rightarrow \exists S, w, \operatorname{EqOn}\left(S, w, J\right) \land \operatorname{WithinTolerance}\left(\delta, \varepsilon, J, S, w\right) \land \neg\operatorname{WithinTolerance}\left(\delta, \varepsilon, J', S, w\right)} \land\\{}{\exists J_{0}, J_{1}, S, T, {J_{0} \subset J_{1} \land J_{0} \neq J_{1}} \land \operatorname{defectRelation}\left(\operatorname{restrict}\left(S, J_{0}\right), \operatorname{restrict}\left(T, J_{0}\right)\right) = \emptyset \land \operatorname{defectRelation}\left(\operatorname{restrict}\left(S, J_{1}\right), \operatorname{restrict}\left(T, J_{1}\right)\right) \neq \emptyset} \land\\{}{\forall \kappa, \operatorname{reportedScope}\left(q\right) = J' \land \operatorname{ValidTransportCert}\left(\kappa, r, \operatorname{concept}\left(q\right), J, J', \operatorname{Version}\left(\operatorname{concept}\left(q\right)\right)\right) \land \operatorname{GivenPremises}\left(\kappa\right) \land \operatorname{Holds}\left(\operatorname{TransportAssumption}\left(\kappa\right)\right) \Rightarrow \operatorname{LicensedReport}\left(q[\operatorname{condition} := \mathrm{True}], J, J'\right)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/OverreachWithoutLicense.overreach_without_license` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A transport report q stores concept(q), its claimed operation scope J', and its retained proposition condition(q). LicensedReport also checks that the stored scope equals the explicit J', so the target domain cannot drift through a free argument.

ValidTransportCert is the concrete predicate imported from the transport-certificate validity module. Its arguments bind the certificate to the source record r, concept(q), old and claimed scopes, and Version(concept(q)); this module introduces no second validity definition.

A license retains condition(q) exactly as GivenPremises(kappa) conjoined with the certificate's explicit transport-assumption obligations. Therefore an unconditional licensed report exposes proofs of both conjuncts, while a missing conjunct prevents the condition from being discharged.

Overreach is the conjunction of strict scope expansion, Scope(concept(q))=J, the report's claim of J', and absence of a license. No certificate validity or premise is inferred from the scope equations.

For a strict expansion, a new operation is selected with Mathlib's ssubset witness. If unchanged readings remain within epsilon and the reading space admits an above-epsilon deviation, two records agree and fit on J but fail on J'.

CAS defines Closed_J(S,T) exactly by emptiness of defectRelation after restricting S and T to J. A concrete two-operation witness has an empty residual on its old singleton scope and a nonempty residual on the expanded scope, so expansion reopens local completion.

Conversely, when the report's stored scope equals the claimed scope, a valid certificate together with every given premise and its transport assumption licenses the condition-update q[condition := True]. Without the premise and assumption proofs, the exact conditional statement remains the only licensed form.

Repository type-shape, English and Chinese synonym, and neighboring-module searches found no transport-license or overreach definition. Concept, Set.EqOn, and the canonical defectRelation are reused; no second residual or closure predicate is introduced.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/OverreachWithoutLicense.overreach_without_license`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
- Dependency: [D5/S3/ConceptDynamics/Transport/TransportCertificateValidity](TransportCertificateValidity.md)
