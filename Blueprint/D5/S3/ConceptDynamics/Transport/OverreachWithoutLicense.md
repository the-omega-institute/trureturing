# Transport Licensing and Scope Overreach

## Abstract

Licensed reports retain transport conditions and expansion reopens completion.

**Theorem 1.1 (Unlicensed scope expansion is overreach).**

$$\begin{gathered}{\operatorname{LicensedReport}\left(q, J, J'\right) \iff \operatorname{reportedScope}\left(q\right) = J' \land \exists \kappa, \operatorname{ValidTransportCert}\left(\kappa, r, c, J, J', \operatorname{Version}\left(c\right)\right) \land {\Gamma_{q} \iff \operatorname{GivenPremises}\left(\kappa\right) \land \operatorname{Holds}\left(\operatorname{TransportAssumption}\left(\kappa\right)\right)}} \land\\{}{\Gamma_{q} = top \land \operatorname{LicensedReport}\left(q, J, J'\right) \Rightarrow \exists \kappa, \operatorname{ValidTransportCert}\left(\kappa, r, c, J, J', \operatorname{Version}\left(c\right)\right) \land \operatorname{GivenPremises}\left(\kappa\right) \land \operatorname{Holds}\left(\operatorname{TransportAssumption}\left(\kappa\right)\right)} \land\\{}{\operatorname{LicensedReport}\left(q, J, J'\right) \Rightarrow \exists \kappa, \operatorname{ValidTransportCert}\left(\kappa, r, c, J, J', \operatorname{Version}\left(c\right)\right) \land {\Gamma_{q} \iff \operatorname{GivenPremises}\left(\kappa\right) \land \operatorname{Holds}\left(\operatorname{TransportAssumption}\left(\kappa\right)\right)} \land ((\neg\operatorname{GivenPremises}\left(\kappa\right) \lor \neg\operatorname{Holds}\left(\operatorname{TransportAssumption}\left(\kappa\right)\right)) \Rightarrow \neg\Gamma_{q})} \land\\{}{\operatorname{Overreach}\left(q, J, J'\right) \iff J \subset J' \land \operatorname{Scope}\left(c\right) = J \land \operatorname{reportedScope}\left(q\right) = J' \land \neg\operatorname{LicensedReport}\left(q, J, J'\right)} \land\\{}{J \subset J' \land (\forall r, \operatorname{delta}\left(r, r\right) \leq \varepsilon) \land (\exists a, b, \varepsilon < \operatorname{delta}\left(a, b\right)) \Rightarrow \exists S, w, \operatorname{EqOn}\left(S, w, J\right) \land \operatorname{WithinTolerance}\left(\delta, \varepsilon, J, S, w\right) \land \neg\operatorname{WithinTolerance}\left(\delta, \varepsilon, J', S, w\right)} \land\\{}{J \subset J' \land (\exists a, b, a \neq b) \Rightarrow \exists S, T, \operatorname{LocallyClosed}\left(J, S, T\right) \land \neg\operatorname{LocallyClosed}\left(J', S, T\right)} \land\\{}{\operatorname{reportedScope}\left(q\right) = J' \land \operatorname{ValidTransportCert}\left(\kappa, r, c, J, J', \operatorname{Version}\left(c\right)\right) \land \operatorname{GivenPremises}\left(\kappa\right) \land \operatorname{Holds}\left(\operatorname{TransportAssumption}\left(\kappa\right)\right) \Rightarrow \operatorname{LicensedReport}\left(q_{top}, J, J'\right)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/OverreachWithoutLicense.overreach_without_license` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A transport report stores its concept c, its claimed operation scope J', and its retained proposition Gamma. LicensedReport also checks that the stored scope equals the explicit J', so the target domain cannot drift through a free argument.

ValidTransportCert is the concrete predicate imported from the transport-certificate validity module. Its arguments bind the certificate to the source record r, concept c, old and claimed scopes, and Version(c); this module introduces no second validity definition.

A license retains Gamma exactly as GivenPremises(kappa) conjoined with the certificate's explicit transport-assumption obligations. Therefore an unconditional licensed report exposes proofs of both conjuncts, while a missing conjunct prevents the condition from being discharged.

Overreach is the conjunction of strict scope expansion, Scope(c)=J, the report's claim of J', and absence of a license. No certificate validity or premise is inferred from the scope equations.

For a strict expansion, a new operation is selected with Mathlib's ssubset witness. If unchanged readings remain within epsilon and the reading space admits an above-epsilon deviation, two records agree and fit on J but fail on J'.

Local completion uses the canonical restricted equality Set.EqOn. Two distinct readings at the selected new operation give Closed_J(S,T) and not Closed_J'(S,T), so expansion reopens local completion.

Conversely, when the report's stored scope equals the claimed scope, a valid certificate together with every given premise and its transport assumption licenses the report whose retained condition is True. Without the premise and assumption proofs, the exact conditional statement remains the only licensed form.

Repository type-shape, English and Chinese synonym, and neighboring-module searches found no transport-license or overreach definition. Concept and Set.EqOn are reused; the canonical defectRelation remains untouched because no escape-residual relation is needed here.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/OverreachWithoutLicense.overreach_without_license`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
- Dependency: [D5/S3/ConceptDynamics/Transport/TransportCertificateValidity](TransportCertificateValidity.md)
