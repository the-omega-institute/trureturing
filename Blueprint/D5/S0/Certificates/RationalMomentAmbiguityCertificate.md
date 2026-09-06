# Moment ambiguity and exact contact certificates

## Abstract

Rational contacts certify an attained largest query difference and an attained least residual budget. Support-monotone compression preserves their optimality.

All coefficients are rational. Feature has type Fin n to Fin d to Q; query and the two weights have type Fin n to Q; tolerance and predictor coefficients have type Fin d to Q. Indices i and j range over Fin n and Fin d respectively. Named applications also denote structure-field access.

**Definition 1.1 (Two probability laws with moment tolerances).**

$$\forall n, d, feature, tolerance, high, low, (\operatorname{MomentTolerancePair}(feature, tolerance, high, low)) \Leftrightarrow ((\forall i, (0) \le (\operatorname{high}(i))) \land ((\sum_{i} (\operatorname{high}(i))) = (1)) \land (\forall i, (0) \le (\operatorname{low}(i))) \land ((\sum_{i} (\operatorname{low}(i))) = (1)) \land (\forall j, (\lvert(\operatorname{linearObjective}((\lambda i \mapsto \operatorname{feature}(i, j)), high)) - (\operatorname{linearObjective}((\lambda i \mapsto \operatorname{feature}(i, j)), low))\rvert) \le (\operatorname{tolerance}(j))))$$

*Formalization.* `D5/S0/Certificates/RationalMomentAmbiguityCertificate.MomentTolerancePair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Tolerances compare the two models directly. The laws have separate nonnegativity and normalization conditions.

**Definition 1.2 (Envelope on every allowed atom).**

$$\forall n, d, feature, query, envelope, (\operatorname{GlobalQueryEnvelope}(feature, query, envelope)) \Leftrightarrow (\forall i, ((\operatorname{lower}(envelope)) \le (\operatorname{queryResidual}(feature, query, envelope, i))) \land ((\operatorname{queryResidual}(feature, query, envelope, i)) \le (\operatorname{upper}(envelope))))$$

*Formalization.* `D5/S0/Certificates/RationalMomentAmbiguityCertificate.GlobalQueryEnvelope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The check covers the whole carrier, including atoms absent from both proposed witnesses.

**Definition 1.3 (Slope-weighted uncertainty cost).**

$$\forall d, tolerance, envelope, (\operatorname{momentToleranceCost}(tolerance, envelope)) = (\sum_{j} ((\lvert\operatorname{coefficient}(envelope, j)\rvert) \cdot (\operatorname{tolerance}(j))))$$

*Formalization.* `D5/S0/Certificates/RationalMomentAmbiguityCertificate.momentToleranceCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Absolute predictor slopes weight the coordinatewise moment tolerances.

**Definition 1.4 (Width plus uncertainty).**

$$\forall d, tolerance, envelope, (\operatorname{residualBudget}(tolerance, envelope)) = (((\operatorname{upper}(envelope)) - (\operatorname{lower}(envelope))) + (\operatorname{momentToleranceCost}(tolerance, envelope)))$$

*Formalization.* `D5/S0/Certificates/RationalMomentAmbiguityCertificate.residualBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the dual value compared against all admissible query differences.

**Theorem 1.5 (Uniform query bound).**

$$\forall n, d, feature, query, tolerance, high, low, envelope, ((\operatorname{MomentTolerancePair}(feature, tolerance, high, low)) \land (\operatorname{GlobalQueryEnvelope}(feature, query, envelope))) \Rightarrow ((\lvert(\operatorname{linearObjective}(query, high)) - (\operatorname{linearObjective}(query, low))\rvert) \le (\operatorname{residualBudget}(tolerance, envelope)))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentAmbiguityCertificate.query_gap_le_residualBudget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing expectation enclosure is applied to both laws, then their predictor-center difference is bounded using the nominated moment errors.

**Theorem 1.6 (Exact three-part gap identity).**

$$\forall n, d, feature, query, tolerance, high, low, envelope, (((\sum_{i} (\operatorname{high}(i))) = (1)) \land ((\sum_{i} (\operatorname{low}(i))) = (1))) \Rightarrow (((\operatorname{residualBudget}(tolerance, envelope)) - (((\operatorname{linearObjective}(query, high)) - (\operatorname{linearObjective}(query, low))))) = (((\sum_{i} ((((\operatorname{upper}(envelope)) - (\operatorname{queryResidual}(feature, query, envelope, i)))) \cdot (\operatorname{high}(i)))) + (\sum_{i} ((((\operatorname{queryResidual}(feature, query, envelope, i)) - (\operatorname{lower}(envelope)))) \cdot (\operatorname{low}(i))))) + (\sum_{j} (((\lvert\operatorname{coefficient}(envelope, j)\rvert) \cdot (\operatorname{tolerance}(j))) - ((\operatorname{coefficient}(envelope, j)) \cdot (((\operatorname{linearObjective}((\lambda i \mapsto \operatorname{feature}(i, j)), high)) - (\operatorname{linearObjective}((\lambda i \mapsto \operatorname{feature}(i, j)), low)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentAmbiguityCertificate.primal_dual_gap_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity requires only normalization. Under pair and global-envelope feasibility its upper-contact, lower-contact and signed-moment contributions are all nonnegative.

**Definition 1.7 (Data-only certificate).**

Lean statement: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.ContactCertificate`

*Formalization.* `D5/S0/Certificates/RationalMomentAmbiguityCertificate.ContactCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The structure has exactly high : Fin n to Q, low : Fin n to Q, and envelope : QueryEnvelope d. There are no proof fields.

**Definition 1.8 (Contact and alignment conditions).**

$$\forall n, d, feature, query, tolerance, certificate, (\operatorname{ValidContactCertificate}(feature, query, tolerance, certificate)) \Leftrightarrow ((\operatorname{MomentTolerancePair}(feature, tolerance, \operatorname{high}(certificate), \operatorname{low}(certificate))) \land (\operatorname{GlobalQueryEnvelope}(feature, query, \operatorname{envelope}(certificate))) \land (\forall i, ((\operatorname{high}(certificate, i)) \neq (0)) \Rightarrow ((\operatorname{queryResidual}(feature, query, \operatorname{envelope}(certificate), i)) = (\operatorname{upper}(\operatorname{envelope}(certificate))))) \land (\forall i, ((\operatorname{low}(certificate, i)) \neq (0)) \Rightarrow ((\operatorname{queryResidual}(feature, query, \operatorname{envelope}(certificate), i)) = (\operatorname{lower}(\operatorname{envelope}(certificate))))) \land (\forall j, ((\operatorname{coefficient}(\operatorname{envelope}(certificate), j)) \cdot (((\operatorname{linearObjective}((\lambda i \mapsto \operatorname{feature}(i, j)), \operatorname{high}(certificate))) - (\operatorname{linearObjective}((\lambda i \mapsto \operatorname{feature}(i, j)), \operatorname{low}(certificate)))))) = ((\lvert\operatorname{coefficient}(\operatorname{envelope}(certificate), j)\rvert) \cdot (\operatorname{tolerance}(j)))))$$

*Formalization.* `D5/S0/Certificates/RationalMomentAmbiguityCertificate.ValidContactCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The high support touches the upper residual level and the low support the lower level. Predictor slopes align with the signed moment discrepancies.

**Definition 1.9 (Finite rational checker).**

$$\forall n, d, feature, query, tolerance, certificate, (\operatorname{checkContactCertificate}(feature, query, tolerance, certificate)) = (\operatorname{decide}(\operatorname{ValidContactCertificate}(feature, query, tolerance, certificate)))$$

*Formalization.* `D5/S0/Certificates/RationalMomentAmbiguityCertificate.checkContactCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decides all probability, moment, envelope, contact and alignment conditions from the raw data.

**Theorem 1.10 (Acceptance reflection).**

$$\forall n, d, feature, query, tolerance, certificate, ((\operatorname{checkContactCertificate}(feature, query, tolerance, certificate)) = (true)) \Leftrightarrow (\operatorname{ValidContactCertificate}(feature, query, tolerance, certificate))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentAmbiguityCertificate.checkContactCertificate_eq_true_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Acceptance is equivalent to the displayed finite contract.

**Theorem 1.11 (Oriented gap attains the budget).**

$$\forall n, d, feature, query, tolerance, certificate, (\operatorname{ValidContactCertificate}(feature, query, tolerance, certificate)) \Rightarrow (((\operatorname{linearObjective}(query, \operatorname{high}(certificate))) - (\operatorname{linearObjective}(query, \operatorname{low}(certificate)))) = (\operatorname{residualBudget}(tolerance, \operatorname{envelope}(certificate))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentAmbiguityCertificate.contact_gap_eq_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Contact and alignment make every contribution to the primal-dual gap vanish.

**Definition 1.12 (Attainable query differences).**

$$\forall n, d, feature, query, tolerance, value, ((value) \in (\operatorname{ambiguityValues}(feature, query, tolerance))) \Leftrightarrow (\exists high, low, (\operatorname{MomentTolerancePair}(feature, tolerance, high, low)) \land ((value) = (\lvert(\operatorname{linearObjective}(query, high)) - (\operatorname{linearObjective}(query, low))\rvert)))$$

*Formalization.* `D5/S0/Certificates/RationalMomentAmbiguityCertificate.ambiguityValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both probability laws vary over the same finite carrier subject to the same tolerance vector.

**Definition 1.13 (All valid residual budgets).**

$$\forall n, d, feature, query, tolerance, value, ((value) \in (\operatorname{residualBudgetValues}(feature, query, tolerance))) \Leftrightarrow (\exists envelope, (\operatorname{GlobalQueryEnvelope}(feature, query, envelope)) \land ((value) = (\operatorname{residualBudget}(tolerance, envelope))))$$

*Formalization.* `D5/S0/Certificates/RationalMomentAmbiguityCertificate.residualBudgetValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predictor and envelope may vary, while the carrier, query, features and tolerances stay fixed.

**Theorem 1.14 (Attained maximum and attained minimum).**

$$\forall n, d, feature, query, tolerance, certificate, ((\operatorname{checkContactCertificate}(feature, query, tolerance, certificate)) = (true)) \Rightarrow ((\operatorname{IsGreatest}(\operatorname{ambiguityValues}(feature, query, tolerance), \operatorname{residualBudget}(tolerance, \operatorname{envelope}(certificate)))) \land (\operatorname{IsLeast}(\operatorname{residualBudgetValues}(feature, query, tolerance), \operatorname{residualBudget}(tolerance, \operatorname{envelope}(certificate)))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentAmbiguityCertificate.checkContactCertificate_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same accepted value is the largest feasible query difference and the least valid residual budget. No general certificate-discovery or certificate-existence theorem is claimed.

**Theorem 1.15 (Sparse optimal witnesses without another query coordinate).**

$$\forall n, d, feature, query, tolerance, certificate, high, low, highSteps, lowSteps, ((\operatorname{ValidContactCertificate}(feature, query, tolerance, certificate)) \land ((\operatorname{checkCompression}(feature, \operatorname{high}(certificate), highSteps)) = (\operatorname{some}(high))) \land ((\operatorname{checkCompression}(feature, \operatorname{low}(certificate), lowSteps)) = (\operatorname{some}(low)))) \Rightarrow ((\operatorname{ValidContactCertificate}(feature, query, tolerance, \{(high) = (high), (low) = (low), (envelope) = (\operatorname{envelope}(certificate))\})) \land ((\operatorname{card}(\operatorname{activeAtoms}(high))) \le ((d) + (1))) \land ((\operatorname{card}(\operatorname{activeAtoms}(low))) \le ((d) + (1))) \land (((\operatorname{linearObjective}(query, high)) - (\operatorname{linearObjective}(query, low))) = ((\operatorname{linearObjective}(query, \operatorname{high}(certificate))) - (\operatorname{linearObjective}(query, \operatorname{low}(certificate))))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/RationalMomentAmbiguityCertificate.contact_certificate_preserved_by_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

highSteps and lowSteps are lists of existing EliminationStep values. Separate support-monotone compression preserves the d feature moments, both residual contact levels and the signed alignment. Each endpoint has at most d+1 active atoms and the exact query gap is unchanged.

## References

- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.ContactCertificate`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.GlobalQueryEnvelope`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.MomentTolerancePair`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.ValidContactCertificate`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.ambiguityValues`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.checkContactCertificate`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.checkContactCertificate_eq_true_iff`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.checkContactCertificate_sound`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.contact_certificate_preserved_by_compression`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.contact_gap_eq_budget`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.momentToleranceCost`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.primal_dual_gap_identity`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.query_gap_le_residualBudget`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.residualBudget`
- Truth anchor: `D5/S0/Certificates/RationalMomentAmbiguityCertificate.residualBudgetValues`
- Dependency: [D5/S0/Certificates/RationalMomentQueryEnvelope](RationalMomentQueryEnvelope.md)
