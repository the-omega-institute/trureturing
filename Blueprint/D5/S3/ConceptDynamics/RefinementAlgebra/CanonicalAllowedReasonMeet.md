# Canonical Allowed Reason Meet

## Abstract

Meet closure gives a canonical unique coarsest allowed sufficient reason.

**Theorem 1.1 (Meet closure gives the unique coarsest ratio).**

$$\begin{gathered}\forall X: \operatorname{Type},\\{}\mathcal{E}: \mathcal{P}(\operatorname{ConceptClass}(X)), J: \operatorname{ConceptClass}(X),\\{}\operatorname{Nonempty}(\{R \in \operatorname{ConceptClass}(X) \mid R \in \mathcal{E} \land J \leq R\}) \land (\operatorname{Nonempty}(\{R \in \operatorname{ConceptClass}(X) \mid R \in \mathcal{E} \land J \leq R\}) \Rightarrow \operatorname{symmApply}(\operatorname{conceptKernelOrderIso}(X), \operatorname{sInf}(\operatorname{image}(\operatorname{conceptKernelOrderIso}(X), \{R \in \operatorname{ConceptClass}(X) \mid R \in \mathcal{E} \land J \leq R\}))) \in \mathcal{E})\\{}\Rightarrow \operatorname{IsLeast}(\{R \in \operatorname{ConceptClass}(X) \mid R \in \mathcal{E} \land J \leq R\}, \operatorname{symmApply}(\operatorname{conceptKernelOrderIso}(X), \operatorname{sInf}(\operatorname{image}(\operatorname{conceptKernelOrderIso}(X), \{R \in \operatorname{ConceptClass}(X) \mid R \in \mathcal{E} \land J \leq R\})))) \land\\{}\exists! R: \operatorname{ConceptClass}(X), \operatorname{IsLeast}(\{R \in \operatorname{ConceptClass}(X) \mid R \in \mathcal{E} \land J \leq R\}, R).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementAlgebra/CanonicalAllowedReasonMeet.meet_closed_allowed_reasons_have_unique_coarsest_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the repository's canonical class of effective concept readouts modulo mutual refinement. The frozen kernel order isomorphism identifies this carrier with the order dual of the complete lattice of equivalence relations.

Acceptable reasons are exactly the allowed concept classes above the judgment essence. Their meet is constructed by taking the infimum after the kernel-order encoding and transporting it back through the inverse isomorphism.

The two displayed premises are the source's existence condition and closure of the allowed doctrine under this relevant nonempty meet. The conclusion exposes both leastness of the canonical meet and unique existence of a least acceptable reason.

The source's closing sentence about legal language is an interpretation of this leastness result, not a separately defined predicate. No additional legal-language vocabulary is introduced.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementAlgebra/CanonicalAllowedReasonMeet.meet_closed_allowed_reasons_have_unique_coarsest_ratio`
- Dependency: [D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality](../Refinement/ConceptKernelOrderDuality.md)
