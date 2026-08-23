# Information Refinement Shrinks Answers

## Abstract

Information refinement can only shrink the set of possible answers, can do so strictly, and is ruled out by the appearance of a new answer.

**Theorem 1.1 (Information refinement cannot enlarge possible answers).**

$$\forall World \in \operatorname{Type}, Answer \in \operatorname{Type}, T \in World \to Answer, R \in \operatorname{Set}\left(World\right), S \in \operatorname{Set}\left(World\right),\; R \subseteq S \Rightarrow \operatorname{Ans}\left(T, R\right) \subseteq \operatorname{Ans}\left(T, S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/InformationRefinementShrinksAnswers.answer_set_antitone_in_information` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A possible answer is the image under T of at least one world that remains compatible with the available information. If every world in the refined set R already belongs to S, the same world witnesses that answer before refinement.

Thus removing possible worlds cannot create an answer outside the former image. The answer-set construction is covariant in sets of worlds, which makes it antitone when greater information is represented by a smaller set of possibilities.

**Lemma 1.2 (Boolean refinement shrinks possible answers strictly).**

$$\left\{true\right\} \subset \operatorname{univ}\left(Bool\right) \land \operatorname{Ans}\left(id, \left\{true\right\}\right) \subset \operatorname{Ans}\left(id, \operatorname{univ}\left(Bool\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/InformationRefinementShrinksAnswers.strict_refinement_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under complete ignorance, both Boolean worlds remain possible and the identity readout can return either truth value. Learning that the world is true leaves only the singleton containing true.

The refinement is proper because it excludes false, and its answer image is proper for the same reason: false was formerly possible as an answer but is no longer attained.

**Lemma 1.3 (Answer growth rules out information refinement).**

$$\forall World \in \operatorname{Type}, Answer \in \operatorname{Type}, T \in World \to Answer, R \in \operatorname{Set}\left(World\right), S \in \operatorname{Set}\left(World\right),\; \left(\neg \operatorname{Ans}\left(T, R\right) \subseteq \operatorname{Ans}\left(T, S\right)\right) \Rightarrow \left(\neg R \subseteq S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Answering/InformationRefinementShrinksAnswers.answer_growth_precludes_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the new possible-world set admits an answer that the old set did not. The new set cannot have been obtained solely by removing old possibilities.

Indeed, containment of the new worlds in the old worlds would invoke answer-set antitonicity and contain the new answer image in the old one, contradicting the observed answer growth.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Answering/InformationRefinementShrinksAnswers.answer_growth_precludes_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/InformationRefinementShrinksAnswers.answer_set_antitone_in_information`
- Truth anchor: `D5/S3/ConceptDynamics/Answering/InformationRefinementShrinksAnswers.strict_refinement_witness`
