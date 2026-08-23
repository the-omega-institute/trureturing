# Symmetric Tie Impossibility

## Abstract

Anonymous and candidate-neutral deterministic choice cannot resolve a two-voter tie.

**Theorem 1.1 (No anonymous neutral deterministic tie rule).**

$$\neg \left(\exists F \in \operatorname{Prod}\left(Bool, Bool\right) \to Bool,\; \left(\forall p \in \operatorname{Prod}\left(Bool, Bool\right),\; F\left((p_{2}, p_{1})\right) = F\left(p\right)\right) \land \left(\forall p \in \operatorname{Prod}\left(Bool, Bool\right),\; F\left((\operatorname{not}\left(p_{1}\right), \operatorname{not}\left(p_{2}\right))\right) = \operatorname{not}\left(F\left(p\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Aggregation/SymmetricTieImpossibility.symmetric_tie_impossibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Candidates are the exact two-element Boolean carrier and profiles are ordered pairs of two voter choices. A rule of type Bool times Bool to Bool is publicly total, single-valued, and always selects one of the two candidates, which is deterministic completeness.

Anonymity says exchanging the two profile coordinates leaves the result unchanged. Candidate neutrality says complementing both choices complements the selected candidate.

At the tied profile (false, true), candidate exchange produces exactly the voter-exchanged profile (true, false). The two symmetry laws therefore force the selected Boolean value to equal its own complement, contradicting Mathlib's exact Bool.not_ne_self lemma.

The carrier and both exchanges occur directly in the public statement; no source object is defined from the desired contradiction. Separate compiling witnesses show that each symmetry law alone is satisfiable by a total deterministic rule.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/SymmetricTieImpossibility.symmetric_tie_impossibility`
