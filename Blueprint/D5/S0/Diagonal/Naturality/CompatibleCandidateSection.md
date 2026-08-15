# Compatible Sections of Finite Candidate Systems

## Abstract

Nonempty finite candidate subsets preserved by a cofiltered diagram admit a compatible section.

**Theorem 1.1 (Cofiltered finite candidates admit a compatible section).**

$$\forall J: \operatorname{Type},\ [\operatorname{Category}(J)] [\operatorname{IsCofiltered}(J)],\ \forall D: \operatorname{Functor}(J, \operatorname{Type}),\ O: \forall i: J, \operatorname{Set}(D(i)),\ (\forall i, j: J, f: \operatorname{Hom}(i, j), x: D(i),\ x \in O(i) \Rightarrow D(f)(x) \in O(j)) \Rightarrow (\forall i: J, \operatorname{Finite}(O(i))) \Rightarrow (\forall i: J, \operatorname{Nonempty}(O(i))) \Rightarrow \operatorname{Nonempty}(\operatorname{CandidateSection}(D, O)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Naturality/CompatibleCandidateSection.compatible_candidate_section_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a cofiltered category, D a diagram of types indexed by J, and O assign a candidate subset of D(i) to every object i. Assume every candidate subtype O(i) is finite and nonempty.

Assume each diagram transition from i to j sends every member of O(i) into O(j). The restricted candidate subtypes form their own diagram. A section of that diagram supplies a candidate at every index, proves membership pointwise, and makes all transitions compatible.

Pinned Mathlib, Loogle, and LeanSearch all returned nonempty_sections_of_finite_cofiltered_system as the exact general section-existence result. The Lean proof imports and applies that theorem to the restricted candidate diagram; repository searches found no existing declaration of the full candidate-subset statement.

## References

- Truth anchor: `D5/S0/Diagonal/Naturality/CompatibleCandidateSection.compatible_candidate_section_nonempty`
