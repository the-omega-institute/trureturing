# Finite Reverse Criterion

## Abstract

Empty carry yields a unique descent on the effective image.

**Theorem 1.1 (Empty carry determines the effective-image descent).**

$$\forall X, Y, B_{C}, B_{D}: \operatorname{Type},\ [\operatorname{Fintype}(X)], [\operatorname{DecidableEq}(X)], [\operatorname{Fintype}(B_{C})], [\operatorname{DecidableEq}(B_{C})], [\operatorname{Fintype}(B_{D})], [\operatorname{DecidableEq}(B_{D})],\ F: X \to Y, q_{C}: X \to B_{C}, q_{D}: Y \to B_{D},\ \operatorname{IsEmpty}\left(\operatorname{Carry}(F, q_{C}, q_{D})\right) \Rightarrow\ \exists! \overline{F}: \operatorname{range}(q_{C}) \to B_{D},\ \forall x: X, \overline{F}(\operatorname{rangeFactorization}(q_{C}, x)) = q_{D}(F(x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/FiniteReverseCriterion.finite_reverse_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X, B_C, and B_D be finite types with decidable equality, let F map X to a process codomain Y, and let q_C and q_D be the current and future readouts. Carry consists exactly of pairs identified by q_C whose future readouts after F differ.

If the carry type is empty, there is a unique map from the realized range of q_C to B_D. On every source state, this map sends its effective current value to q_D(F(x)), so the image-restricted process/readout square commutes.

Pinned Mathlib supplies the canonical Set.rangeFactorization and Set.rangeSplitting maps used by the proof. Empty carry makes the chosen representative irrelevant, while every range element's source witness proves uniqueness. Repository and pinned-library searches found no existing theorem packaging these facts.

This formalizes exactly theorem/13.2 of formal-concept-dynamics, atom generic-residual-88ab11467c06c97a9dd12a0627951364cfe0c6a897813bf9209fc113283a304e. No claim about infinite constructive models or the neighboring quantitative defect is included.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/FiniteReverseCriterion.finite_reverse_criterion`
