# Inductive Sufficiency

## Abstract

A finite history determines a prediction exactly when the prediction factors through its image.

**Theorem 1.1 (Finite-history factorization is the inductive sufficiency criterion).**

$$\begin{gathered}\forall X, H, Y: \operatorname{Type},\\h: X \to H, K: X \to Y,\\(\operatorname{FactorsThrough}(K, h) \Leftrightarrow \operatorname{Refines}(K, \operatorname{rangeFactorization}(h))) \land\\(\neg\operatorname{Refines}(K, \operatorname{rangeFactorization}(h)) \Leftrightarrow \exists x, y: X, h(x) = h(y) \land K(x) \neq K(y)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/InductiveSufficiency.inductive_sufficiency_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h map source states to their realized finite histories and let K be a future prediction. The repository relation Refines K (rangeFactorization h) says exactly that there is a map Kbar from the realized image of h to predictions such that K equals Kbar after the canonical range factorization. The theorem identifies this image factorization with constancy of K on every fiber of h.

The negated criterion is included in the theorem rather than left as prose. Failure of factorization is equivalent to the existence of two source states x and y with the same finite history and different predictions. Thus repeated past data alone does not force repeated future behavior; the displayed descent condition is the explicit premise that does.

This statement covers the source's factorization equivalence, its image-valued factor Kbar, the same-history/different-prediction witness, and both clauses of the final Hume display. The listed examples of additional premises (finite-state stability, stationarity, Markov completion, analyticity, causal closure, a complexity bound, and mechanism invariance) are not separate formal claims because the source gives them no definitions; they remain explanatory examples of conditions that could establish descent.

The repository supplies the exact ConceptDynamics.Refines relation. Pinned Mathlib supplies the exact Function.FactorsThrough predicate and the image-valued Set.rangeFactorization map; all are reused directly. Repository and pinned-source searches found no single theorem combining the image factorization equivalence with the explicit failure witnesses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Refinement/InductiveSufficiency.inductive_sufficiency_criterion`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
