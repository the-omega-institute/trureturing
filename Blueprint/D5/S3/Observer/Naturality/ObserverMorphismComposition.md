# Observer Morphism Composition

## Abstract

Evaluation-preserving observer morphisms compose in the state and protocol directions.

**Theorem 1.1 (Observer morphism composition).**

$$\begin{gathered}\forall X_{1}, X_{2}, X_{3}, P_{1}, P_{2}, P_{3}, Law: Type,\\\forall e_{1}: X_{1} \to \left(P_{1} \to Law\right), e_{2}: X_{2} \to \left(P_{2} \to Law\right), e_{3}: X_{3} \to \left(P_{3} \to Law\right),\\\forall f_{1}: X_{1} \to X_{2}, g_{1}: P_{2} \to P_{1}, f_{2}: X_{2} \to X_{3}, g_{2}: P_{3} \to P_{2},\\(\forall x \in X_{1}, \forall p \in P_{2},\ e_{2}(f_{1}(x), p) = e_{1}(x, g_{1}(p))) \land (\forall x \in X_{2}, \forall p \in P_{3},\ e_{3}(f_{2}(x), p) = e_{2}(x, g_{2}(p))) \Rightarrow\\\forall x \in X_{1}, \forall p \in P_{3},\ e_{3}((f_{2} \circ f_{1})(x), p) = e_{1}(x, (g_{1} \circ g_{2})(p)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Naturality/ObserverMorphismComposition.observer_morphism_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three observers share one law carrier. Each observer has its own state and protocol carriers and an evaluation map into that law carrier.

The first morphism translates states from the first observer to the second and compiles protocols in the reverse direction. The second morphism does the same from the second observer to the third. Both pairs preserve evaluation.

Their state maps compose forward, while their protocol maps compose in the opposite order. Substituting the two preservation equalities proves that this composite pair again preserves evaluation.

Repository searches found no canonical observer-morphism structure or exact theorem to reuse. The proof applies the pinned library's function-composition computation rule and the two stated premises.

## References

- Truth anchor: `D5/S3/Observer/Naturality/ObserverMorphismComposition.observer_morphism_composition`
