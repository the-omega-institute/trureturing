# Blind Residual Charge Decomposition

## Abstract

Every finite selected residual decomposes into its blind and finitely removable charge.

**Theorem 1.1 (Finite residual charge splits around the common blind kernel).**

$$\begin{aligned}\forall I, X, C, Y: \operatorname{Type},\\V: I \to \operatorname{Type}, \Gamma: \operatorname{Set}\left(I\right),\\d: \forall i: I, \operatorname{Concept}\left(X, V(i)\right),\\q: \operatorname{Concept}\left(X, C\right), T: \operatorname{Concept}\left(X, Y\right),\\c: I \to \mathbb{R}, L: \operatorname{NNReal},\\S: \operatorname{Finset}\left(\Gamma\right), A: \operatorname{Set}\left(\operatorname{Set}\left(X \times X\right)\right),\\hA: \operatorname{IsSetRing}\left(A\right), \nu: \operatorname{AddContent}\left(\operatorname{NNReal}, A\right),\\\operatorname{Countable}\left(\Gamma\right) \land (\forall i \in \Gamma, 0 < c(i)) \land\\0 \leq \operatorname{coeReal}\left(L\right) \land 0 < \nu(\operatorname{defectRelation}\left(q, T\right)) \land\\\operatorname{let} E = \operatorname{defectRelation}\left(q, T\right), B = \operatorname{intersection}\left(E, \operatorname{jointKernel}\left((d_{i})_{i \in \Gamma}\right)\right),\\U_{a} = \operatorname{intersection}\left(E, \operatorname{complement}\left(\operatorname{conceptKernel}\left((d_{i})_{i \in \Gamma}, a\right)\right)\right), E_{S} = \operatorname{defectRelation}\left(\operatorname{conceptJoin}\left(q, \operatorname{finiteSelectionSupplement}\left(\Gamma, d, S\right)\right), T\right),\\E \in A \land B \in A \land\\(\forall a \in \Gamma, U_{a} \in A) \Rightarrow\\B = E \setminus \operatorname{iUnion}\left(a \in \Gamma, U_{a}\right) \land\\E_{S} = E \setminus \operatorname{iUnion}\left(a \in S, U_{a}\right) \land\\B \subseteq E_{S} \land\\E_{S} \in A \land \nu(B) \leq \nu(E_{S}) \land\\\nu(E_{S}) = \nu(B) + \nu(E_{S} \setminus B) \land\\(\Gamma = \emptyset \Rightarrow E_{S} = E).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EscapeSpectrum/BlindResidualChargeDecomposition.blind_residual_charge_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The baseline residual E is the canonical defectRelation. Each single-definition cut U and the blind residual B use the existing conceptKernel and dependent jointKernel; the finite residual E_S uses the canonical finiteSelectionSupplement.

The theorem first proves that B is exactly E outside the union of all language cuts. Agreement on every language coordinate then shows that B survives every finite selection S.

An AddContent with NNReal values on an arbitrary IsSetRing supplies finite additivity and monotonicity on the stated algebra. The residual, blind residual, and every single-definition cut are explicitly required to belong to that algebra.

The countable language, positive candidate costs, nonnegative budget, and positive baseline charge retain the source domain even though the local decomposition does not consume their numerical values. When Gamma is empty, the selected residual is the baseline residual; counting charge on a nonempty Boolean residual compiles all premises.

## References

- Truth anchor: `D5/S3/ConceptDynamics/EscapeSpectrum/BlindResidualChargeDecomposition.blind_residual_charge_decomposition`
- Dependency: [D5/S3/ConceptDynamics/EscapeSpectrum/BudgetEnvelopeCompletion](BudgetEnvelopeCompletion.md)
