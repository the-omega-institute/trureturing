# Compact Residual Finite Completion

## Abstract

Compact open separation of a residual space is witnessed by a finite zero-spectrum budget.

**Theorem 1.1 (Compact residual separation has a finite zero-spectrum settlement).**

$$\begin{aligned}\forall I, X, C, Y: \operatorname{Type},\\V: I \to \operatorname{Type}, \Gamma: \operatorname{Set}\left(I\right),\\{}[\operatorname{TopologicalSpace}\left(X \times X\right)],\\d: \forall i: I, \operatorname{Concept}\left(X, \operatorname{V}\left(i\right)\right),\\q: \operatorname{Concept}\left(X, C\right), T: \operatorname{Concept}\left(X, Y\right),\\c: I \to \mathbb{R}, \nu: \operatorname{EscapeWeight}\left(X \times X\right),\\\operatorname{let} E = \operatorname{defectRelation}\left(q, T\right), K_{a} = \operatorname{conceptKernel}\left((d_{i})_{i \in \Gamma}, a\right),\\U_{a} = \{e: E \mid \neg(e \in K_{a})\},\\\operatorname{IsCompact}\left(E\right) \land\\\operatorname{intersection}\left(E, \operatorname{jointKernel}\left((d_{i})_{i \in \Gamma}\right)\right) = \emptyset \land\\(\forall a \in \Gamma, \operatorname{IsOpen}\left(U_{a}\right)) \land\\(\forall i \in \Gamma, 0 \leq \operatorname{c}\left(i\right)) \Rightarrow\\\exists S: \operatorname{Finset}\left(\Gamma\right), L: \mathbb{R}_{\geq0},\\L = \operatorname{finiteSelectionCost}\left(\Gamma, c, S\right) \land\\\operatorname{defectRelation}\left(\operatorname{conceptJoin}\left(q, \operatorname{finiteSelectionSupplement}\left(\Gamma, d, S\right)\right), T\right) = \emptyset \land\\\operatorname{finiteEscapeSpectrum}\left(\Gamma, d, q, T, c, \nu, L\right) = 0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EscapeSpectrum/CompactResidualFiniteCompletion.compact_residual_finite_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residual E is the canonical defectRelation of the baseline readout q against the target T. For each active definition, its cut U is represented as an open subset of the subtype E, so the openness premise is exactly relative openness.

Blind-kernel emptiness invokes the existing finite_cover_laws equivalence to obtain a cover of E. Compactness then extracts a Finset S of the active-definition subtype Gamma.

Nonnegative candidate costs make the exact sum C(S) an NNReal budget L. The selected supplement has empty target defect, so its residual mass is zero and the canonical finiteEscapeSpectrum at L is zero.

No continuity of the definitions, analytic compactness, positive baseline mass, optimizer, or infimum-attainment claim is used.

## References

- Truth anchor: `D5/S3/ConceptDynamics/EscapeSpectrum/CompactResidualFiniteCompletion.compact_residual_finite_completion`
- Dependency: [D5/S3/ConceptDynamics/EscapeSpectrum/BudgetEnvelopeCompletion](BudgetEnvelopeCompletion.md)
