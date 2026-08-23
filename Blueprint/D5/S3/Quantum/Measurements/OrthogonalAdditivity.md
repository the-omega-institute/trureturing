# Orthogonal Additivity

## Abstract

A normal positive state is additive on a complete orthogonal projection family.

**Theorem 1.1 (Normal-state additivity and pure-state Parseval decomposition).**

$$\begin{gathered}\forall A: \operatorname{Type}, H: \operatorname{Type},\\{}[\operatorname{CStarAlgebra}(A)], [\operatorname{PartialOrder}(A)], [\operatorname{StarOrderedRing}(A)],\\{}[\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)],\\{}P: Nat\to A,\\{}pi: \operatorname{StarAlgHom}(\mathbb{C}, A, \operatorname{ContinuousLinearEnd}(\mathbb{C}, H)), omega: \operatorname{PositiveLinearMap}(\mathbb{C}, A, \mathbb{C}),\\{}[\forall i, \operatorname{IsStarProjection}(P_{i})],\\{}[\forall i, j, i\neq j\Rightarrow P_{i} \times P_{j}=0],\\{}[\forall psi, \sum_{i} pi(P_{i})(psi)=psi],\\{}[omega(1)=1],\\{}[\operatorname{SequentiallyNormal}(pi, omega)]\Rightarrow [\sum_{i} omega(P_{i})=1 \land \forall psi, \sum_{i} \left\lVert pi(P_{i})(psi) \right\rVert^{2}=\left\lVert psi \right\rVert^{2}].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/OrthogonalAdditivity.orthogonal_additivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a unital complex C-star algebra represented on a complete complex inner-product space H. The family is a countable sequence of star projections in A, pairwise orthogonal, whose represented strong operator sum is the identity in pointwise form.

The state is a positive linear functional normalized at the identity. Sequential normality is stated publicly as continuity along every monotone sequence with a strong pointwise limit.

The theorem concludes both source clauses: the real state weights have sum one, and every vector has the pure-state Parseval sum of squared projection norms. A finite family is represented by zero extension of its sequence, while the displayed theorem handles the countable case directly.

Pinned Mathlib supplies positivity of star projections, monotone operator partial sums, HasSum transport through continuous linear maps, and the inner-product norm identity. Repository and pinned-library searches found no theorem packaging the normal-state and Parseval clauses together.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/OrthogonalAdditivity.orthogonal_additivity`
