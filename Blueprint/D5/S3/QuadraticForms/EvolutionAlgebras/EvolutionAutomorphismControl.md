# Algebra automorphisms and the canonical support quotient

## Abstract

The full multiplication-preserving linear group of a perfect evolution product is finite and obeys a joint successor-quotient bound.

For the coordinate estimates the space is Coord(n)=Fin(n) to the complex numbers. The multiplication is a bilinear map, with no associativity or unit assumption. NaturalBasisAt(mu,b) means mu(b(i),b(j))=0 whenever i differs from j. Perfectness means all pair products span the coordinate space. The support relation has an arrow i to j exactly when the j-coordinate of mu(b(i),b(i)) in b is nonzero; loops are retained.

**Definition 1.1 (All multiplication automorphisms).**

$$\forall A \in Typeu,\; \operatorname{ComplexVectorSpace}\left(A\right) \Rightarrow \left(\forall mu \in \operatorname{BilinearProduct}\left(A\right),\; \operatorname{Aut}\left(mu\right) = \operatorname{MultiplicationPreservingLinearEquivs}\left(mu\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.Aut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Aut(mu) is the subgroup of all invertible complex-linear maps f with f(mu(x,y))=mu(f(x),f(y)) for every pair x,y. Membership assumes neither monomiality nor graph data nor finiteness.

**Definition 1.2 (The actual support permutation homomorphism).**

$$\forall n \in \operatorname{NaturalNumbers}\left(\right),\; \forall mu \in \operatorname{Product}\left(n\right),\; \forall b \in \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), \operatorname{Complex}\left(\right), \operatorname{Coord}\left(n\right)\right),\; \operatorname{NaturalBasisAt}\left(mu, b\right) \Rightarrow \left(\operatorname{perfect}\left(mu\right) \Rightarrow \operatorname{MonoidHom}\left(\operatorname{Aut}\left(mu\right), \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.rho` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Square-vector independence follows from perfectness and the original natural_basis_structure_map. For distinct basis vectors, their image product is zero. Injectivity of that structure map forces every matrix row to contain at most one nonzero entry. Invertibility supplies exactly one in every row and column. Thus each actual automorphism has a unique basis-image permutation. Comparing coefficients shows that this permutation preserves support, and uniqueness makes rho multiplicative. Monomiality is a credited supporting result from the survey, consumed here to build the full group bound.

**Definition 1.3 (The exact diagonal kernel).**

$$\forall n \in \operatorname{NaturalNumbers}\left(\right),\; \forall mu \in \operatorname{Product}\left(n\right),\; \forall b \in \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), \operatorname{Complex}\left(\right), \operatorname{Coord}\left(n\right)\right),\; \operatorname{NaturalBasisAt}\left(mu, b\right) \Rightarrow \left(\operatorname{perfect}\left(mu\right) \Rightarrow \operatorname{Equiv}\left(\operatorname{ker}\left(\operatorname{rho}\left(mu, b\right)\right), \operatorname{Assignments}\left(\operatorname{supportRelation}\left(mu, b\right), UnitSquaring\right)\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.kernelAssignmentEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

UnitSquaring is z mapped to z squared on the nonzero complex units. The kernel consists exactly of diagonal automorphisms with t(j)=t(i)^2 on every support arrow. The forward map uses the actual kernel; the inverse constructs an invertible diagonal linear map and proves multiplication preservation from these equations on basis pairs. Thus every assignment is realized, without assuming that arbitrary graph automorphisms lift.

**Theorem 1.4 (The exact diagonal cycle cardinality).**

$$\forall n \in \operatorname{NaturalNumbers}\left(\right),\; \forall mu \in \operatorname{Product}\left(n\right),\; \forall b \in \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), \operatorname{Complex}\left(\right), \operatorname{Coord}\left(n\right)\right),\; \operatorname{NaturalBasisAt}\left(mu, b\right) \Rightarrow \left(\operatorname{perfect}\left(mu\right) \Rightarrow \operatorname{card}\left(\operatorname{ker}\left(\operatorname{rho}\left(mu, b\right)\right)\right) = \operatorname{cycleWeight}\left(\operatorname{beta}\left(\operatorname{supportRelation}\left(mu, b\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.diagonal_kernel_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire diagonal kernel is equivalent to the support-arrow assignments, which descend bijectively to the least quotient. Evaluation and independent realization identify its assignments with one roots-of-unity group per successor cycle. Consequently its cardinality equals cycleWeight(beta), including the neutral singleton factors.

**Theorem 1.5 (Actual finiteness).**

$$\forall n \in \operatorname{NaturalNumbers}\left(\right),\; \forall mu \in \operatorname{Product}\left(n\right),\; \forall b \in \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), \operatorname{Complex}\left(\right), \operatorname{Coord}\left(n\right)\right),\; \operatorname{NaturalBasisAt}\left(mu, b\right) \Rightarrow \left(\operatorname{perfect}\left(mu\right) \Rightarrow \operatorname{Finite}\left(\operatorname{Aut}\left(mu\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.automorphism_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Perfectness gives positive in- and outdegree. Diagonal assignments descend exactly through the least admissible support quotient. Its successor beta is a finite permutation; a common return time puts every coordinate in a finite roots-of-unity group. The permutation kernel and image are finite, hence so is the original algebra group. Natural cardinality is used only after this step.

**Theorem 1.6 (The joint algebraic quotient bound).**

$$\forall n \in \operatorname{NaturalNumbers}\left(\right),\; \forall mu \in \operatorname{Product}\left(n\right),\; \forall b \in \operatorname{Basis}\left(\operatorname{Fin}\left(n\right), \operatorname{Complex}\left(\right), \operatorname{Coord}\left(n\right)\right),\; \operatorname{NaturalBasisAt}\left(mu, b\right) \Rightarrow \left(\operatorname{perfect}\left(mu\right) \Rightarrow \operatorname{card}\left(\operatorname{Aut}\left(mu\right)\right) \le \operatorname{cycleWeight}\left(\operatorname{beta}\left(\operatorname{supportRelation}\left(mu, b\right)\right)\right) \cdot \operatorname{card}\left(\operatorname{centralizer}\left(\operatorname{beta}\left(\operatorname{supportRelation}\left(mu, b\right)\right)\right)\right) \cdot \operatorname{BlockFactorialProduct}\left(\operatorname{supportRelation}\left(mu, b\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.automorphism_quotient_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be Blocks(R), beta its successor, and Fiber(R,q) the actual vertices in class q. BlockFactorialProduct is the product over q in P of factorial(card(Fiber(R,q))). The centralizer is taken in the symmetric group on P. cycleWeight(beta) is the product of 2^l-1 over all its cycles, including the factor one on fixed points. These cycles partition P, whose size can be smaller than n. The actual algebra group maps into the support automorphism group. Both the diagonal-root bound and the quotient-action bound apply to that same group. The block-action kernel is retained through its injection into the product of the actual block symmetric groups. No faithful quotient action or support-surjectivity assumption is made.

This coordinate theorem is the algebraic core of the arbitrary-module bound toward Conjecture 3 of Kaygorodov, Martín González and Viruel, arXiv:2610.22248v1. It establishes a joint upper bound, not the sharp all-dimensional maximum. The universal partition estimate, six small values, factorial tail, cycle-family attainment and final maximum assembly remain separate statements. EvolutionBasisTransport conjugates the entire group on an arbitrary complex module to this coordinate model. The diagonal root count is an equality: cycle evaluation has an independently constructed inverse.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.Aut`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.automorphism_finite`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.automorphism_quotient_bound`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.diagonal_kernel_card`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.kernelAssignmentEquiv`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionAutomorphismControl.rho`
- Dependency: [D5/S3/FiniteGroups/SuccessorPowerAssignments](../../FiniteGroups/SuccessorPowerAssignments.md)
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionLowerBound](HuEvolutionLowerBound.md)
