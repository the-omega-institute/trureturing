# The weighted two-minor and three-minor inequality

## Abstract

The weighted two-minor and three-minor inequality

Let n be any natural number, let I=Fin(n), and let x,y,z be orthonormal vectors in the native real Euclidean space on I. For real coordinate vectors define pairMinor(x,y)(i,j)=x(i)y(j)-x(j)y(i). Define tripleMinor(x,y,z)(i,j,k) as the literal three-by-three determinant whose rows are x,y,z and whose columns are i,j,k. The sums below contain each increasing pair or triple once. The nested maximum is the maximum of exactly A(i,j), A(i,k), and A(j,k).

**Theorem 1.1 (Every positive symmetric real weight matrix satisfies the comparison).**

$$\forall n \in \mathbb{N},\; \forall x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \forall y \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \forall z \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \operatorname{Orthonormal}\left(\mathbb{R}, [x,y,z]\right) \Rightarrow \left(\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{A}\left(i, j\right) = \operatorname{A}\left(j, i\right)\right) \land \left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; 0 < \operatorname{A}\left(i, j\right)\right)\right) \Rightarrow \sum_{i,j\in \operatorname{Fin}\left(n\right),i < j} \operatorname{A}\left(i, j\right) \cdot (\operatorname{pairMinor}\left(x, y, i, j\right))^{2} \le \sum_{i,j,k\in \operatorname{Fin}\left(n\right),i < j,j < k} \operatorname{max}\left(\operatorname{A}\left(i, j\right), \operatorname{max}\left(\operatorname{A}\left(i, k\right), \operatorname{A}\left(j, k\right)\right)\right) \cdot (\operatorname{tripleMinor}\left(x, y, z, i, j, k\right))^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinors.weighted_minors` (`✓ std3`). ∎

*Resolves.* `Problems/mathoverflow-469781-weighted-orthogonal-minors` (proved) by `D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinors.weighted_minors`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mathoverflow-469781-weighted-orthogonal-minors","declaration_gid":"D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinors.weighted_minors","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* meler (MathOverflow user 526848; real name unverified) (2024). *Inequality involving minors of an orthogonal matrix*. URL: <https://mathoverflow.net/questions/469781>.

*Commentary.*

Orthonormal means all three vectors have norm one and every two distinct vectors have inner product zero. The theorem applies to every such triple for every n at least three. The coordinate proof only requires the unit norm of z and its orthogonality to x and y; native Euclidean inner-product and squared-norm formulas discharge these conditions from orthonormality. No positive definiteness, distance condition, nonzero-minor premise, rational-weight restriction, or dimension cutoff is used.

The finite-array proof sums over all ordered tuples. Skew(v) means v(i,j)=-v(j,i). Alt(b) means b(j,i,k)=-b(i,j,k) and b(k,i,j)=b(i,j,k). The actual maps are lift(z,v)(i,j,k)=z(i)v(j,k)-z(j)v(i,k)+z(k)v(i,j), lower(z,b)(i,j)=sum over k of z(k)b(k,i,j), and contract(z,v)(i)=sum over k of z(k)v(k,i). Pair mass is one half of the full squared-coordinate sum; triple mass is one sixth of its full squared-coordinate sum.

Finite sum interchange gives the adjoint identity with factor three. Expansion of lower composed with lift and skew symmetry give massThree(lift(z,v))+sum over i of contract(z,v)(i) squared=(sum over k of z(k) squared)massTwo(v). Finite squared Cauchy-Schwarz then bounds massTwo(lower(z,b)) by massThree(b) when z is unit. The zero contracted-mass case is treated separately; no minor is divided by.

The pinned determinant expansion proves tripleMinor=lift(z,pairMinor), and the two orthogonality equations prove lower(z,tripleMinor)=pairMinor. For every symmetric pair family F, retain its pair coordinates and exactly the triples containing a pair in F. The contraction at a retained pair only sees retained triples. Projection discards nonnegative squares, proving domination for every family, including empty and full families.

An exact finite threshold expansion represents every nonnegative real value in a finite set as a sum of nonnegative coefficients times indicators of upper level sets. Induction on the maximum constructs the coefficients. Apply the family inequality at every threshold and interchange finite sums. The union condition on the three edges is exactly the upper level condition for the displayed maximum. Equal weights share the same value, so ties and zero minors require no perturbation or approximation.

Symmetric pair summands occur twice in the full ordered sum. Symmetric triple summands that vanish on repeated indices occur six times. Explicit minimum-index partition and sorting of the other two indices prove these factors; cancellation gives the increasing-index statement. All inequalities are non-strict, including n=3 and equality cases.

The external question is meler, Inequality involving minors of an orthogonal matrix, MathOverflow 469781, revision F53D06CE-3805-43B9-9FEB-43A79F67F7AB, CC-BY-SA 4.0, also Math StackExchange 4902019. The coordinate proof is a repository synthesis. It directly uses pinned Mathlib squared finite Cauchy-Schwarz and determinant expansions, and assumes no coupling, Hall inequality, exterior norm estimate, or probability normalization.

## References

- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinors.weighted_minors`
