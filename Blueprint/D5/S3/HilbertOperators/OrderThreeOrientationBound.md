# Orientation bound for commuting orthogonal operators of order dividing three

## Abstract

The total squared operator-norm commutator defect of an orientation-reversing orthogonal operator is at least three when the common commutant of the order-three orthogonal operators has nonnegative determinant.

**Definition 1.1 (Operator-norm commutator defect).**

Lean statement: `D5/S3/HilbertOperators/OrderThreeOrientationBound.commutatorNorm`

*Formalization.* `D5/S3/HilbertOperators/OrderThreeOrientationBound.commutatorNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defect at index j is the operator norm of the difference between composing A after T at j and composing T at j after A.

**Theorem 1.2 (Squared defect bound for negative determinant).**

Lean statement: `D5/S3/HilbertOperators/OrderThreeOrientationBound.sum_sq_commutatorNorm_ge_three`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/OrderThreeOrientationBound.sum_sq_commutatorNorm_ge_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a finite-dimensional real inner-product space and S a finite set of indices. The continuous real-linear endomorphisms T at indices in S preserve norms, cube to the identity and commute pairwise. The continuous real-linear endomorphism U preserves norms and has negative determinant. Assume every continuous real-linear endomorphism that commutes with all the selected T has nonnegative determinant. Then the sum over S of the squared operator-norm defects of U is at least three.

Conjugation by one of the selected maps cyclically permutes three operator values. Averaging the three is a contraction and commutes with each of the other conjugations. At each point of the determinant-preserving segment, let s range from zero to one and take weights one minus two s over three, s over three and s over three.

The squared norm of the weighted average of three vectors is the weighted mean of their squared norms minus the sum of the squared pairwise distances weighted by the products of their two weights. Those products sum to (2s minus s squared) over three, which is at most one third. Each of the three distances for one conjugation is at most its current defect times the norm of the vector. Averaging by the other conjugations can only decrease that defect.

If the total squared defect were below three, the pointwise squared norm of every intermediate operator would be bounded below by a positive multiple of the input squared norm. Its determinant could never vanish. Continuity would then carry the negative sign to a commuting operator, contradicting the assumed sign of its determinant.

**Definition 1.3 (Real operator on character planes).**

Lean statement: `D5/S3/HilbertOperators/OrderThreeOrientationBound.characterPlane`

*Formalization.* `D5/S3/HilbertOperators/OrderThreeOrientationBound.characterPlane` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The underlying real space of finite-dimensional complex Euclidean space is an orthogonal sum of real planes. Given one complex number per coordinate, the operator acts on each coordinate by multiplication by that number.

**Theorem 1.4 (Orientation bound on conjugate character planes).**

Lean statement: `D5/S3/HilbertOperators/OrderThreeOrientationBound.characterPlane_commutator_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/OrderThreeOrientationBound.characterPlane_commutator_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite set S of generator indices and a finite set of plane labels. The generator at j multiplies coordinate k by a cube root of unity w(j,k). For every ordered pair of planes i,k, including i equal to k, some selected generator has w(j,i) different from the complex conjugate of w(j,k). Then every orthogonal U of negative real determinant has squared defect sum at least three, and some selected defect is at least the square root of three divided by the number of selected generators inside the radical.

If A commutes with all the selected generators, its commutator with multiplication by the imaginary unit commutes with them as well and is conjugate-linear. Applied to a coordinate basis vector at k, its i-th coordinate is killed by the difference between w(j,i) and the conjugate of w(j,k). The separation hypothesis makes every such coordinate vanish. Thus A is complex-linear, and its real determinant is the squared modulus of its complex determinant.

For the order-three triangle bouquet, write the plane for each hyperplane of the generator vector space as one complex coordinate. Use a nonzero linear functional with that kernel and take its values on the standard generators as exponents of a primitive cube root of unity. If two columns were conjugate on every standard generator, their functionals would be negatives of one another and would have the same kernel. Distinct hyperplanes rule this out for distinct labels. A column also differs from its own conjugate because a nonzero functional has a nonzero value on some standard generator, and the two nonidentity cube roots are distinct.

## References

- Truth anchor: `D5/S3/HilbertOperators/OrderThreeOrientationBound.characterPlane`
- Truth anchor: `D5/S3/HilbertOperators/OrderThreeOrientationBound.characterPlane_commutator_bounds`
- Truth anchor: `D5/S3/HilbertOperators/OrderThreeOrientationBound.commutatorNorm`
- Truth anchor: `D5/S3/HilbertOperators/OrderThreeOrientationBound.sum_sq_commutatorNorm_ge_three`
