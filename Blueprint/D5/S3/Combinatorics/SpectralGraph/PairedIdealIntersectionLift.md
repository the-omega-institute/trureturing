# PairedIdealIntersectionLift

## Abstract

Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.

The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the supplied completed mathematical note. The formal proofs and this exposition are independently authored; no priority claim follows.

**Definition 1.1 (The full paired exponent family).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.pairExponents`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.pairExponents` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The exponent vector is (a,a,b,c). Neither tail exponent is bounded above. The final actual graph theorems permit every prime permutation.

**Theorem 1.2 (Injective paired support construction).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_lift_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_lift_nonzero` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For each tail support T, assign h(T) to {0} union T and -h(T) to {1} union T; all other supports get zero. The positive member of each pair is a genuine nonempty proper support cell with positive weight, so any nonzero coordinate vector lifts to a nonzero graph vector.

**Theorem 1.3 (Exact zero sum of actual paired vectors).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_lift_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_lift_sum` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Each paired cell has the same positive multiplicity a times the product of the tail exponents in T. The two values cancel exactly, including the extension by zero across all universal vertices.

**Theorem 1.4 (Exact actual paired action).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_support_action`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_support_action` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The support-complement Laplacian on this subspace is K_a-I. The proof evaluates the full four-coordinate support algebra with symbolic exponents, including all zero cells and both removed endpoints. It enumerates the fixed support carrier, not a finite set of exponents.

**Theorem 1.5 (Actual paired spectral lift).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.actual_paired_eigenvalue`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.actual_paired_eigenvalue` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

A nonzero eigenvector of K_a with eigenvalue kappa lifts to the actual ideal graph eigenvalue V+1-kappa, V=(a+1) squared (b+1)(c+1)-2. The paired vector has explicit zero sum, so the reflection is valid even if kappa-1 is zero.

## Complete resonance tables and actual graph application

The resonance application is attributed to four-prime-resonance-discriminant, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. Use the complete determinant and local-normalization application in PairedIdealIntersectionDeterminants, with F(s,z)=(2s-1)²z²+2s²(2s-1)²z+s⁴. The tables below enumerate the entire residue fields; the subsequent parameter families are unbounded. Passing a table entry is only a necessary square test, never a root-existence or integral-spectrum assertion.

For p=5 and s=2 the square values are {0,1,4}. In the following complete table, roots(z) denotes exactly {v in ZMod 5 : v²=F(2,z)}. Evaluation gives F(2,z)=4z²+2z+1 in ZMod 5. Each listed root set follows by testing the five possible v, so it also certifies every excluded root.

$$
\begin{aligned}z=0,\quad\operatorname{F}\left(2, 0\right)=1,\quad\operatorname{roots}\left(0\right)=\{1,4\}\\z=1,\quad\operatorname{F}\left(2, 1\right)=2,\quad\operatorname{roots}\left(1\right)=\emptyset\\z=2,\quad\operatorname{F}\left(2, 2\right)=1,\quad\operatorname{roots}\left(2\right)=\{1,4\}\\z=3,\quad\operatorname{F}\left(2, 3\right)=3,\quad\operatorname{roots}\left(3\right)=\emptyset\\z=4,\quad\operatorname{F}\left(2, 4\right)=3,\quad\operatorname{roots}\left(4\right)=\emptyset\end{aligned}
$$

Consequently, for every z in ZMod 5, (there exists v in ZMod 5 with v²=F(2,z)) if and only if z=0 or z=2. In particular z=1 is excluded.

For p=7 and s=3 the square values are {0,1,2,4}. Here roots(z) denotes exactly {v in ZMod 7 : v²=F(3,z)}. Evaluation gives F(3,z)=4z²+2z+4 in ZMod 7. Testing all seven v gives the following complete table, including the passing entry z=5 whose value is 2.

$$
\begin{aligned}z=0,\quad\operatorname{F}\left(3, 0\right)=4,\quad\operatorname{roots}\left(0\right)=\{2,5\}\\z=1,\quad\operatorname{F}\left(3, 1\right)=3,\quad\operatorname{roots}\left(1\right)=\emptyset\\z=2,\quad\operatorname{F}\left(3, 2\right)=3,\quad\operatorname{roots}\left(2\right)=\emptyset\\z=3,\quad\operatorname{F}\left(3, 3\right)=4,\quad\operatorname{roots}\left(3\right)=\{2,5\}\\z=4,\quad\operatorname{F}\left(3, 4\right)=6,\quad\operatorname{roots}\left(4\right)=\emptyset\\z=5,\quad\operatorname{F}\left(3, 5\right)=2,\quad\operatorname{roots}\left(5\right)=\{3,4\}\\z=6,\quad\operatorname{F}\left(3, 6\right)=6,\quad\operatorname{roots}\left(6\right)=\emptyset\end{aligned}
$$

Thus, for every z in ZMod 7, (there exists v in ZMod 7 with v²=F(3,z)) if and only if z=0 or z=3 or z=5. This second universal table is independent of its use in any particular progression.

For every pair n,m of natural numbers and every integer c, set a=6+25n and b=20+100n+125m. Then det(K(a,b,c)-2I) is nonzero. Indeed take p=5, e=1, H=1+5n and U=1+5n+5m. The identities a=2-1+5H and b=-5H+25U are exact in the integers. Neither H nor 2-1 is divisible by 5, and the residues of H and U are both 1. A zero determinant would therefore give a square witness for F(2,U/H²)=F(2,1)=2 in ZMod 5, contradicting the complete first table. The argument places no positivity or upper bound on c and no ordering or coprimality condition on the tails.

To pass from this determinant exclusion to actual graph nonintegrality, first consider real a≥2, b≥2a-2 and c≥2a-2. Write S=symmetricK a b c. For the principal submatrix of S-3I on the empty and full tail supports, its exact determinant is the expression below.

$$
J = -\left(\left(a + 2\right) \cdot \left(b - \left(2 \cdot a - 2\right)\right) \cdot \left(c - \left(2 \cdot a - 2\right)\right)\right) - \left(a^{2} + 3 \cdot a - 2\right) \cdot \left(b - \left(2 \cdot a - 2\right) + c - \left(2 \cdot a - 2\right)\right) - 2 \cdot \left(a - 1\right) \cdot \left(3 \cdot a + 2\right)
$$

The first two subtracted products are nonnegative: a+2>0, a²+3a-2>0 and both tail offsets are nonnegative. The last subtracted product 2(a-1)(3a+2) is strictly positive. Thus J<0 even when either or both tail offsets vanish. A positive semidefinite matrix has nonnegative determinant on every principal submatrix, so S-3I is not positive semidefinite. PairedIdealIntersectionObstructions.negative_eigenpair_of_not_posSemidef supplies an actual nonzero eigenvector of S-3I with negative eigenvalue; adding 3 gives a genuine eigenpair (lambda,v) of S with lambda<3. The same source symmetric_eigenvalue_gt_one, from symmetricK_sub_one_posDef, gives 1<lambda because a>0 and b,c≥0. These supplier declarations, and tensor_eigenpair_of_symmetric, are cited at repository revision 8eda9f6e10518fd456dbf9de2e24610fdc027597. Positive b,c make the diagonal weights invertible, so tensor_eigenpair_of_symmetric transports v to a nonzero eigenvector of the original weighted K with the same lambda.

Now let primes : Fin 4 → Nat be any injective map whose four values are prime. Let n,m,c be arbitrary natural numbers with c≥2(6+25n)-2, and put a=6+25n, b=20+100n+125m. The exponent vector pairExponents a b c is exactly (a,a,b,c), and the modulus is the product of primes(i) to these four exponents. The actual ideal-intersection graph of this modulus is not ActualLaplacianIntegral. This quantifies every prime permutation and every n,m,c in the stated domain, including c=2a-2. ActualLaplacianIntegral means every real HasActualEigenvalue of the graph is an integer; the conclusion concerns the actual graph on nonzero proper ideals.

For the proof, a≥6 and b-(2a-2)=10+50n+125m≥0, while the assumed bound gives c≥2a-2. The preceding principal-minor argument supplies an eigenvalue 1<lambda<3 of K with a nonzero eigenvector. PairedIdealIntersectionLift.actual_paired_eigenvalue, at repository revision 8eda9f6e10518fd456dbf9de2e24610fdc027597, transports this eigenpair to the actual graph eigenvalue lambdaPrime=V+1-lambda, where the integer vertex count is V=(a+1)²(b+1)(c+1)-2. Its lift is nonzero and has exactly zero sum by paired_lift_nonzero and paired_lift_sum, so complement reflection is justified on this actual vector. The source ideal/support graph identification applies to every such injective prime map; no equality of a quotient spectrum with the full graph spectrum is assumed.

If the actual graph were Laplacian integral, lambdaPrime would be an integer, hence lambda=V+1-lambdaPrime would be an integer. The strict interval (1,3) forces lambda=2. The nonzero tensor eigenvector then lies in the kernel of K-2I, so its determinant is zero by the existing matrix determinant/injectivity criterion. The determinant has integer coefficients, and casting from integers to reals is injective, so this contradicts the preceding determinant nonvanishing for every integer c. Therefore the graph is not ActualLaplacianIntegral. Neither a bounded exponent rectangle nor a local passing residue is used as a substitute for this actual eigenpair and lift.

This application leaves bad-prime cases, other resonance branches, the general four-prime and higher-prime Q3 problems, and academic approval or publication outside its conclusion. It preserves the supplied source attribution without asserting a reuse license for future joint materials or importing joint code or private correspondence.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.actual_paired_eigenvalue`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.pairExponents`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_lift_nonzero`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_lift_sum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.paired_support_action`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions](PairedIdealIntersectionObstructions.md)
