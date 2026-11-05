# A counterexample to the three-operator Clarkson–McCarthy inequality

## Abstract

Three complex matrices of order two violate the three-operator Clarkson–McCarthy inequality at exponent nine quarters.

**Definition 1.1 (The inequality for real exponents at least two).**

$$(\operatorname{D5.S3.Quantum.Matrix.ZhangThreeOperatorClarksonRefutation.claim}) \Leftrightarrow (\forall (p: \mathbb{R}), (((2: \mathbb{R}) \le p) \to (\forall (n: \mathbb{N}), (\forall (a: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\forall (b: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\forall (c: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{schattenNorm}\left(a + b + c, p\right)^{p} + \operatorname{schattenNorm}\left(a, p\right)^{p} + \operatorname{schattenNorm}\left(b, p\right)^{p} + \operatorname{schattenNorm}\left(c, p\right)^{p} \le (\frac{(3: \mathbb{R})^{p - (1: \mathbb{R})} + (1: \mathbb{R})}{(2: \mathbb{R})^{p}}) \cdot (\operatorname{schattenNorm}\left(a + b, p\right)^{p} + \operatorname{schattenNorm}\left(b + c, p\right)^{p} + \operatorname{schattenNorm}\left(c + a, p\right)^{p}))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Teng Zhang (2024). *Clarkson–McCarthy type inequalities, part I: ℓ_p–ℓ_p and ℓ_q–ℓ_p Schatten p-estimates*. URL: <https://arxiv.org/abs/2410.21961v4>.

*Commentary.*

The assertion quantifies over every real p at least two, every natural dimension n, and three complex n by n matrices a, b, c. The sum of the pth powers of the Schatten norms of a+b+c, a, b and c is bounded above by (3^(p−1)+1)/2^p times the corresponding sum for a+b, b+c and c+a. Here schattenNorm is the trace-functional-calculus Schatten norm; for positive p, its pth power is the sum of the pth powers of the singular values. The source defines the Schatten norm in lines 100–104 and states the conjecture labeled conj:sharp-inequality in lines 571–581 of its TeX source. This assertion is its finite complex matrix reading for p at least two. The reverse inequality for positive p at most two is a separate assertion.

**Theorem 1.2 (A counterexample at exponent nine quarters).**

$$\neg (\operatorname{D5.S3.Quantum.Matrix.ZhangThreeOperatorClarksonRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-2024-three-operator-clarkson-mccarthy` (refuted) by `D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-2024-three-operator-clarkson-mccarthy","declaration_gid":"D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Teng Zhang (2024). *Clarkson–McCarthy type inequalities, part I: ℓ_p–ℓ_p and ℓ_q–ℓ_p Schatten p-estimates*. URL: <https://arxiv.org/abs/2410.21961v4>.

*Commentary.*

For a complex matrix x of order two and a nonnegative real vector d, suppose the Gram matrix x*x has the same characteristic polynomial as the diagonal matrix with entries d, included in the complex numbers. Here x* denotes conjugate transpose. Both matrices are Hermitian, so their ordered eigenvalue vectors agree. Unitary similarity of the diagonal matrix with itself gives a permutation matching its eigenvalues to d. Reindexing the singular-value sum by this permutation and using nonnegativity of d shows that, for every p>0, the pth power of the Schatten norm of x is the sum of d(i)^(p/2).

Take A=coordinateProjectorTwo 0=diag(1,0), B=diag(0,1), and C=−(1/2)[[1,1],[1,1]]. Then A+B+C=(1/2)[[1,−1],[−1,1]]. The Gram matrices of A, B, C and A+B+C each have the characteristic polynomial of diag(1,0). Applying the preceding calculation with d=(1,0) shows that each of these four matrices has Schatten norm to the power p equal to one for every p>0. The left side of the asserted inequality is therefore four.

The Gram matrix of A+B=I is I. The calculation with the constant vector d=(1,1) gives Schatten norm to the power p equal to two. The Gram matrices of B+C and C+A are each (1/2)I. Applying the calculation with d=(1/2,1/2) gives 2(1/2)^(p/2) for each. The sum for the three pairwise sums is thus 2+4(1/2)^(p/2)=2+2^(2−p/2).

At p=9/4, positive real power laws give (3^(1/4))^4=3, (2^(1/4))^4=2, and (2^(7/8))^8=128. Comparing fourth and eighth powers of nonnegative numbers yields 3^(1/4)<13161/10000, 11892/10000<2^(1/4), and 2^(7/8)<18341/10000. Rewrite 3^(9/4−1)=3·3^(1/4), 2^(9/4)=4·2^(1/4), and 2−(9/4)/2=7/8. After clearing the positive denominator, the desired strict upper bound by four reduces to (3·3^(1/4)+1)(2+2^(7/8))<16·2^(1/4). Successively replacing the two factors on the left by their rational upper bounds gives (3·13161/10000+1)(2+18341/10000)<16·11892/10000<16·2^(1/4). The rational strict inequality follows by exact arithmetic.

If the assertion held, its instance at p=9/4, n=2, a=A, b=B and c=C would give 4≤((3^(9/4−1)+1)/2^(9/4))(2+2^(7/8)). The strict bound just established makes that right side smaller than four, a contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/ZhangThreeOperatorClarksonRefutation.result`
- Dependency: [D5/S3/Quantum/QubitWitnesses](../QubitWitnesses.md)
- Dependency: [D5/S3/Quantum/Schatten/Holder](../Schatten/Holder.md)
- Dependency: [D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes](../Tomography/MutuallyUnbiasedDiagonalPlanes.md)
