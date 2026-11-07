# Complete maximal identity for clique–path products

## Abstract

For i,j at least two, the maximal stable configuration lies in the reduced integer Laplacian image at every sink of K_i square P_j exactly for K_4 square P_2.

**Definition 1.1 (The integer-image condition at a sink).**

$$\forall (i: \mathbb{N}), (\forall (j: \mathbb{N}), (\forall (s: \operatorname{Fin}\left(i\right) \times \operatorname{Fin}\left(j\right)), ((\operatorname{maximalIdentityAt}\left(i, j, s\right)) \Leftrightarrow (\exists (f: \{v: \operatorname{Fin}\left(i\right) \times \operatorname{Fin}\left(j\right) // v \ne s\} \to \mathbb{Z}), (\forall (v: \{v: \operatorname{Fin}\left(i\right) \times \operatorname{Fin}\left(j\right) // v \ne s\}), (\sum_{w: \{v: \operatorname{Fin}\left(i\right) \times \operatorname{Fin}\left(j\right) // v \ne s\}} ((\operatorname{SimpleGraph}.\operatorname{lapMatrix}\left(\mathbb{Z}, \operatorname{SimpleGraph}.\operatorname{boxProd}\left((\operatorname{Top}.\operatorname{top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(i\right)\right)), \operatorname{SimpleGraph}.\operatorname{pathGraph}\left(j\right)\right), \operatorname{Subtype}.\operatorname{val}\left(v\right), \operatorname{Subtype}.\operatorname{val}\left(w\right)\right)) \cdot (f\left(w\right))) = ((\operatorname{Nat}.\operatorname{cast}\left(\operatorname{SimpleGraph}.\operatorname{degree}\left(\operatorname{SimpleGraph}.\operatorname{boxProd}\left((\operatorname{Top}.\operatorname{top}: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(i\right)\right)), \operatorname{SimpleGraph}.\operatorname{pathGraph}\left(j\right)\right), \operatorname{Subtype}.\operatorname{val}\left(v\right)\right)\right): \mathbb{Z})) - ((1: \mathbb{Z}))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity.maximalIdentityAt` (`✓ std3`).

*Citation.* Yibo Gao, Rupert Li (2021). *Compatible recurrent identities of the sandpile group and maximal stable configurations*. DOI: [10.1016/j.dam.2020.08.028](https://doi.org/10.1016/j.dam.2020.08.028). URL: <https://arxiv.org/abs/2008.10079v1>.

*Commentary.*

For natural i and j, the vertices of the Cartesian product of the complete graph on Fin i and the path on Fin j are pairs. Remove the row and column of the sink s from the integer Laplacian. The condition asks for an integer vector f whose image under this reduced matrix has value degree(v) minus one at each remaining vertex. The degree is a natural number cast to an integer before subtracting one. Gao–Li define the maximal stable configuration and note its recurrence in the arXiv v1 TeX, Paper/Preliminaries.tex, lines 19–29; the reduced matrix and the integer-image criterion for equivalence appear at lines 132–134 and 157–172. Their recurrent identity is the recurrent representative of the zero class, at lines 192–196. Paper/CMIP.tex, lines 8–10 and 37–41, defines the maximal identity property at one sink and at every sink. For i and j at least two, the formula expresses that property through the integer-image criterion.

**Definition 1.2 (The clique–path classification).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (i: \mathbb{N}), (\forall (j: \mathbb{N}), ((2 \le i) \Rightarrow ((2 \le j) \Rightarrow ((\forall (s: \operatorname{Fin}\left(i\right) \times \operatorname{Fin}\left(j\right)), (\operatorname{maximalIdentityAt}\left(i, j, s\right))) \Leftrightarrow ((i = 4) \land (j = 2)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yibo Gao, Rupert Li (2021). *Compatible recurrent identities of the sandpile group and maximal stable configurations*. DOI: [10.1016/j.dam.2020.08.028](https://doi.org/10.1016/j.dam.2020.08.028). URL: <https://arxiv.org/abs/2008.10079v1>.

*Commentary.*

For every pair of natural numbers i and j at least two, every sink of K_i square P_j satisfies the integer-image condition if and only if i equals four and j equals two. This is the reduced-Laplacian reading of Gao–Li's conjecture in the arXiv v1 TeX, Paper/Conjectures.tex, lines 136–140. The source reports computations through fifty at lines 136–142 and proves the cases j equal to two and three beginning at line 144.

**Theorem 1.3 (Proof of the classification).**

$$\forall (i: \mathbb{N}), (\forall (j: \mathbb{N}), ((2 \le i) \Rightarrow ((2 \le j) \Rightarrow ((\forall (s: \operatorname{Fin}\left(i\right) \times \operatorname{Fin}\left(j\right)), (\operatorname{maximalIdentityAt}\left(i, j, s\right))) \Leftrightarrow ((i = 4) \land (j = 2))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity.result` (`✓ std3`). ∎

*Resolves.* `Problems/gao-li-2020-complete-maximal-identity-clique-path` (proved) by `D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gao-li-2020-complete-maximal-identity-clique-path","declaration_gid":"D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yibo Gao, Rupert Li (2021). *Compatible recurrent identities of the sandpile group and maximal stable configurations*. DOI: [10.1016/j.dam.2020.08.028](https://doi.org/10.1016/j.dam.2020.08.028). URL: <https://arxiv.org/abs/2008.10079v1>.

*Commentary.*

Write G for K_i square P_j and L for its integer Laplacian. For a vector f on all vertices, the row at (a,t) is i f(a,t) minus the sum of f(b,t) over b in Fin i, plus the path Laplacian applied to the function u ↦ f(a,u) at t. The path row is the sum of the differences with the predecessor and successor whenever those vertices exist. Its degree counts these two possible neighbours. Summing the path degrees gives 2(j−1); summing degree(v)−1 over the product therefore gives the integer M = i(ij−2).

Suppose the image condition holds at s. Extend its integer solution to all vertices by setting f(s)=0. Away from s, Lf equals degree(v)−1. The Laplacian is symmetric and annihilates the constant-one vector, so the sum of the entries of Lf is zero. The total mass M then determines the missing equation at s: at every v, (Lf)(v) = degree(v)−1−M if v=s, and (Lf)(v) = degree(v)−1 otherwise.

Take s=(0,0), and compare the clique coordinates a=0 and b=1, which exist because i≥2. Put d(t)=f(a,t)−f(b,t). The clique sums cancel and the two vertices at the same path coordinate have equal degree. Thus i d(t) plus the path Laplacian of d at t is −M at t=0 and zero elsewhere. Reverse the path by setting x(k)=d(j−1−k) for k<j, and x(k)=0 for k≥j. The far endpoint gives x(1)=(i+1)x(0). Each interior row gives x(k+2)=(i+2)x(k+1)−x(k) when k+2<j. The sink endpoint gives (i+1)x(j−1)−x(j−2)=−i(ij−2).

Let S denote Polynomial.Chebyshev.S and put u_j=(S ℤ ((j:ℤ)−1)).eval((i:ℤ)+2). The case k=0 uses S ℤ 0=1 and S ℤ (−1)=0. For 1≤k<j, apply bounded_continuant_endpoint to the initial segment ending at k after casting x to a real sequence. Compatibility of Chebyshev evaluation with the integer-to-real map, injectivity of that map, and the Chebyshev recurrence give x(k)=((S ℤ (k:ℤ)).eval(i+2)−(S ℤ ((k:ℤ)−1)).eval(i+2))x(0) for k<j. Substitution at the last two indices, followed by the Chebyshev recurrence, yields (i+1)x(j−1)−x(j−2)=i u_j x(0). Compare this with the sink equation and cancel the nonzero integer i. The integer −x(0) then shows u_j divides ij−2.

Cast a_n=(S ℤ n).eval(i+2) to the rationals. The second order recurrence growth theorem with coefficient i+2 makes a_n positive and increasing. Its differences d_n=a_(n+1)−a_n satisfy the same recurrence; applying the theorem again shows they increase from d_0=i+1. Hence d_n>i, and a_(n+2)−in is nondecreasing. At j=3, u_j=i²+4i+3>3i−2; the increment bound extends u_j>ij−2 to every j≥3. Since ij−2 is positive, it cannot be divisible by this larger positive integer. For j=2, the divisibility becomes i+2 dividing 2i−2. Subtracting this from 2(i+2) shows i+2 divides six, hence 2≤i≤4. The values two and three fail the original divisibility, leaving precisely i=4.

For K_4 square P_2 and an arbitrary sink s, define f(v) to be zero at s, five when v≠s has the same second coordinate as s, six when its second coordinate differs but its first coordinate agrees, and seven otherwise. Restrict f to the non-sink vertices. The product and path row formulas, checked for the finite choices of the two coordinates, give (Lf)(v)=3 at every non-sink vertex; its degree is four. The omitted sink term is zero because f(s)=0, so this restricted vector satisfies the reduced integer Laplacian equations for every s.

Finally, the condition at every sink supplies the condition at (0,0), so the divisibility argument forces i=4 and j=2. Conversely, those equalities reduce the required condition at every sink to the explicit vectors just constructed. This establishes exactly the integer-image classification in the displayed proposition; the interpretation through recurrent configurations uses the source's sandpile-group characterization.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity.maximalIdentityAt`
- Truth anchor: `D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity.result`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination](../Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence](../Combinatorics/SpectralGraph/TwinFreeThetaRecurrence.md)
- Dependency: [D5/S3/Factorization/BoninShadowMarkoffPositivity](../Factorization/BoninShadowMarkoffPositivity.md)
