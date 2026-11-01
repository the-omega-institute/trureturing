# The normal-modulus triangle constant in dimension two

## Abstract

A Hermitian pair in dimension two rules out every normal-modulus triangle constant below one quarter.

Bourin and Lee, Triangle inequalities for the operator symmetric modulus, arXiv:2602.19607v1, §4, Corollary 4.2, verbatim: “Corollary 4.2. Let A, B ∈ Mn be normal. Then, for some unitary V ∈ Mn, |A + B| ≤ |A| + |B| + (1/4) V(|A| + |B|)V*. If n ≥ 3, the constant 1/4 is the smallest possible one.” The following paragraph asks verbatim: “However, contrarily to the Schur version (4.1), it seems necessary to request n ≥ 3 in Corollary 4.2 to get sharpness of 1/4 (what is the best constant for n = 2 ?).”

**Definition 1.1 (Positive modulus).**

$$\forall X: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall P: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \operatorname{IsModulus}\left(X, P\right) \Leftrightarrow ((\operatorname{PosSemidef}\left(P\right)) \land (P \cdot P = \operatorname{conjTranspose}\left(X\right) \cdot X))$$

*Formalization.* `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.IsModulus` (`✓ std3`).

*Citation.* J.-C. Bourin; E.-Y. Lee (2026). *Triangle inequalities for the operator symmetric modulus*. DOI: [10.1090/proc/17861](https://doi.org/10.1090/proc/17861). URL: <https://arxiv.org/abs/2602.19607v1>.

*Commentary.*

For complex 2×2 matrices X and P, IsModulus X P requires P to be positive semidefinite and P²=X*X. Here X* is the conjugate transpose. The characterization “the positive square root is unique” is quoted; the fixed-pair proof checks both conditions for each explicit P.

**Definition 1.2 (Normal matrices).**

$$\forall X: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \operatorname{IsNormalMatrix}\left(X\right) \Leftrightarrow (\operatorname{conjTranspose}\left(X\right) \cdot X = X \cdot \operatorname{conjTranspose}\left(X\right))$$

*Formalization.* `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.IsNormalMatrix` (`✓ std3`).

*Citation.* J.-C. Bourin; E.-Y. Lee (2026). *Triangle inequalities for the operator symmetric modulus*. DOI: [10.1090/proc/17861](https://doi.org/10.1090/proc/17861). URL: <https://arxiv.org/abs/2602.19607v1>.

*Commentary.*

IsNormalMatrix X means X*X=XX*. The witness matrices are Hermitian and therefore normal.

**Definition 1.3 (A constant smaller than one quarter).**

$$claim \Leftrightarrow (\exists c: \mathbb{R}, (c < \frac{1}{4}) \land (\forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall B: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), (\operatorname{IsNormalMatrix}\left(A\right)) \Rightarrow ((\operatorname{IsNormalMatrix}\left(B\right)) \Rightarrow (\forall PA: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall PB: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall PS: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), (\operatorname{IsModulus}\left(A, PA\right)) \Rightarrow ((\operatorname{IsModulus}\left(B, PB\right)) \Rightarrow ((\operatorname{IsModulus}\left(A + B, PS\right)) \Rightarrow (\exists V: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), (\operatorname{memUnitaryGroup}\left(V\right)) \land (\operatorname{PosSemidef}\left(PA + PB + \operatorname{ofReal}\left(c\right) \cdot (V \cdot (PA + PB) \cdot \operatorname{conjTranspose}\left(V\right)) - PS\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J.-C. Bourin; E.-Y. Lee (2026). *Triangle inequalities for the operator symmetric modulus*. DOI: [10.1090/proc/17861](https://doi.org/10.1090/proc/17861). URL: <https://arxiv.org/abs/2602.19607v1>.

*Commentary.*

The claim asserts the existence of a real c<1/4 working for every normal complex 2×2 pair A,B. For every PA,PB,PS satisfying IsModulus A PA, IsModulus B PB, and IsModulus (A+B) PS, there must be a unitary V making PA+PB+cV(PA+PB)V*−PS positive semidefinite. The real c is cast to a complex scalar. This is the smaller-constant assertion associated with the question following Corollary 4.2; the source's upper bound at c=1/4 is not formalized here.

**Theorem 1.4 (Every smaller constant fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.result` (`✓ std3`). ∎

*Resolves.* `Problems/bourin-lee-2026-normal-modulus-constant-n2` (refuted) by `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bourin-lee-2026-normal-modulus-constant-n2","declaration_gid":"D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* J.-C. Bourin; E.-Y. Lee (2026). *Triangle inequalities for the operator symmetric modulus*. DOI: [10.1090/proc/17861](https://doi.org/10.1090/proc/17861). URL: <https://arxiv.org/abs/2602.19607v1>.

*Commentary.*

Take A=diag(1,0), M=(1/25)[[9,−12],[−12,16]], and B=−M. The matrix M is the projection onto (3,−4)/5. The lemmas modulus_A, modulus_M, and modulus_PS give PA=A, PB=M, and PS=(4/5)I. Put D=A+M and x=(1,2). The lemmas d_pos, d_quad, ps_quad, and d_upper give D≥0, x*Dx=2, x*PSx=4, and D≤(8/5)I. The identity conjugation_quad holds for every matrix V. For unitary V, it and the conjugated positivity certificates give 0≤q=x*VDV*x≤8. The asserted inequality requires 4≤2+cq. If c≥0, this yields 4≤2+8c and c≥1/4; if c<0, it yields 4≤2. Both contradict c<1/4. Thus the displayed Hermitian pair defeats every unitary for every smaller real constant. Together with the source's Corollary 4.2, the lower bound gives the attained best constant 1/4 in dimension two; that upper bound is a source consequence rather than a theorem of this module. As exact mathematical reasoning, A+B=(1/25)[[16,12],[12,−16]] is of reflection type, with scalar modulus (4/5)I, whereas D has eigenvalues 2/5 and 8/5. The ratio ((4/5)−(2/5))/(8/5)=1/4 also governs the Schur version (4.1); that comparison is not formalized. Sharpness in Theorem 4.1 for other positive maps between small dimensions and the classification of equality cases are not settled by this result. The journal version's text is ASSUMED-UNVERIFIED; the quotations refer to arXiv:2602.19607v1, §4.

For the arbitrary rank-one application, let n≥2 and retain the same ordered pair of nonzero rank-one normal matrices A,B in Mₙ(ℂ), the right modulus |X|=sqrt(X*X), and D=|A|+|B|. Define S(A,B)={c≥0 : there is U∈U(n) with D+cUDU*−|A+B| positive semidefinite}. The group here is the full ambient unitary group, including transformations mixing the joint range with its orthogonal complement.

The normal spectral diagonalization Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal and rank of a diagonal matrix give A=αP and B=βQ, with α,β≠0 and rank-one orthogonal projections P,Q. Set a=|α|, b=|β|, ξ=a/α and ω=ξβ/b. Then a,b>0, |ξ|=|ω|=1, ξA=aP and ξB=bωQ. The single multiplier ξ preserves each right modulus, including that of A+B, since (ξX)*(ξX)=X*X. The positive-square-root uniqueness CFC.sqrt_unique applied to (αP)*(αP)=a²P gives |A|=aP and likewise |B|=bQ, hence D=aP+bQ. This correspondence preserves the actual relative phase and the actual feasible set S(A,B).

For a rank-one projection P=uu* with u*u=1, PureStateHandshake.pure_state_handshake gives PXP=tr(PX)P. Applying this to Q, and to the positive projections Q and I−Q, shows 0≤tr(PQ)≤1. Thus r=sqrt(tr(PQ)) is real with 0≤r≤1. If r=0, the identity tr((QP)*(QP))=tr(PQ)=0 gives QP=PQ=0. Consequently the right squared modulus of aP+bωQ is a²P+b²Q=D², and |A+B|=D. If r=1, the trace of (P−Q)*(P−Q) is 2−2tr(PQ)=0, so P=Q and |A+B|=|a+bω|P≤(a+b)P=D. If ω=1, the normalized sum aP+bQ is positive semidefinite and again |A+B|=D. In each of these three cases 0 belongs to S(A,B), is its least element, and equals its infimum. The coincident-projection argument includes a+bω=0; none of these cases divides by an interior parameter.

For 0<r<1 and ω≠1, set s=a+b, z=(a−b)/s, q=4ab/s², η=(1−Re ω)/2, x=sqrt(1−q(1−r²)), y=sqrt(1−qr²η), x₀=sqrt(1−y²), and W=z²+qr²(1−η). Then q=1−z², 0<q≤1, and 0<η≤1. The latter strict inequality uses |ω|=1: Re ω=1 would force Im ω=0 and ω=1. Since qr²η≤r²<1, one has 0<y<1; likewise 0<x<1, 0<x₀<1, x₀=sqrt(q)r sqrt(η), and W=x²−x₀²≥0, hence x₀≤x. These bounds include a=b and η=1, with W allowed to vanish. They justify the interior divisions by y, x₀ and x+x₀ while leaving the boundary arguments independent.

The projection relations also give an ambient projection formula. For t=tr(PQ)=r²<1, put R=(P+Q−PQ−QP)/(1−t). The sandwich identities PQP=tP and QPQ=tQ imply R*=R, R²=R, RP=P and RQ=Q. Therefore R is positive semidefinite; cyclicity of trace and tr(P)=tr(Q)=1 give tr(R)=2. All these identities concern matrices on the full ambient space.

The ambient lower-bound argument also applies independently of a two-dimensional reduction. Let K=|A+B|−D, let e be a unit vector with Ke=ke, and suppose D≤LI. For every ambient unitary U, conjugation gives UDU*≤LI. If c≥0 is feasible, adding the positive matrices c(LI−UDU*) and cUDU*−K gives cLI−K≥0. Its quadratic form at e is cL−k≥0. Thus every such U forces k≤cL; when L>0 and k>0, every c<k/L fails. No invariance of the joint range under U is needed for this implication.

For real parameters 0≤x<1 and 0<y<1, put C=(sqrt((1−y)²+2(1−x²)(1−y)/y)−(1−y))/(1+x). The radicand is strictly greater than (1−y)², so C>0. Squaring the defining equality (1+x)C+(1−y)=sqrt((1−y)²+2(1−x²)(1−y)/y) gives ((1+x)/2)C²+(1−y)C−(1−x)(1−y)/y=0. If another positive d satisfies this equation, subtracting the two equations factors as (d−C)(((1+x)/2)(d+C)+1−y)=0. The second factor is positive, so d=C. This scalar identity requires a native spectral identification before it can specify the optimum of S(A,B). The remaining interior obligations are the right-modulus spectrum for this same pair, its positive defect eigenvalue, the attaining ambient unitary, and the resulting exact coefficient and reverse zero-set implication.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.IsModulus`
- Truth anchor: `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.IsNormalMatrix`
- Truth anchor: `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.result`
