# The normal-modulus triangle constant in dimension two

## Abstract

A Hermitian pair in dimension two rules out every normal-modulus triangle constant below one quarter.

Bourin and Lee, Triangle inequalities for the operator symmetric modulus, arXiv:2602.19607v1, §4, Corollary 4.2, verbatim: “Corollary 4.2. Let A, B ∈ Mn be normal. Then, for some unitary V ∈ Mn, |A + B| ≤ |A| + |B| + (1/4) V(|A| + |B|)V*. If n ≥ 3, the constant 1/4 is the smallest possible one.” The following paragraph asks verbatim: “However, contrarily to the Schur version (4.1), it seems necessary to request n ≥ 3 in Corollary 4.2 to get sharpness of 1/4 (what is the best constant for n = 2 ?).”

**Definition 1.1 (Positive modulus).**

$$\forall X: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \forall P: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \operatorname{IsModulus}\left(X, P\right) \Leftrightarrow ((\operatorname{PosSemidef}\left(P\right)) \land (P \cdot P = \operatorname{conjTranspose}\left(X\right) \cdot X))$$

*Formalization.* `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.IsModulus` (`✓ std3`).

*Citation.* J.-C. Bourin; E.-Y. Lee (2026). *Triangle inequalities for the operator symmetric modulus*. DOI: [10.1090/proc/17861](https://doi.org/10.1090/proc/17861). URL: <https://arxiv.org/abs/2602.19607v1>.

*Commentary.*

For complex 2×2 matrices X and P, IsModulus X P requires P to be positive semidefinite and P²=X*X. Here X* is the conjugate transpose. The characterization “the positive square root is unique” is quoted, not proved or used: the proof checks both conditions for each explicit P.

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

## References

- Truth anchor: `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.IsModulus`
- Truth anchor: `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.IsNormalMatrix`
- Truth anchor: `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.result`
