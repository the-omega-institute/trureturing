# Exact Positive-Cone Propagation

## Abstract

The positive-cone crossing sandwich lowers the exact winding phase by two.

**Theorem 1.1 (The crossing sandwich lowers the winding phase by two).**

$$\begin{gathered}\forall T,b,c\in\mathbb{N},\quad 2\leq T,\quad b\leq c,\quad b^2+c^2+1=T^2+bc\longrightarrow\\\gamma=\begin{pmatrix}T+c-b&b\\c&T+b-c\end{pmatrix},\quad M=\begin{pmatrix}3&1\\2&1\end{pmatrix},\\(c_\gamma,c_M,c_{\gamma M},c_{M\gamma M})=(c,2,c+2T+2b,8T+7c),\\c+2T+2b\geq2c+2(T-\sqrt{T^2-1})>0,\\c_\gamma\operatorname{tr}(\gamma)>0,\quad c_{M\gamma M}\operatorname{tr}(M\gamma M)>0,\\\operatorname{Phi}(M)=2,\quad \operatorname{Phi}(\gamma M)=\operatorname{Phi}(\gamma)+\operatorname{Phi}(M)-3,\\\operatorname{Phi}(M\gamma M)=\operatorname{Phi}(M)+\operatorname{Phi}(\gamma M)-3,\\\operatorname{Psi}(M\gamma M)=\operatorname{Psi}(\gamma)-2.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Crossing/ExactPropagation.exact_propagation_positive_cone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let T, b, and c be natural numbers with 2 <= T, b <= c, and b^2 + c^2 + 1 = T^2 + bc. Define gamma = [[T+c-b,b],[c,T+b-c]] and M = [[3,1],[2,1]]. The cone equation forces every coefficient used by the phase formula to be positive; in particular T+b-c > 0.

Direct multiplication gives the complete lower-left chain c, 2, c+2T+2b, and 8T+7c. Completing the square in the cone equation gives c-b <= sqrt(T^2-1), while sqrt(T^2-1) < T. These two bounds prove the displayed inequality and make the endpoint sign corrections positive.

The phase proof uses the repository's finite rational Dedekind sum and its proved reciprocity theorem. A residue-permutation argument first proves invariance under inverse numerators. Two reciprocity calculations then establish the right and left multiplication corrections separately, each with correction -3; no cocycle law is assumed. Since the fixed matrix has Phi(M)=2, the winding phase of M gamma M is exactly Psi(gamma)-2.

Local searches in D5 and pinned Mathlib found no ready-made Rademacher phase or cocycle theorem. The exact imported hits are the finite Dedekind sum, its residue-permutation lemma, and Dedekind reciprocity. Loogle returned Unknown identifier Rademacher; the grep.app query returned HTTP 503, and the attempted LeanSearch endpoint returned HTTP 404.

## References

- Truth anchor: `D5/S3/PrimeForms/Crossing/ExactPropagation.exact_propagation_positive_cone`
