# The exact cooling-code optimum in the projective-plane progression

## Abstract

An exact cooling-code optimum for a family of finite projective planes with one extra coordinate.

**Theorem 1.1 (Exactly n minus one information classes).**

$$\forall (F: Type) [\operatorname{Field}\left(F\right)] [\operatorname{Finite}\left(F\right)],\quad \operatorname{let} q=Nat.card\left(F\right), n=q(q+1)+2, m=n/2,\quad(7 \le q \land ((\operatorname{Odd}\left(m\right) \land \neg \operatorname{IsSquare}\left(q+1\right)) \lor (\operatorname{Even}\left(m\right) \land \neg \operatorname{IsSquare}\left(q-1\right)))) \implies \operatorname{IsGreatest}\left(\{s: \mathbb{N} | \exists P \in \operatorname{Fin}\left(s\right) \to \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{IsSupportFamily}\left(P, q-1, 2\right)\}, n-1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/ProjectiveOptimum.support_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shuangqing Liu, Qianfei Zhang, Shikang Yu, Menglong Zhang, Lijun Ji (2026). *Optimal bounds for (n,t,w,w−2)-constant-power error-correcting cooling codes*. URL: <https://arxiv.org/abs/2611.34386v1>.

*Commentary.*

For the binary support model the deletion size is two, the word weight is q − 1, and the correction radius is q − 3. At weight q − 1, at most one shared point is equivalent to distance at least 2(q − 3) + 1 because the Hamming distance is even. Every line over the field F has q + 1 points and contributes all of its weight-(q − 1) subsets as one information class. Two deletions leave at least q − 1 points on each line. Distinct lines meet in at most one point. The q(q + 1) + 1 points embed into the coordinate set with one unused coordinate, giving n − 1 classes.

The finite leave bound gives at most n classes. The residue-two equality criterion would give a design with m two-point groups if n were attained. With k = q + 1, the design has n blocks and each point lies in k blocks. Its square integer incidence matrix A has Gram matrix kI + J − P, where J is all ones and P indicates pairs of indices in the same group, including on the diagonal. The m two-by-two blocks in kI − P each have determinant k(k − 2). Adding J multiplies the determinant by 1 + n/(k − 2). Since k − 2 + n = k², the result is k to the power m + 2 times (k − 2) to the power m − 1. The odd exponent on the nonsquare factor gives an odd prime valuation, contradicting the square det(A)².

The field of order seven gives the length-58 result. The theorem also covers even and odd finite field orders satisfying the disjunction. Section 5's unrestricted even-deletion construction question remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/Hamming/ConstantPowerCooling/ProjectiveOptimum.support_optimum`
- Dependency: [D5/S3/Combinatorics/Hamming/ConstantPowerCooling/GroupDivisibleDesign](GroupDivisibleDesign.md)
