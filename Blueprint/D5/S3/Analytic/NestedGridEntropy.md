# Nested Grid Entropy

## Abstract

A legal binary refinement history imposes an entropy budget beyond the static averaging lower bound.

**Theorem 1.1 (Finite resolution cost with explicit refinement losses).**

$$\forall C,B,A: \mathbb{N} \to \operatorname{List}\left(\mathbb{R}\right), \forall a,b,c: \mathbb{N} \to \mathbb{R}, \operatorname{C}\left(0\right) = [1] \land (\forall k \in \mathbb{N}, (0 < a_{k} \land 0 < b_{k}) \land C_{k} = B_{k}++[a_{k}+b_{k}]++A_{k} \land C_{k+1} = B_{k}++[a_{k},b_{k}]++A_{k} \land (\forall x \in C_{k}, x \le c_{k})) \longrightarrow \text{let } \delta_{k} := (c_{k}-(a_{k}+b_{k}))\operatorname{log}\left(2\right)+(a_{k}+b_{k})(\operatorname{log}\left(2\right)-\operatorname{H}\left(\frac{a_{k}}{a_{k}+b_{k}}\right)); (\forall k, 0 \le \delta_{k}) \land (\forall n \in \mathbb{N}, \operatorname{log}\left(\frac{1}{c_{n}}\right)+\sum_{k<n} \delta_{k} \le \operatorname{log}\left(2\right)\sum_{k<n} c_{k})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NestedGridEntropy.binary_refinement_entropy_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial cell list is [1]. At each step an actual listed parent a+b is replaced by two positive children a and b, leaving the other cells unchanged. From these identities the proof derives positive unit total mass at every stage, the exact entropy increment, and a terminal entropy lower bound from the maximal-cell cap. Each nonnegative loss equals the cost of splitting below the cap plus the binary-entropy deficit of the split ratio. The theorem bounds final log resolution plus cumulative loss by log(2) times the sum of past caps. The ordinary consumer gives the sharp 1/log(2)^2 sequential error factor for the previously derived two-moment grid loss using the classical Niederreiter logarithmic construction. The sequence theorem and the full grid identification are not claimed as kernel-checked by this declaration.

## References

- Truth anchor: `D5/S3/Analytic/NestedGridEntropy.binary_refinement_entropy_budget`
