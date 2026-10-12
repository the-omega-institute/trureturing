# Endpoint comparison of Gini means on a bounded interval

## Abstract

A three-point rational witness refutes endpoint characterization of Gini mean comparisons.

Grünwald and Páles, Comparison of Gini means with fixed number of variables, arXiv:2408.07658v1, §4, introductory paragraph, verbatim: “We conclude this paper by formulating two conjectures that we have not been able to verify. The first conjecture seems to be a natural extension of the formula for Γ2(I), if 0 < inf I < sup I < ∞.” Conjecture 1 states verbatim: “Conjecture 1. Let n ≥ 3 and let I be a subinterval of R+ such that 0 < a := inf I < sup I =: b < ∞. Then Γn(I) = {((r, s), (p, q)) ∈ R² × R² | r + s ≤ p + q, G[n]r,s(a, …, a, b) ≤ G[n]p,q(a, …, a, b), and G[n]r,s(a, b, …, b) ≤ G[n]p,q(a, b, …, b)}.”

**Definition 1.1 (The distinct-parameter Gini mean).**

$$\forall n: (\mathbb{N}), \forall r: (\mathbb{R}), \forall s: (\mathbb{R}), \forall x: (\operatorname{Fin}\left(n\right) \to \mathbb{R}), \operatorname{giniMean}\left(r, s, x\right) = (\frac{\sum_{i: \operatorname{Fin}\left(n\right)} \operatorname{x}\left(i\right)^{r}}{\sum_{i: \operatorname{Fin}\left(n\right)} \operatorname{x}\left(i\right)^{s}})^{\frac{1}{r - s}}$$

*Formalization.* `D5/S3/ArithSums/GiniMeanEndpointComparison.giniMean` (`✓ std3`).

*Citation.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

For x : Fin n → ℝ, giniMean r s x is the displayed real-power expression. For positive coordinates and r≠s it is the source's Gini mean. The Lean definition is a total real-valued expression; the equal-parameter mean is not encoded.

**Definition 1.2 (One upper endpoint).**

$$\forall n: (\mathbb{N}), \forall a: (\mathbb{R}), \forall b: (\mathbb{R}), \forall i: (\operatorname{Fin}\left(n\right)), \operatorname{lowTuple}\left(n, a, b, i\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) + 1 = n, b, a\right)$$

*Formalization.* `D5/S3/ArithSums/GiniMeanEndpointComparison.lowTuple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

The index i ranges over Fin n. The value val i is its natural-number index. The tuple places b at the last index and a elsewhere, so for n=3 it is (a,a,b).

**Definition 1.3 (One lower endpoint).**

$$\forall n: (\mathbb{N}), \forall a: (\mathbb{R}), \forall b: (\mathbb{R}), \forall i: (\operatorname{Fin}\left(n\right)), \operatorname{highTuple}\left(n, a, b, i\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) = 0, a, b\right)$$

*Formalization.* `D5/S3/ArithSums/GiniMeanEndpointComparison.highTuple` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

The tuple places a at index zero and b elsewhere, so for n=3 it is (a,b,b). Both tuple definitions also apply to n=0, when there are no indices.

**Definition 1.4 (Sufficiency of the two extreme endpoint tests).**

$$claim \Leftrightarrow (\forall n: (\mathbb{N}), (3 \le n) \Rightarrow (\forall a: (\mathbb{R}), \forall b: (\mathbb{R}), (0 < a) \Rightarrow ((a < b) \Rightarrow (\forall r: (\mathbb{R}), \forall s: (\mathbb{R}), \forall p: (\mathbb{R}), \forall q: (\mathbb{R}), (r \ne s) \Rightarrow ((p \ne q) \Rightarrow ((r + s \le p + q) \Rightarrow ((\operatorname{giniMean}\left(r, s, \operatorname{lowTuple}\left(n, a, b\right)\right) \le \operatorname{giniMean}\left(p, q, \operatorname{lowTuple}\left(n, a, b\right)\right)) \Rightarrow ((\operatorname{giniMean}\left(r, s, \operatorname{highTuple}\left(n, a, b\right)\right) \le \operatorname{giniMean}\left(p, q, \operatorname{highTuple}\left(n, a, b\right)\right)) \Rightarrow (\forall x: (\operatorname{Fin}\left(n\right) \to \mathbb{R}), (\forall i: (\operatorname{Fin}\left(n\right)), (a \le \operatorname{x}\left(i\right)) \land (\operatorname{x}\left(i\right) \le b)) \Rightarrow (\operatorname{giniMean}\left(r, s, x\right) \le \operatorname{giniMean}\left(p, q, x\right)))))))))))$$

*Formalization.* `D5/S3/ArithSums/GiniMeanEndpointComparison.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

The claim is the proposed ⊇ inclusion of Conjecture 1 for closed intervals [a,b] and distinct parameters r≠s and p≠q. It quantifies over n≥3 and 0<a<b. The parameter-sum inequality and both endpoint comparisons are required to imply comparison at every tuple whose coordinates lie in [a,b]. This restricted implication is enough to refute the full conjectured equality.

**Theorem 1.5 (The extreme endpoint tests are insufficient).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GiniMeanEndpointComparison.result` (`✓ std3`). ∎

*Resolves.* `Problems/grunwald-pales-2024-gini-mean-comparison` (refuted) by `D5/S3/ArithSums/GiniMeanEndpointComparison.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"grunwald-pales-2024-gini-mean-comparison","declaration_gid":"D5/S3/ArithSums/GiniMeanEndpointComparison.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

Take n=3, a=1, b=3, (r,s)=(3,−1), and (p,q)=(0,2). Both parameter sums equal 2. The lemmas gini_low_rs and gini_low_pq give fourth powers 87/7 and 121/9 at (1,1,3). The lemmas gini_high_rs and gini_high_pq give 33 and 361/9 at (1,3,3). The nonnegativity lemmas and le_fourth establish both endpoint comparisons. The private tuple x=(1,1,5/3) has all coordinates in [1,3]. The lemmas gini_x_rs and gini_x_pq give fourth powers 895/351 and 1849/729 there. Their order reverses: 895·729=652455>648999=1849·351. Applying the claim to this tuple yields a false fourth-power inequality. Thus the proposed ⊇ inclusion, and hence Conjecture 1, fails. As mathematical reasoning, homogeneity scales x to (a,a,5a/3), an endpoint configuration at a smaller ratio. For these parameters the comparison fails at ratio 5/3 but holds at ratio 3, so the extreme ratio does not control the intermediate ratios. A candidate correction requires both endpoint tests for every t∈(1,b/a]; its sufficiency is not proved. Further integer-parameter violations, including (−2,0,4,−6) on [1,4] at (1,13/8,13/8), are computed numerical observations and are not formalized. Conjecture 2 for inf I=0 or sup I=∞, and the true bounded-interval description of Γn(I), are not settled by this result. The journal version's text is ASSUMED-UNVERIFIED; the quotations refer to arXiv:2408.07658v1, §4.

## References

- Truth anchor: `D5/S3/ArithSums/GiniMeanEndpointComparison.claim`
- Truth anchor: `D5/S3/ArithSums/GiniMeanEndpointComparison.giniMean`
- Truth anchor: `D5/S3/ArithSums/GiniMeanEndpointComparison.highTuple`
- Truth anchor: `D5/S3/ArithSums/GiniMeanEndpointComparison.lowTuple`
- Truth anchor: `D5/S3/ArithSums/GiniMeanEndpointComparison.result`
