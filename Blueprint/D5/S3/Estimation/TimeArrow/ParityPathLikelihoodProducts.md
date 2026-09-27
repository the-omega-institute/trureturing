# Inner Products of Parity-Kernel Path Likelihoods

## Abstract

Against the uniform product reference on hypercube paths, same-direction parity-kernel path products have inner product (1 + E[a b])^s and opposite-direction path products have inner product one; for profiles with |a| < 1 these products are the path likelihood ratios.

**Definition 1.1 (Forward path product).**

$$L_{a,+}(x)= \prod_{t<s} 2^{d} P_{a}(x_{t}, x_{t+1})$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.forwardLikelihood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a path x_0, ..., x_s of sign vectors and a real profile a, the forward product of the parity kernel P_a is the product of 2^d P_a over the steps; for |a| < 1 it is the likelihood ratio of the forward path law against the uniform product reference.

**Definition 1.2 (Backward path product).**

$$L_{a,-}(x)= \prod_{t<s} 2^{d} P_{a}(x_{t+1}, x_{t})$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.backwardLikelihood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The backward product uses every step in reverse; for |a| < 1 it is the likelihood ratio of the time-reversed path law.

**Definition 1.3 (Uniform product reference).**

$$E_{U}[F]= (\frac{1}{2^{d}})^{s+1} \sum_{x} \operatorname{F}(x)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.uniformPathMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reference law makes the s + 1 states of a path independent and uniform on the hypercube. When |a| < 1 the forward and backward products are the likelihood ratios of the forward and time-reversed path laws of P_a against this reference; the identities below are stated for every real profile.

**Theorem 1.4 (Forward products: inner product).**

$$\sum_{y} \operatorname{a}(y)=0, \sum_{y} \operatorname{b}(y)=0 \Rightarrow E_{U}[L_{a,+} L_{b,+}]= (1+\frac{1}{2^{d}} \sum_{y} \operatorname{a}(y) \operatorname{b}(y))^{s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.forward_inner_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the profiles a and b both sum to zero over the hypercube, then for every number of steps s the forward products of P_a and P_b have uniform-reference inner product (1 + E[a b])^s, where E is the uniform average.

The step matrix M(x, y) = 2^d P_a(x, y) 2^d P_b(x, y) equals 1 + chi(y)(a(x) + b(x)) + a(x) b(x), because chi(y)^2 = 1. Hence every column of M sums to 2^d (1 + E[a b]). Summing the edge products over all paths, the first state is summed out against a column, and induction on s gives 2^d times the s-th power of the column sum; the uniform normalization then leaves (1 + E[a b])^s.

**Theorem 1.5 (Backward products: inner product).**

$$\sum_{y} \operatorname{a}(y)=0, \sum_{y} \operatorname{b}(y)=0 \Rightarrow E_{U}[L_{a,-} L_{b,-}]= (1+\frac{1}{2^{d}} \sum_{y} \operatorname{a}(y) \operatorname{b}(y))^{s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.backward_inner_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses the backward products have the same inner product. Now the reversed step matrix has constant row sums 2^d (1 + E[a b]), and the last state of the path is summed out at each induction step.

**Theorem 1.6 (Opposite directions are orthogonal after centering).**

$$d\geq 1, \sum_{y} \operatorname{b}(y)=0, \sum_{y} \operatorname{chi}(y) \operatorname{b}(y)=0 \Rightarrow E_{U}[L_{a,+} L_{b,-}]=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.forward_backward_inner_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d >= 1. If the profile b sums to zero and chi b sums to zero, then for every profile a and every s the forward product of P_a and the backward product of P_b have inner product one. Each product has reference mean one, so the centered forward and backward products are orthogonal; for |a|, |b| < 1 these are the centered likelihood ratios of the two time directions.

The step matrix H(x, y) = 2^d P_a(x, y) 2^d P_b(y, x) has row sums 4^d (P_a P_b)(x, x) = 2^d: expanding the product, the parity sum vanishes (it is the record weight of the empty coordinate set) and the two remaining sums vanish by hypothesis. Summing out the last state at each step gives 2^d (2^d)^s, which the uniform normalization turns into one.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.backwardLikelihood`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.backward_inner_product`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.forwardLikelihood`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.forward_backward_inner_product`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.forward_inner_product`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.uniformPathMean`
- Dependency: [D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates](ParityKernelSubcoordinates.md)
