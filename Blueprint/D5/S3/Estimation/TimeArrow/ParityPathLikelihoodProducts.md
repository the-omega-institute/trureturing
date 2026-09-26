# Inner Products of Parity-Kernel Path Likelihoods

## Abstract

Against the uniform product reference on hypercube paths, same-direction parity-kernel likelihoods have inner product (1 + E[a b])^s and opposite-direction likelihoods have inner product one.

**Definition 1.1 (Forward path likelihood).**

$$L_{a,+}(x)= \prod_{t<s} 2^{d} P_{a}(x_{t}, x_{t+1})$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.forwardLikelihood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a path x_0, ..., x_s of sign vectors and a real profile a, the forward likelihood of the parity kernel P_a against the uniform product reference is the product of 2^d P_a over the steps.

**Definition 1.2 (Backward path likelihood).**

$$L_{a,-}(x)= \prod_{t<s} 2^{d} P_{a}(x_{t+1}, x_{t})$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.backwardLikelihood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The backward likelihood uses every step in reverse; it is the likelihood of the time-reversed path law.

**Definition 1.3 (Uniform product reference).**

$$E_{U}[F]= (\frac{1}{2^{d}})^{s+1} \sum_{x} \operatorname{F}(x)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.uniformPathMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reference law makes the s + 1 states of a path independent and uniform on the hypercube. When |a| < 1 the forward and backward products are the likelihood ratios of the forward and time-reversed path laws of P_a against this reference; the identities below are stated for every real profile.

**Theorem 1.4 (Forward likelihoods: inner product).**

$$\sum_{y} \operatorname{a}(y)=0, \sum_{y} \operatorname{b}(y)=0 \Rightarrow E_{U}[L_{a,+} L_{b,+}]= (1+\frac{1}{2^{d}} \sum_{y} \operatorname{a}(y) \operatorname{b}(y))^{s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.forward_inner_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the profiles a and b both sum to zero over the hypercube, then for every number of steps s the forward likelihoods of P_a and P_b have uniform-reference inner product (1 + E[a b])^s, where E is the uniform average.

The step matrix M(x, y) = 2^d P_a(x, y) 2^d P_b(x, y) equals 1 + chi(y)(a(x) + b(x)) + a(x) b(x), because chi(y)^2 = 1. Hence every column of M sums to 2^d (1 + E[a b]). Summing the edge products over all paths, the first state is summed out against a column, and induction on s gives 2^d times the s-th power of the column sum; the uniform normalization then leaves (1 + E[a b])^s.

**Theorem 1.5 (Backward likelihoods: inner product).**

$$\sum_{y} \operatorname{a}(y)=0, \sum_{y} \operatorname{b}(y)=0 \Rightarrow E_{U}[L_{a,-} L_{b,-}]= (1+\frac{1}{2^{d}} \sum_{y} \operatorname{a}(y) \operatorname{b}(y))^{s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.backward_inner_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses the backward likelihoods have the same inner product. Now the reversed step matrix has constant row sums 2^d (1 + E[a b]), and the last state of the path is summed out at each induction step.

**Theorem 1.6 (Opposite directions are orthogonal after centering).**

$$d\geq 1, \sum_{y} \operatorname{b}(y)=0, \sum_{y} \operatorname{chi}(y) \operatorname{b}(y)=0 \Rightarrow E_{U}[L_{a,+} L_{b,-}]=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.forward_backward_inner_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d >= 1. If the profile b sums to zero and chi b sums to zero, then for every profile a and every s the forward likelihood of P_a and the backward likelihood of P_b have inner product one. Since each likelihood has reference mean one, the centered forward and backward likelihoods are orthogonal.

The step matrix H(x, y) = 2^d P_a(x, y) 2^d P_b(y, x) has row sums 4^d (P_a P_b)(x, x) = 2^d, because the two-step product P_a P_b is the uniform kernel for such b. Summing out the last state at each step gives 2^d (2^d)^s, which the uniform normalization turns into one.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.backwardLikelihood`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.backward_inner_product`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.forwardLikelihood`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.forward_backward_inner_product`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.forward_inner_product`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ParityPathLikelihoodProducts.uniformPathMean`
- Dependency: [D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates](ParityKernelSubcoordinates.md)
