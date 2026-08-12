# Finite Renyi Divergence

## Abstract

Finite Renyi divergence is defined for real orders and pinned by complementary half-order, self, and order-two identities.

**Definition 1.1 (Finite Renyi divergence is the logarithmic power sum).**

Lean statement: `D5/S3/RenyiDivergence/Basic.renyiDivergence`

*Formalization.* `D5/S3/RenyiDivergence/Basic.renyiDivergence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The repository already contains Kullback--Leibler divergence, the Bhattacharyya coefficient, and squared Hellinger distance as separate objects. The Renyi family places them in a common order parameter: order one half is the Bhattacharyya coefficient in logarithmic form, and hence is linked to squared Hellinger distance through the existing affinity identity, while the order-one limit is the classical divergence. This module introduces the finite family and proves the half-order bridge exactly.

The order-one limit is not attempted. Establishing it requires a genuine limiting argument, so the present theorem set does not complete the unification suggested by the family.

The definition is total. Lean totalizes real division, real powers at zero, and the logarithm at zero, and the order condition alpha != 1 therefore belongs to results that interpret the expression as a genuine Renyi divergence rather than to the data of the definition. Requiring a proof of alpha != 1 in the definition would alter every downstream signature; the interpreting theorems already constrain the order where that constraint is mathematically needed.

**Theorem 1.2 (Half order is minus twice log Bhattacharyya).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\(\forall i, 0\le p(i)) \Rightarrow\\D_{\frac{1}{2}}(p\Vert \Vert q)=-2 \log (\operatorname{BC}(p, q)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/Basic.renyi_divergence_one_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At order one half both powers are square roots. Pointwise nonnegativity of p is exactly the hypothesis used to combine them into the frozen Bhattacharyya coefficient; no normalization, absolute continuity, or nonnegativity assumption on q occurs in the theorem.

The pinning argument is a coverage analysis: three corruptions were hunted across three probes because no single identity observes every part of the definition. Dropping the prefactor is detected here: on the Bool point-mass-versus-uniform witness, the corrupted value is -log(2)/2 rather than the correct log(2). That corruption nevertheless survives self-divergence, where log(1) already forces zero. The order-two witness cannot detect it either, since the correct prefactor 1/(alpha-1) equals one at alpha = 2.

Swapping p and q in the two exponents exposes the complementary gap. It survives the half-order bridge pointwise, because both exponents are one half, and it also survives self-divergence. The order-two probe alone separates the forms, returning -2 log(2) for the swapped expression against the correct log(2).

Replacing the exponent 1-alpha by alpha also survives the half-order witness, but a uniform self-distribution at order two gives -3 log(2) instead of zero. Thus a pinning identity can have a symmetry blind spot: the half-order bridge is structurally incapable of detecting an exponent swap. The order-two evaluation is therefore a necessary second probe at a different order, not a decorative example. The caller independently verified this blind spot.

**Theorem 1.3 (Probability mass has zero self-divergence).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall \alpha \in \mathbb{R},\\\forall p: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum _{i} p(i)=1) \Rightarrow\\D_{\alpha }(p\Vert \Vert p)=0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/Basic.renyi_divergence_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonnegative normalized mass, the two powers recombine to p(i), so the power sum is one and its logarithm vanishes. This is the self probe used in the coverage analysis: at order two on the uniform Bool law it rejects the alpha-in-both-exponents corruption.

The theorem is stated for every real order because it is an identity of the totalized formula. In particular, its alpha = 1 instance records Lean's totalized value and is not an order-one limiting theorem. The identical inputs have identical support, while nonnegativity and unit mass ensure that the common support is nonempty.

**Theorem 1.4 (Point versus uniform has order-two divergence log two).**

$$\begin{gathered}p=\Delta_{\operatorname{true}}, q=u_{\operatorname{Bool}},\\D_{2}(p\Vert \Vert q)=\log 2.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/Basic.renyi_divergence_two_point_order_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete Bool witness takes p to be the point mass at true and q to be uniform. At order two the correct power sum is two, and the prefactor is one, giving log(2). The reference law q is positive on both points, so this evaluation lies in the finite-support regime rather than relying on a zero denominator convention.

Together with the half-order bridge and self-divergence, this evaluation closes the coverage analysis. It supplies the distinct order needed to break the exponent-swap symmetry that order one half cannot observe, while its prefactor equal to one explains precisely why it cannot test the presence of that prefactor.

**Theorem 1.5 (Finite Renyi divergence is nonnegative below order one).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall \alpha \in \mathbb{R}, 0<\alpha <1,\\\forall p, q: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum _{i} p(i)=1) \land\\((\forall i, 0\le q(i)) \land \sum _{i} q(i)=1) \land\\(\forall i, q(i)=0 \Rightarrow p(i)=0)) \Rightarrow\\0\le D_{\alpha }(p\Vert \Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/Basic.renyi_divergence_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0 < alpha < 1 and two nonnegative normalized laws, weighted arithmetic--geometric mean bounds the power sum above by one. Its logarithm is therefore nonpositive, while 1/(alpha-1) is nonpositive, and their product is nonnegative.

This result additionally assumes discrete absolute continuity in the direction q(i) = 0 implies p(i) = 0. Since p has unit mass, that support condition supplies a coordinate on which both laws are positive and thereby makes the power sum strictly positive. It is exactly the hypothesis that excludes the disjoint-support flattening recorded below.

**Theorem 1.6 (Disjoint support is flattened by totalization).**

$$\begin{gathered}p=\Delta_{\operatorname{true}}, q=\Delta_{\operatorname{false}},\\D_{\frac{1}{2}}(p\Vert \Vert q)=0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/RenyiDivergence/Basic.renyi_divergence_disjoint_support_flattening_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two point masses are nonnegative and normalized but have disjoint supports. They violate the absolute-continuity hypothesis q(i) = 0 implies p(i) = 0 at true. At order one half every term in the power sum vanishes, and Lean's Real.log(0) = 0 together with its Real.rpow conventions returns zero.

Mathematically the divergence is infinite in this case. The displayed zero is a convention-induced flattening, not a mathematical claim about disjoint probability laws. This qualification is itself frozen as a theorem beside the finite results, so it cannot be mistaken for an informal warning detached from the module it limits.

The half-order bridge carries only nonnegativity of p and remains an algebraic identity under the same totalized conventions. Self-divergence carries a nonnegative normalized p with coincident support; the general nonnegativity theorem carries both probability hypotheses, strict order bounds, and absolute continuity; and the order-two point-versus-uniform witness has an everywhere-positive q. These distinct support hypotheses separate genuine finite interpretations from the frozen flattened boundary value.

This module opens the S3 RenyiDivergence bucket as the address for finite Renyi divergences of real order alpha, their pinning identities, and future monotonicity in the order. No order-one limit, monotonicity in alpha, data-processing inequality for the family, or measure-theoretic analogue is claimed. All logarithms are natural, so the units are nats.

## References

- Truth anchor: `D5/S3/RenyiDivergence/Basic.renyiDivergence`
- Truth anchor: `D5/S3/RenyiDivergence/Basic.renyi_divergence_disjoint_support_flattening_witness`
- Truth anchor: `D5/S3/RenyiDivergence/Basic.renyi_divergence_nonneg`
- Truth anchor: `D5/S3/RenyiDivergence/Basic.renyi_divergence_one_half`
- Truth anchor: `D5/S3/RenyiDivergence/Basic.renyi_divergence_self`
- Truth anchor: `D5/S3/RenyiDivergence/Basic.renyi_divergence_two_point_order_two`
- Dependency: [D5/S3/TotalVariation/Bhattacharyya](../TotalVariation/Bhattacharyya.md)
