# Sharp Scalar Fidelity Endpoint Comparison

## Abstract

A sharp scalar condition characterizes dominance of the fidelity quotient over every independent upper endpoint in the unit cube.

**Definition 1.1 (The scalar quotient).**

$$\forall a,b,c \in \mathbb{R},\quad\operatorname{g}\left(a, b, c\right)=\frac{a^{2}+b^{2}+c^{2}-1}{2ab}$$

*Formalization.* `D5/S3/Quantum/ScalarFidelityEndpoint.scalarQuotient` (`✓ std3`).

*Citation.* Reza Rajaei (2026). *Generalized Fidelity and the Data Processing Inequality*. URL: <https://arxiv.org/html/2609.09753v1>.

*Commentary.*

For real a,b,c, scalarQuotient(a,b,c), denoted by g(a,b,c), is (a squared+b squared+c squared-1)/(2ab). The theorem uses strictly positive a and b, so its denominators are positive. Rajaei's qubit identity motivates this scalar expression; the scalar definition itself imposes no matrix realization.

**Theorem 1.2 (Exact lower-corner dominance).**

$$\forall a,b,c \in \mathbb{R},\quad0<a\le1,\ 0<b\le1,\ 0\le c\le1 \Rightarrow ((\forall A,B,C \in \mathbb{R},\ a\le A\le1 \land b\le B\le1 \land c\le C\le1 \Rightarrow \operatorname{g}\left(a, b, c\right)\le\operatorname{g}\left(A, B, C\right)) \Leftrightarrow \left|a^{2}-b^{2}\right|\le1-c^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ScalarFidelityEndpoint.lower_corner_dominance_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Reza Rajaei (2026). *Generalized Fidelity and the Data Processing Inequality*. URL: <https://arxiv.org/html/2609.09753v1>.

*Commentary.*

For every base point with 0<a,b<=1 and 0<=c<=1, the displayed equivalence includes both directions and all closed upper endpoints. The upper endpoints vary independently. Neither the endpoint nor any intervening point is required to satisfy the squared-imbalance condition. The sharp scalar argument is due to Haobo Ma and Wenlin Zhang in their corrected note, Monotonicity of the qubit fidelity quotient and fixed-reference convexity. Rajaei's Corollaries 5 and 6 supply the earlier sufficient criteria.

For sufficiency put d=1-c squared, x=A-a and y=B-b. Clearing the positive denominators gives the nonnegative expression below. The condition bounds both signed squared differences by d and also bounds (a-b) squared by d. Increasing c to C adds a nonnegative contribution because 0<=c<=C.

$\forall a,b,c,A,B,x,y,d \in \mathbb{R},\quad(x=A-a \land y=B-b \land d=1-c^{2}) \Rightarrow ab(A^{2}+B^{2}+c^{2}-1)-AB(a^{2}+b^{2}+c^{2}-1)=bx(a^{2}-b^{2}+d)+ay(b^{2}-a^{2}+d)+ab(x-y)^{2}+(d-(a-b)^{2})xy$

For necessity, if b squared-a squared exceeds 1-c squared, choose s=sqrt(b squared+c squared-1). Then a<s<=1, and the difference after increasing a to s has numerator -bs(s-a) squared after multiplication by positive denominators. It is strictly negative. Interchanging a and b gives the other signed bound. This proves the sharpness at the lower corner, including c=0 and c=1. It does not characterize physical channel realizability, prove a matrix fidelity bridge, or classify CPTP maps.

## References

- Truth anchor: `D5/S3/Quantum/ScalarFidelityEndpoint.lower_corner_dominance_iff`
- Truth anchor: `D5/S3/Quantum/ScalarFidelityEndpoint.scalarQuotient`
