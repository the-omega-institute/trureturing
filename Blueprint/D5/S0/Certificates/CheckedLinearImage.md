# Checked Linear Query Images

## Abstract

Executable rational certificates determine complete real query images.

**Theorem 1.1 (Accepted endpoint data determine every real target).**

$$\begin{aligned}\forall C,V, \operatorname{Fintype}\left(C\right)\land \operatorname{Fintype}\left(V\right) \Rightarrow \forall A:C\to V\to \mathbb{Q}, b:C\to \mathbb{Q}, c:V\to \mathbb{Q}, p:\operatorname{RawSharpPayload}\left(C, V\right),\\\operatorname{checkSharp}\left(A, b, c, p\right)=true \Rightarrow\\\operatorname{RealQueryImage}\left(A, b, c\right)=\operatorname{Icc}\left(\operatorname{castReal}\left(\operatorname{lower}\left(p\right)\right), \operatorname{castReal}\left(\operatorname{upper}\left(p\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/CheckedLinearImage.checked_real_query_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

C and V are arbitrary finite types, including empty types. A is a rational C-by-V matrix, b is a rational C-vector, c is a rational V-vector, and p is a RawSharpPayload C V. The only additional premise is that checkSharp accepts these exact inputs.

The payload contains two rational endpoint values, two rational primal vectors, and two rational multiplier vectors, with no proof fields. The checker tests multiplier nonnegativity, column identities for c and minus c, weighted right-hand-side bounds, both primal feasibility conditions, and both objective equalities.

RealQueryImage(A,b,c) denotes the set of sums of c(j)x(j), after casting rational coefficients to the reals, for all real vectors x satisfying every cast row inequality. The theorem includes irrational targets and coincident endpoints. No separate convexity or nonemptiness hypothesis is imposed: mathlib's convex halfspaces and linear images supply it.

The underlying checked_query_image theorem works over any field K with a linear order and IsStrictOrderedRing K. This is certificate soundness, not an optimizer or a certificate-existence theorem.

**Theorem 1.2 (Accepted Farkas data exclude all field-valued solutions).**

$$\begin{aligned}\forall K, \operatorname{Field}\left(K\right)\land\operatorname{LinearOrder}\left(K\right)\land\operatorname{IsStrictOrderedRing}\left(K\right) \Rightarrow\\\forall C,V, \operatorname{Fintype}\left(C\right)\land \operatorname{Fintype}\left(V\right) \Rightarrow \forall A:C\to V\to \mathbb{Q}, b:C\to \mathbb{Q}, y:C\to \mathbb{Q},\\\operatorname{checkFarkas}\left(A, b, y\right)=true \Rightarrow\neg\exists x:V\to K, \operatorname{FeasibleK}\left(A, b, x\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/CheckedLinearImage.checked_infeasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

K is a field with a linear order and IsStrictOrderedRing K; C and V are arbitrary finite types. A, b, and y have rational entries. checkFarkas requires nonnegative y, zero weighted coefficients in every column, and a strictly negative weighted right-hand side.

FeasibleK(A,b,x) means that, for every row i, the sum of the cast coefficient A(i,j) times x(j) is at most the cast b(i). Acceptance excludes every such K-valued x. The rational companion theorem constructs the existing RationalFarkas.Certificate and invokes RationalFarkas.infeasible_of_certificate.

## References

- Truth anchor: `D5/S0/Certificates/CheckedLinearImage.checked_infeasible`
- Truth anchor: `D5/S0/Certificates/CheckedLinearImage.checked_real_query_image`
- Dependency: [D5/S0/Certificates/RationalFarkas](RationalFarkas.md)
