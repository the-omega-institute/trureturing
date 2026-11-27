# Finite-Fiber Transportation in Commutative Monoids

## Abstract

Conical binary refinement is equivalent to exact transportation over every finite pair of fibers.

**Theorem 1.1 (The exact transportation equivalence).**

$$\forall K \in Type,\; [AddCommMonoid\left(K\right)], ((\forall x \in K,\; \forall y \in K,\; (x + y = 0) \Rightarrow ((x = 0) \land (y = 0))) \land (\forall a \in K,\; \forall b \in K,\; \forall c \in K,\; \forall d \in K,\; (a + b = c + d) \Rightarrow (\exists r \in K,\; \exists s \in K,\; \exists t \in K,\; \exists u \in K,\; (r + s = a) \land ((t + u = b) \land ((r + t = c) \land (s + u = d)))))) \Leftrightarrow (\forall A \in Type,\; \forall B \in Type,\; \forall Z \in Type,\; [Fintype\left(A\right)], [Fintype\left(B\right)], \forall f \in A \to Z,\; \forall g \in B \to Z,\; \forall p \in A \to K,\; \forall q \in B \to K,\; (\forall h \in Z,\; fiberSum\left(f, p, h\right) = fiberSum\left(g, q, h\right)) \Rightarrow (\exists m \in A \to B \to K,\; (\forall a \in A,\; \forall b \in B,\; (f\left(a\right) \ne g\left(b\right)) \Rightarrow (m\left(a, b\right) = 0)) \land ((\forall a \in A,\; \sum_{b \in B} m\left(a, b\right) = p\left(a\right)) \land (\forall b \in B,\; \sum_{a \in A} m\left(a, b\right) = q\left(b\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Transportation/FiniteFiberTransport.conical_refinement_iff_finite_fiber_transport` (`✓ std3`). ∎

*Citation.* Albert Atserias and Phokion G. Kolaitis (2025). *Consistency Witnesses for Annotated Relations*. DOI: [10.1145/3749116.3749118](https://doi.org/10.1145/3749116.3749118). URL: <https://sigmodrecord.org/publications/sigmodRecord/2506/pdfs/03_Principles_Atserias.pdf>.

*Commentary.*

K is any additive commutative monoid. Conicality means that x+y=0 implies x=0 and y=0. Binary refinement means that every equality a+b=c+d admits four entries r,s,t,u with r+s=a, t+u=b, r+t=c and s+u=d. These are exactly the two clauses on the left of the equivalence.

On the right, A and B range over all finite types, including empty types, and Z ranges over arbitrary types. The maps f:A to Z and g:B to Z and the weights p:A to K and q:B to K are arbitrary. In the formula, fiberSum(f,p,h) denotes the original finite sum of p(a) over all a with f(a)=h, equivalently the sum over A of p(a) when f(a)=h and zero otherwise. Sum notation always uses the given monoid addition and its zero.

If the two fiber sums agree for every h in Z, there exists one matrix m:A to B to K. It is zero whenever the labels disagree; every row sums to its prescribed p(a), and every column sums to its prescribed q(b). Equality is exact. No order, cancellation, multiplication, division, normalization, nonzero individual weight, nonempty carrier, nontrivial monoid or finite label type is required.

For the construction, binary refinement first splits a finite family into two families with prescribed totals. Induction on the row set then builds a matrix for any two equal finite totals. Conicality makes every term of a vanishing sum zero and supplies both empty-set base cases. For each label, apply this construction to the two families with all other labels replaced by zero. Choose a matrix for every label. The final entry in row a is taken from the matrix for f(a). A mismatched column of that matrix vanishes. For a fixed column b, each summand can therefore be compared with the matrix for g(b), yielding its exact column total. No sum over Z occurs.

Conversely, use two rows and no columns with a single label to force each summand of x+y=0 to vanish. Use two rows and two columns with a single label to obtain the four refinement entries. Universe lifts of the two-element and empty types preserve the quantified carrier universes.

The finite transportation theorem and fiberwise consistency construction are known results in Atserias and Kolaitis, Theorem 1 and Section 6. The formulation here also makes empty carriers and the converse conicality clause explicit. The Section 8 classification of monoids admitting largest-support witnesses remains a separate question; this theorem neither classifies such supports nor asserts uniqueness or pointwise maximality.

## References

- Truth anchor: `D5/S3/Combinatorics/Transportation/FiniteFiberTransport.conical_refinement_iff_finite_fiber_transport`
