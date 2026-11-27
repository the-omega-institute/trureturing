# Regular Mayer–Vietoris Transportation

## Abstract

Under regularity, conicality and the three idempotent-component laws characterize exact finite-fiber transportation.

**Theorem 1.1 (The exact transportation equivalence).**

$$\forall K \in Type,\; [AddCommMonoid\left(K\right)], (\forall x \in K,\; \exists y \in K,\; x + y + x = x) \Rightarrow (((\forall x \in K,\; \forall y \in K,\; (x + y = 0) \Rightarrow ((x = 0) \land (y = 0))) \land ((\forall a \in K,\; \forall b \in K,\; \forall c \in K,\; \forall d \in K,\; ((I\left(a\right)) \land ((I\left(b\right)) \land ((I\left(c\right)) \land ((I\left(d\right)) \land (a + b = c + d))))) \Rightarrow (\exists r \in K,\; \exists s \in K,\; \exists t \in K,\; \exists u \in K,\; (I\left(r\right)) \land ((I\left(s\right)) \land ((I\left(t\right)) \land ((I\left(u\right)) \land ((r + s = a) \land ((t + u = b) \land ((r + t = c) \land (s + u = d))))))))) \land ((\forall a \in K,\; \forall b \in K,\; ((I\left(a\right)) \land (I\left(b\right))) \Rightarrow (\forall x \in K,\; (C\left(a + b, x\right)) \Leftrightarrow (\exists u \in K,\; \exists v \in K,\; (C\left(a, u\right)) \land ((C\left(b, v\right)) \land (u + v = x))))) \land (\forall a \in K,\; \forall b \in K,\; \forall u \in K,\; \forall v \in K,\; ((I\left(a\right)) \land ((I\left(b\right)) \land ((C\left(a, u\right)) \land ((C\left(b, v\right)) \land (u + b = v + a))))) \Rightarrow (\exists w \in K,\; (w + a = u) \land (w + b = v)))))) \Leftrightarrow (\forall A \in Type,\; \forall B \in Type,\; \forall Z \in Type,\; [Fintype\left(A\right)], [Fintype\left(B\right)], \forall f \in A \to Z,\; \forall g \in B \to Z,\; \forall p \in A \to K,\; \forall q \in B \to K,\; (\forall h \in Z,\; fiberSum\left(f, p, h\right) = fiberSum\left(g, q, h\right)) \Rightarrow (\exists m \in A \to B \to K,\; (\forall a \in A,\; \forall b \in B,\; (f\left(a\right) \ne g\left(b\right)) \Rightarrow (m\left(a, b\right) = 0)) \land ((\forall a \in A,\; \sum_{b \in B} m\left(a, b\right) = p\left(a\right)) \land (\forall b \in B,\; \sum_{a \in A} m\left(a, b\right) = q\left(b\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Transportation/RegularMayerVietoris.regular_mvp_iff_finite_fiber_transport` (`✓ std3`). ∎

*Citation.* K. R. Goodearl; E. Pardo; F. Wehrung (2004). *Semilattices of Groups and Inductive Limits of Cuntz Algebras*. URL: <https://arxiv.org/pdf/math/0408072v1>.

*Commentary.*

K is an arbitrary AddCommMonoid satisfying regularity: for every x there is y with x+y+x=x. Write I(e) for e+e=e, L(x,y) for existence of t with x+t=y, and C(e,x) for L(e,x) and L(x,e). I and C in the displayed formula abbreviate precisely these definitions. No ambient order is used, and the component identity e need not be the global zero.

The left side has four clauses: conicality; refinement of any equality between sums of two idempotents into four idempotent entries; C(e+f,x) exactly when x decomposes into a representative of the e-component plus one of the f-component; and a common lift w of u and v whenever C(e,u), C(f,v), and u+f=v+e. Distributivity here means idempotent refinement and does not require meets.

The right side quantifies over independently universed finite types A and B, including empty types, and an arbitrary type Z. fiberSum(f,p,h) means the sum over A of p(a) if f(a)=h and zero otherwise. A matrix in the original K is zero on mismatched labels and has every prescribed row and column sum. There is no finite K, cancellation, multiplication, normalization, nonempty carrier, nontriviality, embedding, or purity premise.

Goodearl, Pardo and Wehrung, Lemma 2.1, supply the regular component construction; Theorem 3.2 supplies the refinement classification. Necessity takes the idempotent identities of refinement entries, offsets a refinement of x plus its internal inverse to obtain component-sum surjectivity, and adds the inverse of the lower-right entry to the upper-left entry to obtain a common lift. Sufficiency refines the four component identities, decomposes each row, forms the column defects, and lifts their compatible pair. Splitting that lift under the two row identities gives two row corrections. Their internal inverses correct the first column and the corrections themselves correct the second column, preserving both rows.

Closure of idempotent sums is supplied directly by the pinned Mathlib theorem IsIdempotentElem.mul on Multiplicative K. This type tag changes the notation for the same operation; both the component proof and the final matrix equalities remain in the original additive monoid.

A concrete coefficient example is Additive (WithOne (Multiplicative (ZMod 2))), the two-element additive group with a new global identity adjoined. It has three elements: global zero, an embedded local identity e, and an element x with e nonzero, e+x=x, x+x=e, and x+x distinct from x. It is regular, conical, and has binary refinement, so the criterion gives finite-fiber transportation. In contrast, ZMod 2 itself is regular but is not conical: two weights equal to one sum to zero. On a two-element source and an empty target with constant label, fiber totals agree but every matrix row sums to zero, so those nonzero marginals cannot be transported.

The predecessor exact transportation equivalence is applied directly to this refinement construction and conicality. The result is an acquisition of the published classification and its transportation consequence. It does not settle the separate largest-support classification problem and makes no mathematical originality claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Transportation/RegularMayerVietoris.regular_mvp_iff_finite_fiber_transport`
- Dependency: [D5/S3/Combinatorics/Transportation/FiniteFiberTransport](FiniteFiberTransport.md)
