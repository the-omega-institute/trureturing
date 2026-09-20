# The shared mixed-coordinate comparison

## Abstract

Mixed-coordinate monotonicity for the exact six-variable hyper-ideal cosine.

All variables below are real numbers. Icc(a,b) denotes the closed interval [a,b]. In the local edge order (12,13,14,34,24,23), the inputs (x,y,z,o,v,w) keep all six coordinates independent. Coordinates x and o are opposite.

Define rad(x,y,z)=2xyz+x^2+y^2+z^2-1 and P(x,y,z,o,v,w)=yz+vw+xyv+xzw-(x^2-1)o. The function cosine is P divided first by sqrt(rad(x,y,w)) and then by sqrt(rad(x,z,v)). This is the actual formula in Zhao, arXiv:2601.15174v2, Lemma 2.2. Both radicands are proved positive on the box.

**Theorem 1.1 (Increasing neighbours and decreasing the opposite coordinate).**

$$\forall x \in \mathrm{Real}, y \in \mathrm{Real}, z \in \mathrm{Real}, o \in \mathrm{Real}, v \in \mathrm{Real}, w \in \mathrm{Real}, Y \in \mathrm{Real}, Z \in \mathrm{Real}, O \in \mathrm{Real}, V \in \mathrm{Real}, W \in \mathrm{Real},\; \left(x \in Icc\left(1, 2\right) \land \left(y \in Icc\left(1, 2\right) \land \left(z \in Icc\left(1, 2\right) \land \left(o \in Icc\left(1, 2\right) \land \left(v \in Icc\left(1, 2\right) \land \left(w \in Icc\left(1, 2\right) \land \left(Y \in Icc\left(1, 2\right) \land \left(Z \in Icc\left(1, 2\right) \land \left(O \in Icc\left(1, 2\right) \land \left(V \in Icc\left(1, 2\right) \land \left(W \in Icc\left(1, 2\right) \land \left(y \le Y \land \left(z \le Z \land \left(O \le o \land \left(v \le V \land w \le W\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow cosine\left(x, y, z, o, v, w\right) \le cosine\left(x, Y, Z, O, V, W\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FourCycleEnvelopes.cosine_mixed_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All eleven variables lie in [1,2]. Increasing the four neighbouring coordinates and decreasing the opposite coordinate cannot decrease the actual cosine. The proof differentiates the original square-root expression and derives the nonnegative coupled numerator (x^2-1)(xow+xv+yo+yvw+z(1-w^2)). It retains endpoint continuity, positive denominators and the two actual tetrahedral symmetries.

Endpoint envelopes used by later incidence arguments are obtained there by direct specialization and normalization. They are not separate formal declarations. Geometric identification with a tetrahedron, face-pairing topology and the global co-volume existence argument remain outside this analytic theorem.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FourCycleEnvelopes.cosine_mixed_comparison`
