# Weighted Legal-Path Temperley-Lieb Relations

## Abstract

Finite symmetric weighted legal paths carry the exact local Temperley-Lieb projections.

**Theorem 1.1 (Weighted path projections satisfy all four local relations).**

$$\begin{gathered}\forall L: \operatorname{Finite}, R: L \to L \to \operatorname{Prop},\ \operatorname{Symmetric}(R), d: L \to \mathbb{R}, 0<\Delta, \forall a\in L, 0<d_{a} \land \sum_{b: \operatorname{R}(a, b)} d_{b}=\Delta d_{a},\ \forall n\in\mathbb{N}, s, t\in L,\\\operatorname{let} \operatorname{LegalPath}(R, n, s, t): Type = \{x: \operatorname{Fin}(n+1) \to L | x\left(0\right) = s \land \left(x\left(n\right) = t \land \left(\forall k \in \operatorname{Fin}(n),\; R\left(x\left(k\right), x\left(k+1\right)\right)\right)\right)\}; \\\operatorname{let} P_{i}: \operatorname{Matrix}(\operatorname{LegalPath}(R, n, s, t), \operatorname{LegalPath}(R, n, s, t), \mathbb{C}), i\in \mathbb{N}, 1\le i<n, \forall x \in \operatorname{LegalPath}(R, n, s, t), y \in \operatorname{LegalPath}(R, n, s, t),\; P_{i}\left(x, y\right) = (\begin{cases}\operatorname{Complex.ofReal}(\frac{\sqrt{d\left(x\left(i\right)\right) \cdot d\left(y\left(i\right)\right)}}{\Delta \cdot d\left(x\left(i-1\right)\right)}) & \text{if} (\left(\forall k \in \operatorname{Fin}(n+1),\; k \ne i \Rightarrow x\left(k\right) = y\left(k\right)\right) \land x\left(i-1\right) = x\left(i+1\right))\\0 & \text{otherwise}\end{cases}); \\(\forall i, 1\le i<n \Rightarrow \operatorname{conjTranspose}(P_{i})=P_{i} \land P_{i}P_{i}=P_{i}) \land\\(\forall i, 1\le i, i+1<n \Rightarrow P_{i}P_{i+1}P_{i}=\Delta^{-2}P_{i}) \land\\(\forall i, j, 1\le i<n, 1\le j<n, i+2\le j \lor j+2\le i \Rightarrow P_{i}P_{j}=P_{j}P_{i}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb.weighted_legal_path_temperley_lieb` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let L be any finite label type and R a symmetric Boolean adjacency relation, including possible self-loops. Every label has a strictly positive real weight d, delta is strictly positive, and the sum of d(b) over R(a,b) equals delta times d(a) for every a. Fix any path length n and endpoints s,t. The path basis contains precisely the legal length-n paths from s to t and may be empty.

For every interior i, P_i(x,y) is zero unless x and y agree outside i and x at i-1 equals x at i+1. In the remaining case its literal FT.12 coefficient is the complex cast of sqrt(d(x_i) * d(y_i)) / (delta * d(x_(i-1))). This is the source's square root of the product, with no rescaling or normalization of P_i.

The theorem establishes self-adjointness and idempotence at every interior index, the forward adjacent triple product whenever i+1 is interior, and commutation for both ordered cases of distance at least two. Its local replacement equivalence identifies a legal fiber with the neighbors of its common flank; the proof also establishes the adjacent unique survivor and the distant locality argument. No nonempty path-space premise is used.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb.weighted_legal_path_temperley_lieb`
