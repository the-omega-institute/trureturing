# Grouped biases of an affine parity law

## Abstract

Bias recovery for independent binary inputs under a fixed affine readout.

**Theorem 1.1 (The output law determines the bias product of each nonzero column).**

$$\begin{aligned}\forall (A: \operatorname{Type})(I: \operatorname{Type}),\\{}[\operatorname{AddCommGroup}(A)][\operatorname{Fintype}(A)][\operatorname{Fintype}(I)],\\(c: I \to A)(s: A),(\forall (x: A),x+x=0) \longrightarrow\\\operatorname{let} Y((x: I \to \operatorname{Bool})):=s+\sum_{i}x_{i}c(i),\\\operatorname{let} L((q: I \to \mathbb{R}),(y: A)):=\sum_{x \in (I \to \operatorname{Bool}): Y(x)=y}\prod_{i}\frac{1+(-1)^{x_{i}}q(i)}{2},\\\operatorname{let} v((\psi: \operatorname{AddChar}(A,\mathbb{C})),(a: A)):=\Re \psi(a),\\\operatorname{let} G((q: I \to \mathbb{R}),(a: A)):=\prod_{i: c(i)=a}q(i),\\\operatorname{let} m((q: I \to \mathbb{R}),(\psi: \operatorname{AddChar}(A,\mathbb{C}))):=\sum_{y \in A}L(q,y)v(\psi,y),\\\forall (q: I \to \mathbb{R})(r: I \to \mathbb{R}),(\forall (i: I),0<q(i)<1) \land (\forall (i: I),0<r(i)<1) \longrightarrow\\((\forall (y: A),L(q,y)=L(r,y)) \Leftrightarrow \forall (a: A),a \neq 0 \implies G(q,a)=G(r,a)) \land\\\forall (a: A),a \neq 0 \implies \log G(q,a)=\frac{-2}{\left|A\right|}\sum_{\psi \in \operatorname{AddChar}(A,\mathbb{C})}v(\psi,a) \log \left|m(q,\psi)\right|\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/GroupedParityBias.affine_law_iff_grouped_bias` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite additive group A satisfies x+x=0 for every x. The column map c and the affine offset s are fixed. A bias factor q(i) in (0,1) corresponds to input probability (1-q(i))/2. The mass L(q,y) is the pushforward of the independent input product by the affine readout. The product G(q,a) collects the bias factors of columns equal to a. Two laws agree exactly when these products agree for every nonzero a. The explicit recovery formula takes logarithms of absolute sign moments, so the recovered products do not depend on the offset sign. For section 35.6.8 in Quantum Geometry, take A to be the quotient by the fair-input image. Each c(i) is the projected column of a biased input and s is the projected offset. In Y, the contribution of c(i) is zero when x(i) is false and c(i) when x(i) is true.

**Theorem 1.2 (Individual identifiability of bias factors).**

$$\begin{aligned}\forall (A: \operatorname{Type})(I: \operatorname{Type}),\\{}[\operatorname{AddCommGroup}(A)][\operatorname{Finite}(A)][\operatorname{Fintype}(I)],\\(c: I \to A)(s: A),(\forall (x: A),x+x=0) \longrightarrow\\\operatorname{let} Y((x: I \to \operatorname{Bool})):=s+\sum_{i}x_{i}c(i),\\\operatorname{let} L((q: I \to \mathbb{R}),(y: A)):=\sum_{x \in (I \to \operatorname{Bool}): Y(x)=y}\prod_{i}\frac{1+(-1)^{x_{i}}q(i)}{2},\\\operatorname{InjOn}(L,\{q|(\forall (i: I),0<q(i)<1)\}) \Leftrightarrow (\forall (i: I),c(i) \neq 0) \land \operatorname{Injective}(c)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/GroupedParityBias.affine_bias_identifiable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the open interval of bias factors, the map from parameter vectors to laws is injective exactly when every column is nonzero and c is injective. With a zero column, changing the factor of that column keeps the law. For two equal columns, moving a factor of one third between their indices keeps the group product when all other factors are one half. With distinct nonzero columns every group product contains exactly the factor of its own input.

## References

- Truth anchor: `D5/S3/TotalVariation/GroupedParityBias.affine_bias_identifiable_iff`
- Truth anchor: `D5/S3/TotalVariation/GroupedParityBias.affine_law_iff_grouped_bias`
- Dependency: [D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift](Equality/FiberwiseEqualDistanceLift.md)
