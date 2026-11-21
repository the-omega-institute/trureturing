# Equality in the logarithmic parity modulus

## Abstract

At positive distance, affine parity recovery attains the logarithmic bound exactly below a strict threshold.

**Theorem 1.1 (Equality forces the threshold and a common offset).**

$$\begin{aligned}\forall (A: \operatorname{Type}),[\operatorname{AddCommGroup}(A)][\operatorname{Fintype}(A)],\\\operatorname{let} N:=\left|A\right|,\\(\forall (x: A),x+x=0) \land 1<N \longrightarrow\\\operatorname{let} \beta:=\frac{N-1}{N},\\\forall (I: \operatorname{Type}),[\operatorname{Fintype}(I)],\\\operatorname{let} R((c: I \to A), (s: A), (x: I \to \operatorname{Bool})):=s+\sum_{i}x_{i}c(i),\\\operatorname{let} L((c: I \to A), (s: A), (f: I \to \mathbb{R})):=y\mapsto\sum_{x\in (I \to \operatorname{Bool}):R(c, s, x)=y}\prod_{i}\frac{1+(-1)^{x_{i}}f(i)}{2},\\\operatorname{let} G((c: I \to A), (f: I \to \mathbb{R}), (a: A)):=\prod_{i:c(i)=a}f(i),\\\operatorname{let} m((P: A \to \mathbb{R}), (\psi: \operatorname{AddChar}(A, \mathbb{C}))):=\sum_{x \in A}P(x) \Re \psi(x),\\\forall (c: I \to A)(s: A)(t: A)(a: A)(f: I \to \mathbb{R})(g: I \to \mathbb{R})(e: \mathbb{R}),\\\operatorname{let} P:=L(c, s, f),\\\operatorname{let} Q:=L(c, t, g),\\\operatorname{let} \Delta:=\operatorname{TV}(P, Q),\\a\neq 0 \land (\exists (i: I),c(i)=a) \land 0<e \land\\(\forall (i: I),0<f(i)<1) \land (\forall (i: I),0<g(i)<1) \land (\forall (\psi: \operatorname{AddChar}(A, \mathbb{C})),e\le\left|m(P, \psi)\right| \land e\le\left|m(Q, \psi)\right|) \land\\0<\Delta \land \left|\log G(c, f, a)-\log G(c, g, a)\right|=2\beta \log (1+\frac{\Delta}{\beta e}) \longrightarrow\\e(1+\frac{\Delta}{\beta e})^{\frac{N}{2}}<1 \land s=t\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityLogModulusEquality.equality_requires_cutoff_and_offset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input-bit rates are (1-f(i))/2 and (1-g(i))/2. The two laws may start with distinct offsets. At positive distance, equality in strict Jensen forces a common nonzero moment displacement. Scalar equality fixes one magnitude at e and forces the two moments to have the same sign. Equality in the triangle inequality aligns their signed logarithmic differences. Inverting these complementary profiles yields the strict threshold because the target column is present and its factors lie in the open unit interval.

**Theorem 1.2 (The threshold admits an attaining pair).**

$$\begin{aligned}\forall (A: \operatorname{Type}),[\operatorname{AddCommGroup}(A)][\operatorname{Fintype}(A)],\\\operatorname{let} N:=\left|A\right|,\\(\forall (x: A),x+x=0) \land 1<N \longrightarrow\\\operatorname{let} \beta:=\frac{N-1}{N},\\\operatorname{let} I:=\{x\in A|x\neq 0\},\\\operatorname{let} R((c: I \to A), (s: A), (x: I \to \operatorname{Bool})):=s+\sum_{i}x_{i}c(i),\\\operatorname{let} L((c: I \to A), (s: A), (f: I \to \mathbb{R})):=y\mapsto\sum_{x\in (I \to \operatorname{Bool}):R(c, s, x)=y}\prod_{i}\frac{1+(-1)^{x_{i}}f(i)}{2},\\\operatorname{let} G((c: I \to A), (f: I \to \mathbb{R}), (a: A)):=\prod_{i:c(i)=a}f(i),\\\operatorname{let} m((P: A \to \mathbb{R}), (\psi: \operatorname{AddChar}(A, \mathbb{C}))):=\sum_{x \in A}P(x) \Re \psi(x),\\\operatorname{let} c:=x \mapsto x,\\\forall (a: A)(e: \mathbb{R})(\Delta: \mathbb{R}),a\neq 0 \land 0<e \land 0<\Delta \land e(1+\frac{\Delta}{\beta e})^{\frac{N}{2}}<1 \longrightarrow\\\exists (f: I \to \mathbb{R})(g: I \to \mathbb{R}),(\forall (i: I),0<f(i)<1) \land (\forall (i: I),0<g(i)<1) \land\\\operatorname{let} P:=L(c, 0, f),\\\operatorname{let} Q:=L(c, 0, g),\\(\forall (\psi: \operatorname{AddChar}(A, \mathbb{C})),e\le\left|m(P, \psi)\right| \land e\le\left|m(Q, \psi)\right|) \land \operatorname{TV}(P, Q)=\Delta \land\\\left|\log G(c, f, a)-\log G(c, g, a)\right|=2\beta \log (1+\frac{\Delta}{\beta e})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityLogModulusEquality.equality_criterion_sufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use one input bit per nonzero group element and use offset zero in both laws. The assigned log bias factors realize the complementary nontrivial moment profiles. Inverting their difference gives a point mass at the target minus the uniform mass, scaled by the common moment displacement. This computes the specified total variation and attains the bound.

## References

- Truth anchor: `D5/S3/TotalVariation/ParityLogModulusEquality.equality_criterion_sufficient`
- Truth anchor: `D5/S3/TotalVariation/ParityLogModulusEquality.equality_requires_cutoff_and_offset`
- Dependency: [D5/S3/TotalVariation/GroupedParityBias](GroupedParityBias.md)
- Dependency: [D5/S3/TotalVariation/ParityLogModulus](ParityLogModulus.md)
