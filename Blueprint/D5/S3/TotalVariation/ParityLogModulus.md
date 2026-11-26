# Finite-distance stability of logarithmic parity recovery

## Abstract

Averaging the nontrivial sign moments gives a logarithmic stability bound at finite distance.

**Theorem 1.1 (Logarithmic modulus of the parity coefficient).**

$$\begin{aligned}\forall (A: \operatorname{Type}),[\operatorname{AddCommGroup}(A)][\operatorname{Fintype}(A)],\\(\forall (x: A),x+x=0) \land 1<\left|A\right| \longrightarrow\\\operatorname{let} s((\psi: \operatorname{AddChar}(A, \mathbb{C})), (x: A)):=\Re \psi(x),\\\operatorname{let} m((f: A \to \mathbb{R}), (\psi: \operatorname{AddChar}(A, \mathbb{C}))):=\sum_{x \in A}f(x)s(\psi, x),\\\operatorname{let} L((a: A), (f: A \to \mathbb{R})):=\frac{-2}{\left|A\right|}\sum_{\psi \in \operatorname{AddChar}(A, \mathbb{C})}s(\psi, a) \log \left|m(f, \psi)\right|,\\\operatorname{let} \beta:=\frac{\left|A\right|-1}{\left|A\right|},\\\forall (p: A \to \mathbb{R})(q: A \to \mathbb{R})(a: A)(e: \mathbb{R}),0<e \land \sum_{x \in A}p(x)=\sum_{x \in A}q(x) \land\\(\forall (\psi: \operatorname{AddChar}(A, \mathbb{C})),e\le\left|m(p, \psi)\right| \land e\le\left|m(q, \psi)\right|) \longrightarrow\\\left|L(a, p)-L(a, q)\right|\le2\beta \log (1+\frac{\operatorname{TV}(p, q)}{\beta e})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityLogModulus.log_parity_coefficient_modulus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed sum of moment differences is an expectation difference. Equal mass and character orthogonality bound its absolute value by the order of the group times total variation. The trivial character contributes zero. Logarithm concavity on the other characters gives the finite-distance estimate. In Quantum Geometry section 35.6.8, apply it on the quotient by the fair-input image to the log bias product of a nonzero projected column.

## References

- Truth anchor: `D5/S3/TotalVariation/ParityLogModulus.log_parity_coefficient_modulus`
- Dependency: [D5/S3/TotalVariation/ParityLogStability](ParityLogStability.md)
