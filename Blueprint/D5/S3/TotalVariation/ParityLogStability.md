# Sharp stability of logarithmic parity recovery

## Abstract

A common positive floor for absolute sign moments gives a sharp total-variation bound.

**Theorem 1.1 (Stability of the log parity coefficient).**

$$\begin{aligned}\forall (A: \operatorname{Type}),[\operatorname{AddCommGroup}(A)][\operatorname{Fintype}(A)],\\(\forall (x: A),x+x=0) \longrightarrow\\\operatorname{let} s((\psi: \operatorname{AddChar}(A, \mathbb{C})), (x: A)):=\Re \psi(x),\\\operatorname{let} m((f: A \to \mathbb{R}), (\psi: \operatorname{AddChar}(A, \mathbb{C}))):=\sum_{x \in A}f(x)s(\psi, x),\\\operatorname{let} L((a: A), (f: A \to \mathbb{R})):=\frac{-2}{\left|A\right|}\sum_{\psi \in \operatorname{AddChar}(A, \mathbb{C})}s(\psi, a) \log \left|m(f, \psi)\right|,\\\forall (p: A \to \mathbb{R})(q: A \to \mathbb{R})(a: A)(e: \mathbb{R}),0<e \land \sum_{x \in A}p(x)=\sum_{x \in A}q(x) \land\\(\forall (\psi: \operatorname{AddChar}(A, \mathbb{C})),e\le\left|m(p, \psi)\right| \land e\le\left|m(q, \psi)\right|) \longrightarrow\\\left|L(a, p)-L(a, q)\right|\le\frac{2\operatorname{TV}(p, q)}{e}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityLogStability.log_parity_coefficient_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithmic divided differences turn the coefficient difference into an expectation difference for a single real test function. At two distinct points, the sum over characters of the absolute sign differences equals the group order by character orthogonality. This bounds the oscillation of the test function. Equal total masses allow centering it at the midpoint of its range, giving the factor two.

In Quantum Geometry section 35.6.8, A is the quotient by the fair-input image and the two mass functions are the induced probability laws. For each nonzero projected column a, the grouped-bias recovery formula identifies L(a,p) with the natural logarithm of the product of the positive bias factors in that group. The two laws must have absolute sign moments at least the same positive e. Absolute moments also remove the sign contributed by an affine offset.

**Theorem 1.2 (Sharpness on a one-bit law).**

$$\begin{aligned}\operatorname{let} (t: \mathbb{R}), B(t, \operatorname{false}):=\frac{1+t}{2}, B(t, \operatorname{true}):=\frac{1-t}{2},\\\forall (e: \mathbb{R})(c: \mathbb{R}),0<e<1 \land c<2 \longrightarrow\\\exists (q: \mathbb{R}),e<q<1 \land \frac{c\operatorname{TV}(B(q), B(e))}{e}<\log q-\log e\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParityLogStability.log_bernoulli_bias_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a one-bit input the absolute moments are one and the positive bias factor. For every floor strictly between zero and one, the construction chooses a second bias factor strictly above that floor with enough margin to violate the estimate for any constant below two. The total variation is half the difference of the two bias factors.

## References

- Truth anchor: `D5/S3/TotalVariation/ParityLogStability.log_bernoulli_bias_sharp`
- Truth anchor: `D5/S3/TotalVariation/ParityLogStability.log_parity_coefficient_stability`
- Dependency: [D5/S3/TotalVariation/Pinsker](Pinsker.md)
