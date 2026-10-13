# The trace exponential is not exponentially convex

## Abstract

The trace exponential fails exponential convexity on density matrices, already on four qubit states.

Jop Briët and Peter Harremoës, Properties of classical and quantum Jensen-Shannon divergence, Physical Review A 79, 052311 (2009), DOI 10.1103/PhysRevA.79.052311, arXiv:0806.4472v4. Definition 4 (Exponential convexity), verbatim: “Let X be a convex set and φ : X → R a mapping. Then φ is said to be exponentially convex if the function X × X → R given by (x, y) → φ((x+y)/2) is positive definite.” §VI (Conclusions and open problems), verbatim: “Whether (QJD1)^{1/2} is a metric for all mixed states remains unknown. However, based on a large amount of numerical evidence, we conjecture the function A → Tr(e^A) to be exponentially convex for density matrices A. Proving this would imply that QJDα is negative definite for α ∈ (0, 2], and hence the square of a metric that can be embedded in a real Hilbert space.”

**Definition 1.1 (The trace exponential).**

$$\forall n: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{trExp}\left(A\right) = \operatorname{trace}\left(\operatorname{exp}\left(A\right)\right)$$

*Formalization.* `D5/S3/Divergence/TraceExpExponentialConvexityRefutation.trExp` (`✓ std3`).

*Citation.* Jop Briët, Peter Harremoës (2009). *Properties of classical and quantum Jensen-Shannon divergence*. DOI: [10.1103/PhysRevA.79.052311](https://doi.org/10.1103/PhysRevA.79.052311). URL: <https://arxiv.org/abs/0806.4472v4>.

*Commentary.*

The function takes the trace of the matrix exponential over the complex numbers. For Hermitian inputs its value is real.

**Definition 1.2 (Density matrices).**

$$\forall n: \mathbb{N}, \forall rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{IsDensity}\left(rho\right)) \Leftrightarrow ((\operatorname{PosSemidef}\left(rho\right)) \land (\operatorname{trace}\left(rho\right) = 1))$$

*Formalization.* `D5/S3/Divergence/TraceExpExponentialConvexityRefutation.IsDensity` (`✓ std3`).

*Citation.* Jop Briët, Peter Harremoës (2009). *Properties of classical and quantum Jensen-Shannon divergence*. DOI: [10.1103/PhysRevA.79.052311](https://doi.org/10.1103/PhysRevA.79.052311). URL: <https://arxiv.org/abs/0806.4472v4>.

*Commentary.*

A density matrix is positive semidefinite and has trace one.

**Definition 1.3 (Exponential convexity on density matrices).**

$$(claim) \Leftrightarrow (\forall n: \mathbb{N}, \forall N: \mathbb{N}, \forall rho: \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall c: \operatorname{Fin}\left(N\right) \to \mathbb{R}, (\forall i: \operatorname{Fin}\left(N\right), \operatorname{IsDensity}\left(\operatorname{rho}\left(i\right)\right)) \Rightarrow (0 \le \operatorname{re}\left(\sum_{i} \sum_{j} (\operatorname{ofReal}\left(\operatorname{c}\left(i\right) \cdot \operatorname{c}\left(j\right)\right) \cdot \operatorname{trExp}\left((\frac{1}{2}) \cdot (\operatorname{rho}\left(i\right) + \operatorname{rho}\left(j\right))\right))\right)))$$

*Formalization.* `D5/S3/Divergence/TraceExpExponentialConvexityRefutation.claim` (`✓ std3`).

*Citation.* Jop Briët, Peter Harremoës (2009). *Properties of classical and quantum Jensen-Shannon divergence*. DOI: [10.1103/PhysRevA.79.052311](https://doi.org/10.1103/PhysRevA.79.052311). URL: <https://arxiv.org/abs/0806.4472v4>.

*Commentary.*

Definition 4 requires the midpoint kernel to be positive definite. For every finite family of density matrices and every real coefficient vector, the real part of its quadratic form must therefore be nonnegative.

**Theorem 1.4 (Failure at every nonzero inverse temperature).**

$$\forall t: \mathbb{R}, (t \neq 0) \Rightarrow (\exists rho: \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right), \exists c: \operatorname{Fin}\left(4\right) \to \mathbb{R}, (\forall i: \operatorname{Fin}\left(4\right), \operatorname{IsDensity}\left(\operatorname{rho}\left(i\right)\right)) \land (\operatorname{re}\left(\sum_{i} \sum_{j} (\operatorname{ofReal}\left(\operatorname{c}\left(i\right) \cdot \operatorname{c}\left(j\right)\right) \cdot \operatorname{trExp}\left((\operatorname{ofReal}\left(\frac{t}{2}\right)) \cdot (\operatorname{rho}\left(i\right) + \operatorname{rho}\left(j\right))\right))\right) < 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/TraceExpExponentialConvexityRefutation.family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jop Briët, Peter Harremoës (2009). *Properties of classical and quantum Jensen-Shannon divergence*. DOI: [10.1103/PhysRevA.79.052311](https://doi.org/10.1103/PhysRevA.79.052311). URL: <https://arxiv.org/abs/0806.4472v4>.

*Commentary.*

Let ρ₀=I/2 and let ρ₁,ρ₂,ρ₃ be the rank-one projectors onto (1,0), (1/2,√3/2), and (−1/2,√3/2). Set u=e^(t/4)>0. Explicit rotations diagonalize their pairwise sums. The kernel values are K₀₀=2u², Kₖₖ=u⁴+1 for k>0, and Kᵢⱼ=u³+u for i≠j. With c=(−3(u+u⁻¹)/2,1,1,1), the quadratic form equals −(3/2)(u−1)⁴. Injectivity of the real exponential makes this strictly negative for t≠0. Replacing t by −t also refutes the kernels Tr exp(−t(ρ+σ)/2).

**Theorem 1.5 (A centre-plus-trine counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/TraceExpExponentialConvexityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/briet-harremoes-2009-trace-exp-exponential-convexity` (refuted) by `D5/S3/Divergence/TraceExpExponentialConvexityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"briet-harremoes-2009-trace-exp-exponential-convexity","declaration_gid":"D5/S3/Divergence/TraceExpExponentialConvexityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jop Briët, Peter Harremoës (2009). *Properties of classical and quantum Jensen-Shannon divergence*. DOI: [10.1103/PhysRevA.79.052311](https://doi.org/10.1103/PhysRevA.79.052311). URL: <https://arxiv.org/abs/0806.4472v4>.

*Commentary.*

The temperature family at t=1 contradicts exponential convexity of A↦Tr(e^A) on density matrices. One maximally mixed qubit state and three pure states suffice. The proposed argument for Hilbert-space embeddability through this conjecture cannot apply. Hilbert-space embeddability of the square root of quantum Jensen–Shannon divergence in dimensions at least three is not settled by this result.

## References

- Truth anchor: `D5/S3/Divergence/TraceExpExponentialConvexityRefutation.IsDensity`
- Truth anchor: `D5/S3/Divergence/TraceExpExponentialConvexityRefutation.claim`
- Truth anchor: `D5/S3/Divergence/TraceExpExponentialConvexityRefutation.family`
- Truth anchor: `D5/S3/Divergence/TraceExpExponentialConvexityRefutation.result`
- Truth anchor: `D5/S3/Divergence/TraceExpExponentialConvexityRefutation.trExp`
