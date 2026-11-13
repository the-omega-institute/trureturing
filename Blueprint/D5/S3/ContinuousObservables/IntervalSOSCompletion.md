# Interval sums of squares and a signed circle completion

## Abstract

Parity-controlled interval sums of squares construct continuous determinant-one unitary fields on the native phase circle.

Write T=AddCircle(1), z=windingPhase:T→C and A₂=C(T,Matrix(ZMod 2,ZMod 2,C)), the existing CyclicObservable 2 algebra. Write R[X] for real polynomials, c(P) for complexification and d(P) for Polynomial.natDegree. Every subtraction k−1 of natural degrees is truncated. Even(c(A)) means that all odd coefficients vanish. par(P,k) means HasParity(c(P),k): coefficients of parity opposite to k vanish. These coefficient definitions include the zero polynomial.

**Theorem 1.1 (The complete scalar endpoint).**

$$\forall (k: \mathbb{N}), \forall (A: \mathbb{R}[X]), ((\operatorname{Even}(\operatorname{c}(A))) \land (\operatorname{d}(A) \leq 2k) \land (\forall (x: I), 0 \leq \operatorname{A}(x))) \Rightarrow \exists (B: \mathbb{R}[X]), \exists (C: \mathbb{R}[X]), (A = (B)^{2}+(1-(X)^{2})(C)^{2}) \land (\operatorname{d}(B) \leq k) \land (\operatorname{d}(C) \leq k-1) \land ((k = 0) \Rightarrow C = 0) \land (\operatorname{par}(B, k)) \land (\operatorname{par}(C, k-1))$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/IntervalSOSCompletion.exists_sumsq_decomposition` (`✓ std3`). ∎

*Citation.* Andras Gilyen, Yuan Su, Guang Hao Low, Nathan Wiebe (2019). *Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics*. DOI: [10.1145/3313276.3316366](https://doi.org/10.1145/3313276.3316366). URL: <https://arxiv.org/abs/1806.01838v1>.

*Commentary.*

Here I is the closed real interval [−1,1], and X is the polynomial indeterminate. The identity is global in R[X], although nonnegativity is assumed only on I. The zero polynomial and k=0 are included; the latter has C=0 explicitly, so the natural-degree convention loses no endpoint condition.

The original construction removes one elementary factor from A at a time. A nonreal squared root gives a real conjugate quartic with a degree-two SOS representation. A real squared root outside (0,1) gives a signed quadratic with a degree-one representation, including zero and both endpoints. An interior real root is at least double, since a simple root would force a sign change. This supplies a square factor.

Divisibility descends from the complexification to real coefficients. The cofactor is even and nonnegative away from the finite zero set of the removed factor. One-sided continuity extends this inequality over the entire closed interval. Each removal reduces the degree by twice a positive natural number; strong induction reconstructs A. The product step uses (B₁²+wC₁²)(B₂²+wC₂²)=(B₁B₂−wC₁C₂)²+w(B₁C₂+B₂C₁)², with w=1−X². Multiplication by the identity X²+(1−X²)=1 adjusts the parity budget.

**Theorem 1.2 (A continuous field with both star products and determinant one).**

$$\forall (k: \mathbb{N}), \forall (p: \mathbb{R}[X]), ((\operatorname{d}(p) \leq k) \land (\operatorname{par}(p, k)) \land (\forall (x: I), (\operatorname{p}(x))^{2} \leq 1)) \Rightarrow \exists (B: \mathbb{R}[X]), \exists (C: \mathbb{R}[X]), \exists (U: A_{2}), ((1-(p)^{2} = (B)^{2}+(1-(X)^{2})(C)^{2}) \land (\operatorname{d}(B) \leq k) \land (\operatorname{d}(C) \leq k-1) \land ((k = 0) \Rightarrow C = 0) \land (\operatorname{par}(B, k)) \land (\operatorname{par}(C, k-1))) \land (U = \operatorname{F}(p, B, C)) \land (\operatorname{star}(U)U = 1) \land (U\operatorname{star}(U) = 1) \land (\forall (t: T), \operatorname{det}(\operatorname{U}(t)) = 1) \land (\forall (t: T), \operatorname{Re}(\operatorname{entry}(\operatorname{U}(t), 0, 0)) = \operatorname{p}(\operatorname{Re}(\operatorname{z}(t))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/IntervalSOSCompletion.exists_phase_unitary_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The symbol F(p,B,C) denotes phaseCompletion. At t in T set x=Re(z(t)) and y=Im(z(t)). Its entries are F₀₀=p(x)+iB(x), F₀₁=F₁₀=iyC(x), F₁₁=p(x)−iB(x). Thus the field uses the existing windingPhase in its actual entries and has rows and columns indexed by ZMod 2. The existential statement retains all degree, parity and zero-degree conditions of the scalar theorem, as well as the actual field formula.

The bound on p makes A=1−p² nonnegative on I; its degree is at most 2k and it is even because p has parity k. The scalar endpoint gives B,C. Since |z|=1, x²+y²=1 and x belongs to I. Evaluation gives p(x)²+B(x)²+y²C(x)²=1. Polynomial evaluation and the real and imaginary coordinate maps are continuous, so every matrix entry is continuous, including both interval endpoints and the circle seam. Matrix multiplication and conjugation now give both star products and determinant one; the upper-left real part is p(x).

This is the signed-circle convention. On the upper semicircle y=√(1−x²), so its matrix agrees with Gilyen–Su–Low–Wiebe, arXiv:1806.01838v1, Theorem 3 equation (3). On the lower semicircle the off-diagonal sign differs from the square-root pullback. There is no phase factorization, algorithmic root-finding or query bound, block encoding, physical implementation or full QSVT claim. The elementary matrix normalization is an application; the substantial proof content is the original root, double-root, cofactor and induction construction.

Source custody: Copyright (c) 2026 shosonoda. All rights reserved. The selected original statement/proof bodies are from auto-res/lean-qsvt at commit 42c4b9149d5957db497e4226bc02da92d10f7a3c, QSVT/Polynomial/Parity.lean, Polynomial/SqrtPart.lean, QSP/Poly.lean, QSP/PolyW.lean and QSP/Complementary.lean. They are licensed under Apache-2.0; the full text is docs/reports/licenses/auto-res-lean-qsvt-LICENSE.txt. The assembly adapts namespaces, helper visibility, imports and exposition, and adds the native field application. The mathematical source is Lemma 6 of Gilyen–Su–Low–Wiebe, DOI 10.1145/3313276.3316366, with the verified arXiv v1 locator in the Library note. This is source reuse, not an originality claim. An equivalent result in the receiver's pinned Mathlib should replace the transplant when available.

## References

- Truth anchor: `D5/S3/ContinuousObservables/IntervalSOSCompletion.exists_phase_unitary_completion`
- Truth anchor: `D5/S3/ContinuousObservables/IntervalSOSCompletion.exists_sumsq_decomposition`
- Dependency: [D5/S3/ContinuousObservables/CentralWinding](CentralWinding.md)
