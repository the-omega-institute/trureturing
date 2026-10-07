# Calderon's Reciprocal Moment Congruences

## Abstract

Calderon's reciprocal moments satisfy both congruences for every admissible imaginary quadratic order.

**Definition 1.1 (The local quadratic order).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)], \forall T \in \mathbb{Z},\; \forall N \in \mathbb{Z},\; \operatorname{R}\left(p, T, N\right) = \operatorname{AdjoinRoot}\left(X^{2} - \operatorname{C}\left((T : \operatorname{PadicInt}\left(p\right))\right) \cdot X + \operatorname{C}\left((N : \operatorname{PadicInt}\left(p\right))\right)\right)$$

*Formalization.* `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.R` (`✓ std3`).

*Citation.* Kevin Calderon (2026). *Ljunggren–Jacobsthal and Bailey-Type Congruences for Rectangular Gaussian Binomial Coefficients*. DOI: [10.48550/arXiv.2608.00347](https://doi.org/10.48550/arXiv.2608.00347). URL: <https://arxiv.org/abs/2608.00347v1>.

*Commentary.*

The source writes Oomega,p := Zp[omega] (page 19). The ring is AdjoinRoot of X squared minus T X plus N over the p-adic integers. X is the polynomial indeterminate and C embeds a coefficient; the displayed integer casts are into PadicInt p.

**Definition 1.2 (Coordinates in the chosen basis).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)], \forall T \in \mathbb{Z},\; \forall N \in \mathbb{Z},\; \forall x \in \mathrm{Nat},\; \forall y \in \mathrm{Nat},\; \operatorname{element}\left(p, T, N, x, y\right) = (x : \operatorname{R}\left(p, T, N\right)) + (y : \operatorname{R}\left(p, T, N\right)) \cdot \operatorname{AdjoinRootRoot}\left(X^{2} - \operatorname{C}\left((T : \operatorname{PadicInt}\left(p\right))\right) \cdot X + \operatorname{C}\left((N : \operatorname{PadicInt}\left(p\right))\right)\right)$$

*Formalization.* `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.element` (`✓ std3`).

*Citation.* Kevin Calderon (2026). *Ljunggren–Jacobsthal and Bailey-Type Congruences for Rectangular Gaussian Binomial Coefficients*. DOI: [10.48550/arXiv.2608.00347](https://doi.org/10.48550/arXiv.2608.00347). URL: <https://arxiv.org/abs/2608.00347v1>.

*Commentary.*

Equation (6.1), page 18, is omega squared minus T omega plus N equals zero, with T,N integers and negative discriminant. The distinguished root is AdjoinRoot.root of this polynomial. The source's expression x+yomega uses the displayed natural coordinates and ring casts.

**Definition 1.3 (The imaginary and inert hypotheses).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)], \forall T \in \mathbb{Z},\; \forall N \in \mathbb{Z},\; (\operatorname{Admissible}\left(p, T, N\right)) \Leftrightarrow ((5 < p) \land ((T^{2} - 4 \cdot N < 0) \land ((\neg ((p : \mathbb{Z}) \mid T^{2} - 4 \cdot N)) \land (\operatorname{legendreSym}\left(p, T^{2} - 4 \cdot N\right) = -1))))$$

*Formalization.* `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.Admissible` (`✓ std3`).

*Citation.* Kevin Calderon (2026). *Ljunggren–Jacobsthal and Bailey-Type Congruences for Rectangular Gaussian Binomial Coefficients*. DOI: [10.48550/arXiv.2608.00347](https://doi.org/10.48550/arXiv.2608.00347). URL: <https://arxiv.org/abs/2608.00347v1>.

*Commentary.*

Equations (6.1) and (6.3) require T,N in Z, Delta=T squared minus 4N < 0, p>5, p not dividing Delta, and its Legendre symbol equal to -1. The bracket assumption supplies the prime instance.

**Definition 1.4 (The literal set of positive representatives).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)], \forall T \in \mathbb{Z},\; \forall N \in \mathbb{Z},\; \forall k \in \mathrm{Nat},\; \operatorname{U}\left(p, T, N, k\right) = \{z : \operatorname{R}\left(p, T, N\right) \mid \exists x \in \mathrm{Nat},\; \exists y \in \mathrm{Nat},\; ((1 \le x) \land (x \le p^{k})) \land (((1 \le y) \land (y \le p^{k})) \land ((\neg \left((p \mid x) \land (p \mid y)\right)) \land (z = \operatorname{element}\left(p, T, N, x, y\right))))\}$$

*Formalization.* `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.U` (`✓ std3`).

*Citation.* Kevin Calderon (2026). *Ljunggren–Jacobsthal and Bailey-Type Congruences for Rectangular Gaussian Binomial Coefficients*. DOI: [10.48550/arXiv.2608.00347](https://doi.org/10.48550/arXiv.2608.00347). URL: <https://arxiv.org/abs/2608.00347v1>.

*Commentary.*

Source expression (page 19): For k ≥ 1, define Uω,k := {x+yω : 1 ≤ x,y ≤ pᵏ, p ∤ (x,y)}. U is a finite set of ring elements, obtained as the image of the positive coordinate rectangle after excluding simultaneous divisibility. The existential coordinate binders express precisely that image; p^k is included in each coordinate.

**Definition 1.5 (The reciprocal first moment).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)], \forall T \in \mathbb{Z},\; \forall N \in \mathbb{Z},\; \forall k \in \mathrm{Nat},\; \operatorname{H1}\left(p, T, N, k\right) = \sum_{z \in \operatorname{U}\left(p, T, N, k\right)} \operatorname{RingInverse}\left(z\right)$$

*Formalization.* `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.H1` (`✓ std3`).

*Citation.* Kevin Calderon (2026). *Ljunggren–Jacobsthal and Bailey-Type Congruences for Rectangular Gaussian Binomial Coefficients*. DOI: [10.48550/arXiv.2608.00347](https://doi.org/10.48550/arXiv.2608.00347). URL: <https://arxiv.org/abs/2608.00347v1>.

*Commentary.*

Source expression (page 19): Hr,ω(k) := ∑z∈Uω,k z⁻ʳ. Here r=1 and the sum is over the ring elements of U. RingInverse is Mathlib Ring.inverse: for a unit z it is val((hz.unit)^(-1)), where hz proves IsUnit z. It is zero on nonunits. Every representative in the admissible setting is a unit, so that extension adds no terms or hypotheses to the source sum.

**Definition 1.6 (The reciprocal second moment).**

$$\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)], \forall T \in \mathbb{Z},\; \forall N \in \mathbb{Z},\; \forall k \in \mathrm{Nat},\; \operatorname{H2}\left(p, T, N, k\right) = \sum_{z \in \operatorname{U}\left(p, T, N, k\right)} \operatorname{RingInverse}\left(z\right)^{2}$$

*Formalization.* `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.H2` (`✓ std3`).

*Citation.* Kevin Calderon (2026). *Ljunggren–Jacobsthal and Bailey-Type Congruences for Rectangular Gaussian Binomial Coefficients*. DOI: [10.48550/arXiv.2608.00347](https://doi.org/10.48550/arXiv.2608.00347). URL: <https://arxiv.org/abs/2608.00347v1>.

*Commentary.*

The same source formula Hr,ω(k) := ∑z∈Uω,k z⁻ʳ (page 19), with r=2, squares the underlying inverse unit value. The finite set and inverse convention are exactly those of H1.

**Definition 1.7 (Conjecture 6.3).**

$$(claim) \Leftrightarrow (\forall p \in \mathrm{Nat},\; \forall hp \in \operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right),\; \forall T \in \mathbb{Z},\; \forall N \in \mathbb{Z},\; (\operatorname{Admissible}\left(p, hp, T, N\right)) \Rightarrow (\forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow ((\operatorname{H1}\left(p, hp, T, N, k\right) \in \operatorname{IdealSpan}\left(\left\{(p : \operatorname{R}\left(p, hp, T, N\right))^{2 \cdot k}\right\}\right)) \land (\operatorname{H2}\left(p, hp, T, N, k\right) \in \operatorname{IdealSpan}\left(\left\{(p : \operatorname{R}\left(p, hp, T, N\right))^{k}\right\}\right)))))$$

*Formalization.* `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kevin Calderon (2026). *Ljunggren–Jacobsthal and Bailey-Type Congruences for Rectangular Gaussian Binomial Coefficients*. DOI: [10.48550/arXiv.2608.00347](https://doi.org/10.48550/arXiv.2608.00347). URL: <https://arxiv.org/abs/2608.00347v1>.

*Commentary.*

Conjecture 6.3 (page 19): Let ω satisfy (6.1), and let p satisfy (6.3). Then, for every k ≥ 1,

$$
\forall p \in \mathrm{Nat},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)], \forall T \in \mathbb{Z},\; \forall N \in \mathbb{Z},\; (\operatorname{Admissible}\left(p, T, N\right)) \Rightarrow (\forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow ((\operatorname{H1}\left(p, T, N, k\right) \in \operatorname{IdealSpan}\left(\left\{(p : \operatorname{R}\left(p, T, N\right))^{2 \cdot k}\right\}\right)) \land (\operatorname{H2}\left(p, T, N, k\right) \in \operatorname{IdealSpan}\left(\left\{(p : \operatorname{R}\left(p, T, N\right))^{k}\right\}\right))))
$$

The source's displayed conclusion is H₁,ω(k) ∈ p²ᵏ𝒪ω,p, H₂,ω(k) ∈ pᵏ𝒪ω,p. The explicit hp binder supplies the prime instance in the calls to Admissible, R, H1 and H2. IdealSpan of a singleton is the principal ideal generated by that ring power. The source states a conjecture.

<table><thead><tr><th>Public definition</th><th>Source expression (pages 18–19)</th><th>Encoding</th></tr></thead><tbody><tr><td>R</td><td>𝒪ω,p := ℤp[ω]</td><td>AdjoinRoot of X²−TX+N over PadicInt p</td></tr><tr><td>element</td><td>x+yω</td><td>Natural casts and AdjoinRoot.root</td></tr><tr><td>Admissible</td><td>Equations (6.1), (6.3)</td><td>Negative discriminant; p&gt;5; nondivisibility; Legendre symbol −1</td></tr><tr><td>U</td><td>{x+yω : 1≤x,y≤pᵏ, p∤(x,y)}</td><td>Finite image of the filtered positive rectangle in R</td></tr><tr><td>H1</td><td>Hr,ω(k) := ∑z∈Uω,k z⁻ʳ, r=1</td><td>Sum over U of Ring.inverse, the underlying inverse unit value</td></tr><tr><td>H2</td><td>Hr,ω(k) := ∑z∈Uω,k z⁻ʳ, r=2</td><td>Sum over U of the squared inverse unit value</td></tr></tbody></table>

**Theorem 1.8 (The moment conjecture holds).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.result` (`✓ std3`). ∎

*Resolves.* `Problems/calderon-2026-quadratic-order-reciprocal-moments` (proved) by `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"calderon-2026-quadratic-order-reciprocal-moments","declaration_gid":"D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kevin Calderon (2026). *Ljunggren–Jacobsthal and Bailey-Type Congruences for Rectangular Gaussian Binomial Coefficients*. DOI: [10.48550/arXiv.2608.00347](https://doi.org/10.48550/arXiv.2608.00347). URL: <https://arxiv.org/abs/2608.00347v1>.

*Commentary.*

Positive coordinates identify U bijectively with the units of the finite quadratic quotient. Multiplication by 2 permutes those units; cancellation of 3 makes their inverse-square sum zero. Reflect each coordinate a<p^k to p^k-a and fix a=p^k. The resulting affine correction has two boundary strips; each reduces to a scalar inverse-square sum modulo p^k. The exact inverse identity then gives the first-moment bound after cancellation of 2. Both conjuncts hold for every admissible parameter, without an extra assumption.

The omega-Ljunggren analogue (Conjecture 6.4) has its stated Conjecture 6.3 reciprocal-moment premise discharged; its translated-block and Newton-identity conclusion remains open. The omega-Bailey analogue (Conjecture 6.5) remains open under its stated inert-prime and digit-range hypotheses; the source gives Frobenius strip factorizations without a Conjecture 6.3 premise. Sharpness remains open.

## References

- Truth anchor: `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.Admissible`
- Truth anchor: `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.H1`
- Truth anchor: `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.H2`
- Truth anchor: `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.R`
- Truth anchor: `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.U`
- Truth anchor: `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.claim`
- Truth anchor: `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.element`
- Truth anchor: `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.result`
- Dependency: [D5/S3/Combinatorics/Parking/OperationalDynamics](../../../Combinatorics/Parking/OperationalDynamics.md)
