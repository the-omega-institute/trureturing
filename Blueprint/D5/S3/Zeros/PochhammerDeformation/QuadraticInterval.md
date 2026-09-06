# Quadratic Pochhammer Deformation

## Abstract

The normalized Pochhammer operator has an exact degree-two real-root interval; its leftward extent violates the proposed strict upper bound for small positive parameters.

**Definition 1.1 (The normalized falling-Pochhammer operator).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.lOp`

*Formalization.* `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.lOp` (`✓ std3`).

*Citation.* Anna Vishnyakova (2026). *Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros*. DOI: [10.48550/arXiv.2608.03723](https://doi.org/10.48550/arXiv.2608.03723).

*Commentary.*

The operator is constructed as a real linear map on the falling-Pochhammer basis. Its kth basis vector D_k is X(X-1)...(X-k+1), including D_0=1. The rising factor (a)_k is the evaluation at a of Mathlib's ascending Pochhammer polynomial. The construction sends D_k to (a)_k X^k.

**Definition 1.2 (All complex roots lie in the real interval).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.RealRootsInUnitInterval`

*Formalization.* `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.RealRootsInUnitInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every member z of the root multiset after mapping the real polynomial's coefficients to the complex numbers, the imaginary part of z is zero and its real part lies in the closed interval [-1,0].

**Definition 1.3 (The degree-two parameter set).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.m2`

*Formalization.* `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.m2` (`✓ std3`).

*Citation.* Anna Vishnyakova (2026). *Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros*. DOI: [10.48550/arXiv.2608.03723](https://doi.org/10.48550/arXiv.2608.03723).

*Commentary.*

M_2(a) consists of all real t for which L_a((X+t)^2) satisfies the preceding complex-root predicate. Write Q_{a,t}=L_a((X+t)^2).

**Definition 1.4 (Leftward extent from the parameter set).**

$$c_{2}\left(a\right)=-\operatorname{sInf}\left(M_{2}\left(a\right)\right)$$

*Formalization.* `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.c2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The extent is the negative infimum of M_2(a), defined independently of the square-root formula. The interval theorem proves this infimum is the left endpoint and identifies the conjecture's interval parameter.

**Theorem 1.5 (Definition 1.4 holds for the constructed map).**

$$\forall a\in \mathbb{R},a>0,\forall k\in \mathbb{N},\mathcal{L}_{a}\left(\frac{D_{k}}{(a)_{k}}\right)=X^{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.lOp_definition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity of a makes every rising Pochhammer factor nonzero. Linearity extends these defining equations to every finite expansion, exactly as in Definition 1.4.

**Theorem 1.6 (Explicit quadratic image).**

$$\forall a\in \mathbb{R},a>0,\quad \forall t\in \mathbb{R},\quad \mathcal{L}_{a}\left((X+t)^{2}\right)=a(a+1)X^{2}+a(1+2t)X+t^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.lOp_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand the input on D_0,D_1,D_2 and apply the normalized defining equation together with linearity. The coefficient formula is a conclusion about the constructed operator.

**Theorem 1.7 (Both endpoint values are squares).**

$$\forall a\in \mathbb{R},a>0,\quad \forall t\in \mathbb{R},\quad Q_{a,t}\left(0\right)=t^{2}\geq 0,\quad Q_{a,t}\left(-1\right)=(a-t)^{2}\geq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.quadratic_endpoint_squares` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The value at -1 is identically (a-t)^2. This equality is used in the interval proof to supply the lower-endpoint sign condition.

**Theorem 1.8 (Exact parameter interval and extent).**

$$\begin{aligned}\forall a\in \mathbb{R},a>0,\quad M_{2}\left(a\right)=[\frac{a-\sqrt{a^{2}+a}}{2},\frac{a+\sqrt{a^{2}+a}}{2}],\\c_{2}\left(a\right)=\frac{\sqrt{a^{2}+a}-a}{2},\quad M_{2}\left(a\right)=[-c_{2}\left(a\right),a+c_{2}\left(a\right)]\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.quadratic_interval_closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complex root exists because the leading coefficient is positive and the degree is two. If all complex roots are real, the discriminant is a square. Conversely, a nonnegative discriminant makes each complex root real by the quadratic formula. The endpoint squares and the vertex bounds then place these roots in [-1,0].

The discriminant is a(a+4at-4t^2). Its nonnegativity gives the displayed t interval, and sqrt(a^2+a)<a+1 makes the vertex condition automatic. Repeated roots at the two parameter endpoints are included. Thus the conjectured interval shape holds at degree two.

**Theorem 1.9 (The strict upper bound fails for all small positive parameters).**

$$\begin{aligned}\forall a\in \mathbb{R},a>0,\quad (c_{2}\left(a\right)<2a\Leftrightarrow \frac{1}{24}<a),\\c_{2}\left(\frac{1}{24}\right)=\frac{1}{12}=2\cdot\frac{1}{24},\\(a\leq \frac{1}{24}\Rightarrow (2a\leq c_{2}\left(a\right)\land \neg (0<c_{2}\left(a\right)\land c_{2}\left(a\right)<2a)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.quadratic_conjecture_refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a, sqrt(a^2+a)<5a is equivalent to 1/24<a. The boundary equality is an instance of the general closed form. Every 0<a<=1/24 therefore refutes Conjecture 6.5's strict upper bound at k=1. Higher degrees, monotonicity in k, its limit, and the Riemann hypothesis are outside this result.

## References

- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.RealRootsInUnitInterval`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.c2`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.lOp`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.lOp_definition`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.lOp_quadratic`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.m2`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.quadratic_conjecture_refutation`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.quadratic_endpoint_squares`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticInterval.quadratic_interval_closed_form`
