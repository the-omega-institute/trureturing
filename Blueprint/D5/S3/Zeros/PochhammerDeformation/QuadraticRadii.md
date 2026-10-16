# Exact Quadratic Root Radii

## Abstract

For every positive a, the quadratic Pochhammer class has outer radius a+1 and inner radius (a+sqrt(a(a+1)))/2, both attained.

**Theorem 1.1 (Factorization of a complex quadratic).**

$$\forall A \in \mathbb{C},\; \forall B \in \mathbb{C},\; \forall c \in \mathbb{C},\; A \ne 0 \Rightarrow \left(\exists z \in \mathbb{C},\; \exists w \in \mathbb{C},\; \operatorname{Polynomial.roots}\left(\operatorname{Polynomial.C}\left(A\right) \cdot \operatorname{Polynomial.X}^{2} + \operatorname{Polynomial.C}\left(B\right) \cdot \operatorname{Polynomial.X} + \operatorname{Polynomial.C}\left(c\right)\right) = \left\{z, w\right\} \land \operatorname{Polynomial.C}\left(A\right) \cdot \operatorname{Polynomial.X}^{2} + \operatorname{Polynomial.C}\left(B\right) \cdot \operatorname{Polynomial.X} + \operatorname{Polynomial.C}\left(c\right) = \operatorname{Polynomial.C}\left(A\right) \cdot \left(\operatorname{Polynomial.X} - \operatorname{Polynomial.C}\left(z\right)\right) \cdot \left(\operatorname{Polynomial.X} - \operatorname{Polynomial.C}\left(w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex A, B and c with A nonzero, there are complex z and w such that the multiset of roots of A X^2 + B X + c is {z,w}, and the polynomial equals A(X-z)(X-w). The roots are counted with multiplicity, so z and w may coincide.

**Definition 1.2 (The full degree-two class).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.U2`

*Formalization.* `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.U2` (`✓ std3`).

*Citation.* Anna Vishnyakova (2026). *Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros*. DOI: [10.48550/arXiv.2608.03723](https://doi.org/10.48550/arXiv.2608.03723).

*Commentary.*

U2 consists of all real polynomials of degree two whose image under the frozen Pochhammer operator has every complex root real and in [-1,0]. The original polynomial need not be monic or real-rooted.

**Definition 1.3 (Norms of complex zeros).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.rootNorms`

*Formalization.* `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.rootNorms` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A root norm is the norm of a complex number at which the real polynomial evaluates to zero. The definition uses algebra evaluation into C.

**Definition 1.4 (Outer radius).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.R2`

*Formalization.* `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.R2` (`✓ std3`).

*Citation.* Anna Vishnyakova (2026). *Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros*. DOI: [10.48550/arXiv.2608.03723](https://doi.org/10.48550/arXiv.2608.03723).

*Commentary.*

R2 is the supremum, over U2, of the supremum of each polynomial's root norms. For degree two the nonempty finite root set makes the inner supremum the largest root norm, as in Open Problem 7.2.

**Definition 1.5 (Inner radius).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.r2`

*Formalization.* `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.r2` (`✓ std3`).

*Citation.* Anna Vishnyakova (2026). *Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros*. DOI: [10.48550/arXiv.2608.03723](https://doi.org/10.48550/arXiv.2608.03723).

*Commentary.*

r2 is the supremum, over U2, of the infimum of each polynomial's root norms, corresponding to the smallest root norm in Open Problem 7.1.

**Definition 1.6 (The normalized inverse image).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.normalQuadratic`

*Formalization.* `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.normalQuadratic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna Vishnyakova (2026). *Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros*. DOI: [10.48550/arXiv.2608.03723](https://doi.org/10.48550/arXiv.2608.03723).

*Commentary.*

The polynomial is x^2+((a+1)(u+v)-1)x+a(a+1)uv. Its transformed image is a(a+1)(z+u)(z+v).

**Theorem 1.7 (Equivalence with the parameter square).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna Vishnyakova (2026). *Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros*. DOI: [10.48550/arXiv.2608.03723](https://doi.org/10.48550/arXiv.2608.03723).

*Commentary.*

Membership in U2 is equivalent to being a nonzero real scalar multiple of a normalQuadratic with u,v in [0,1]. The proof reuses the frozen operator and Mathlib's factorization over the complex numbers.

**Theorem 1.8 (Every root lies in the outer disk).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.normal_outer_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.normal_outer_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna Vishnyakova (2026). *Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros*. DOI: [10.48550/arXiv.2608.03723](https://doi.org/10.48550/arXiv.2608.03723).

*Commentary.*

Every complex zero of every normalQuadratic from the parameter square has norm at most a+1. Real roots are controlled by coefficient and endpoint inequalities; nonreal roots have squared norm a(a+1)uv.

**Theorem 1.9 (Some root lies in the sharp inner disk).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.normal_inner_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.normal_inner_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna Vishnyakova (2026). *Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros*. DOI: [10.48550/arXiv.2608.03723](https://doi.org/10.48550/arXiv.2608.03723).

*Commentary.*

Put M=(a+sqrt(a(a+1)))/2 and q=sqrt(a(a+1)uv). If q<=M, the root product gives a root of norm at most M. Otherwise AM-GM gives p(-M)<=(q-M)(q-M-1)<0, and the intermediate value theorem supplies a real zero in [-M,0].

**Theorem 1.10 (The corner witness).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_outer_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_outer_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna Vishnyakova (2026). *Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros*. DOI: [10.48550/arXiv.2608.03723](https://doi.org/10.48550/arXiv.2608.03723).

*Commentary.*

At u=v=1 the admissible polynomial factors as (x+a)(x+a+1), and the zero -(a+1) attains the outer bound.

**Theorem 1.11 (The repeated-root witness).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_inner_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_inner_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna Vishnyakova (2026). *Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros*. DOI: [10.48550/arXiv.2608.03723](https://doi.org/10.48550/arXiv.2608.03723).

*Commentary.*

Writing s=sqrt(a(a+1)) and M=(a+s)/2, the parameter u=v=M/s belongs to the unit square and yields (x+M)^2. The identity M=a+c2(a) and its admissibility reuse the frozen interval theorem.

**Theorem 1.12 (Open Problem 7.2 in degree two).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_outer_radius`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_outer_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna Vishnyakova (2026). *Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros*. DOI: [10.48550/arXiv.2608.03723](https://doi.org/10.48550/arXiv.2608.03723).

*Commentary.*

For every a>0, R2(a)=a+1. This proves the degree-two case of the paper's conjectured formula R_n=a+n-1; no assertion about n>2 is made.

**Theorem 1.13 (Open Problem 7.1 in degree two).**

Lean statement: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_inner_radius`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_inner_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna Vishnyakova (2026). *Polynomially Deformed Normalized Pochhammer Sequences Having Generating Functions With Only Real Non-positive Zeros*. DOI: [10.48550/arXiv.2608.03723](https://doi.org/10.48550/arXiv.2608.03723).

*Commentary.*

For every a>0, r2(a)=(a+sqrt(a(a+1)))/2. The paper states this expression as a lower bound; the uniform inner estimate proves equality. This result does not assert a bound uniform in the degree.

## References

- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.R2`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.U2`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.normalQuadratic`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.normal_inner_bound`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.normal_outer_bound`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_factors`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_inner_radius`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_inner_witness`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_normal_form`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_outer_radius`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.quadratic_outer_witness`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.r2`
- Truth anchor: `D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.rootNorms`
- Dependency: [D5/S3/Zeros/PochhammerDeformation/QuadraticInterval](QuadraticInterval.md)
