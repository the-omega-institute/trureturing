# CStarSendov

## Abstract

Critical branches exchange over a compact interval and refute C*-algebraic Sendov.

**Definition 1.1 (The C*-algebraic disc).**

$$\forall A:Type, [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] \forall a:A, \forall r:\mathbb{R}, \operatorname{cstarDisc}\left(a, r\right) = \{z:A\mid\left(z - a\right) \cdot \operatorname{star}\left(z - a\right) \le \operatorname{SMul}.\operatorname{smul}\left(((\operatorname{Real}.\operatorname{sqrt}\left(r\right)):\mathbb{C}), ((1):A)\right)\}$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.cstarDisc` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

Definition 2.3, p. 3: “Given a unital C*-algebra 𝒜 with identity 1 and an element a∈𝒜, we define the C*-algebraic closed unit disc centered at a and of radius r>0, r∈ℝ, denoted as 𝔻̅*(a,r) by 𝔻̅*(a,r) ≔ {z∈𝒜: (z−a)(z−a)* ≤ √r·1}.” The scalar √r is embedded in ℂ before acting on A. The encoding defines the expression for every real r; both conjectures use r=1.

**Definition 1.2 (Positive barycentric form).**

$$\forall A:Type, [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] \forall n:\mathbb{N}, \forall a:\operatorname{Fin}\left(n\right) \to A, \forall z:A, (\operatorname{IsConvexForm}\left(a, z\right)) \Leftrightarrow (\exists w:\operatorname{Fin}\left(n\right) \to A, (\forall j:\operatorname{Fin}\left(n\right), 0 \le (w)\left(j\right)) \land ((\sum_{(j):\operatorname{Fin}\left(n\right)}((w)\left(j\right)) = 1) \land (z = \sum_{(j):\operatorname{Fin}\left(n\right)}((w)\left(j\right) \cdot (a)\left(j\right)))))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.IsConvexForm` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

Theorem 2.2, Equation (1), p. 2: “there are positive ω_z₁, …, ω_zₙ ∈ 𝒜 such that z=∑_{j=1}ⁿ ω_zⱼ aⱼ, ∑_{j=1}ⁿ ω_zⱼ=1.” Positive means nonnegative in the C*-order. Indices become zero-based Fin n. The constructed weights are also invertible and strictly positive pointwise.

**Definition 1.3 (The clipped linear ramp).**

$$\forall t:\mathbb{R}, \operatorname{ramp}\left(t\right) = \operatorname{min}\left(1, \operatorname{max}\left(0, t\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.ramp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The ramp is zero below zero, linear from zero to one, and one above one.

**Definition 1.4 (The real coordinate of the polygon).**

$$\forall t:\mathbb{R}, \operatorname{cx}\left(t\right) = -(\frac{((9):\mathbb{R})}{((10):\mathbb{R})}) + \frac{((4):\mathbb{R})}{((5):\mathbb{R})} \cdot \operatorname{ramp}\left(t\right) + \frac{((1):\mathbb{R})}{((5):\mathbb{R})} \cdot \operatorname{ramp}\left(t - 1\right) - \frac{((1):\mathbb{R})}{((5):\mathbb{R})} \cdot \operatorname{ramp}\left(t - 3\right) - \frac{((4):\mathbb{R})}{((5):\mathbb{R})} \cdot \operatorname{ramp}\left(t - 5\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.cx` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The real coordinate is piecewise linear, with turns at the integer parameters from zero to six.

**Definition 1.5 (The imaginary coordinate of the polygon).**

$$\forall t:\mathbb{R}, \operatorname{cy}\left(t\right) = \frac{((4):\mathbb{R})}{((5):\mathbb{R})} \cdot \operatorname{ramp}\left(t\right) + \frac{((1):\mathbb{R})}{((10):\mathbb{R})} \cdot \operatorname{ramp}\left(t - 2\right) - \frac{((1):\mathbb{R})}{((10):\mathbb{R})} \cdot \operatorname{ramp}\left(t - 4\right) - \frac{((4):\mathbb{R})}{((5):\mathbb{R})} \cdot \operatorname{ramp}\left(t - 5\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.cy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The imaginary coordinate stays positive in the interior of the interval.

**Definition 1.6 (The polygon in the complex plane).**

$$\forall t:\mathbb{R}, \operatorname{cfun}\left(t\right) = ((\operatorname{cx}\left(t\right)):\mathbb{C}) + ((\operatorname{cy}\left(t\right)):\mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.cfun` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The vertices are −9/10, −1/10+4i/5, 1/10+4i/5, 1/10+9i/10, −1/10+9i/10, −1/10+4i/5, and −9/10.

**Definition 1.7 (The continuous coefficient).**

$$\forall t:\operatorname{Set}.\operatorname{Icc}\left(((0):\mathbb{R}), 6\right), (c)\left(t\right) = \operatorname{cfun}\left(((t):\mathbb{R})\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.c` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The continuous map c is the restriction of cfun to Set.Icc 0 6, with codomain ℂ.

**Definition 1.8 (The discriminant expression).**

$$\forall t:\mathbb{R}, \operatorname{dfun}\left(t\right) = (\operatorname{cfun}\left(t\right))^{2} + \frac{((3):\mathbb{C})}{((4):\mathbb{C})}$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.dfun` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The derivative discriminant is c²+3/4. Its two branch points in the coefficient plane are ±i√3/2.

**Definition 1.9 (The real square-root coordinate).**

$$\forall z:\mathbb{C}, \operatorname{rootU}\left(z\right) = \operatorname{Real}.\operatorname{sqrt}\left(\frac{\left\lVert z \right\rVert + \operatorname{Complex}.\operatorname{re}\left(z\right)}{2}\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.rootU` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The coordinate is the nonnegative real square root of (|z|+Re z)/2.

**Definition 1.10 (The imaginary square-root coordinate).**

$$\forall z:\mathbb{C}, \operatorname{rootV}\left(z\right) = \operatorname{Real}.\operatorname{sqrt}\left(\frac{\left\lVert z \right\rVert - \operatorname{Complex}.\operatorname{re}\left(z\right)}{2}\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.rootV` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The coordinate is the nonnegative real square root of (|z|−Re z)/2.

**Definition 1.11 (The square-root chart with positive real part).**

$$\forall z:\mathbb{C}, \operatorname{rootR}\left(z\right) = ((\operatorname{rootU}\left(z\right)):\mathbb{C}) + ((\frac{\operatorname{Complex}.\operatorname{im}\left(z\right)}{2 \cdot \operatorname{rootU}\left(z\right)}):\mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.rootR` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

On its domain the square of this chart is z.

**Definition 1.12 (The square-root chart with positive imaginary part).**

$$\forall z:\mathbb{C}, \operatorname{rootI}\left(z\right) = ((\frac{\operatorname{Complex}.\operatorname{im}\left(z\right)}{2 \cdot \operatorname{rootV}\left(z\right)}):\mathbb{C}) + ((\operatorname{rootV}\left(z\right)):\mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.rootI` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

This chart joins the first chart above the real axis and its negative below the real axis.

**Definition 1.13 (The square root along the polygon).**

$$\forall t:\mathbb{R}, \operatorname{sfun}\left(t\right) = \operatorname{ite}\left(t \le 2, \operatorname{rootR}\left(\operatorname{dfun}\left(t\right)\right), \operatorname{ite}\left(t \le 4, \operatorname{rootI}\left(\operatorname{dfun}\left(t\right)\right), -(\operatorname{rootR}\left(\operatorname{dfun}\left(t\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.sfun` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The chart switches occur at t=2 and t=4, where the selected values agree.

**Definition 1.14 (The continuous square root).**

$$\forall t:\operatorname{Set}.\operatorname{Icc}\left(((0):\mathbb{R}), 6\right), (s)\left(t\right) = \operatorname{sfun}\left(((t):\mathbb{R})\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.s` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The continuous map s has square c²+3/4. Its endpoint values are √(39/25) and −√(39/25).

**Definition 1.15 (The three roots).**

$$((a):\operatorname{Fin}\left(3\right) \to \operatorname{C}\left(\operatorname{Set}.\operatorname{Icc}\left(((0):\mathbb{R}), 6\right), \mathbb{C}\right)) = ![\operatorname{SMul}.\operatorname{smul}\left(\frac{((1):\mathbb{C})}{((2):\mathbb{C})}, ((1):\operatorname{C}\left(\operatorname{Set}.\operatorname{Icc}\left(((0):\mathbb{R}), 6\right), \mathbb{C}\right))\right), \operatorname{SMul}.\operatorname{smul}\left(-(\frac{((1):\mathbb{C})}{((2):\mathbb{C})}), ((1):\operatorname{C}\left(\operatorname{Set}.\operatorname{Icc}\left(((0):\mathbb{R}), 6\right), \mathbb{C}\right))\right), c]$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The tuple gives the roots 1/2, −1/2, c in C(Set.Icc 0 6,ℂ).

**Definition 1.16 (The first critical branch).**

$$((bplus):\operatorname{C}\left(\operatorname{Set}.\operatorname{Icc}\left(((0):\mathbb{R}), 6\right), \mathbb{C}\right)) = \operatorname{SMul}.\operatorname{smul}\left(\frac{((1):\mathbb{C})}{((3):\mathbb{C})}, c + s\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.bplus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

This branch starts near the root 1/2 and ends at the distant critical point.

**Definition 1.17 (The second critical branch).**

$$((bminus):\operatorname{C}\left(\operatorname{Set}.\operatorname{Icc}\left(((0):\mathbb{R}), 6\right), \mathbb{C}\right)) = \operatorname{SMul}.\operatorname{smul}\left(\frac{((1):\mathbb{C})}{((3):\mathbb{C})}, c - s\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.bminus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The second branch starts at the distant critical point and ends near 1/2.

**Definition 1.18 (The supplied critical-root tuple).**

$$((bs):\operatorname{Fin}\left(2\right) \to \operatorname{C}\left(\operatorname{Set}.\operatorname{Icc}\left(((0):\mathbb{R}), 6\right), \mathbb{C}\right)) = ![bplus, bminus]$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.bs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

Both branches are algebra-valued zeros, with positive barycentric representations.

**Lemma 1.19 (The cubic derivative at every parameter).**

$$\forall z:\operatorname{C}\left(\operatorname{Set}.\operatorname{Icc}\left(((0):\mathbb{R}), 6\right), \mathbb{C}\right), \forall t:\operatorname{Set}.\operatorname{Icc}\left(((0):\mathbb{R}), 6\right), (\operatorname{CStarSchoenberg}.\operatorname{orderedDeriv}\left(a, z\right))\left(t\right) = ((3):\mathbb{C}) \cdot ((z)\left(t\right))^{2} - ((2):\mathbb{C}) \cdot (c)\left(t\right) \cdot (z)\left(t\right) - \frac{((1):\mathbb{C})}{((4):\mathbb{C})}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarSendov.ordered_deriv_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

Pointwise evaluation of the ordered sum yields 3z²−2cz−1/4.

**Lemma 1.20 (Both branches are critical).**

$$(\operatorname{CStarSchoenberg}.\operatorname{orderedDeriv}\left(a, bplus\right) = 0) \land (\operatorname{CStarSchoenberg}.\operatorname{orderedDeriv}\left(a, bminus\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarSendov.critical_both` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The factorization 3(z−bplus)(z−bminus) gives both zeros.

**Lemma 1.21 (All polynomial roots are in the disc).**

$$\forall j:\operatorname{Fin}\left(3\right), (a)\left(j\right) \in \operatorname{cstarDisc}\left(0, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarSendov.roots_in_disc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

Every polygon vertex has squared norm at most 82/100; the segments remain inside the unit disc.

**Lemma 1.22 (Both critical branches are in the disc).**

$$(bplus \in \operatorname{cstarDisc}\left(0, 1\right)) \land (bminus \in \operatorname{cstarDisc}\left(0, 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarSendov.critical_in_disc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The estimates |c|≤1 and |s|≤2 imply that both branches have norm at most one.

**Lemma 1.23 (No critical zero is close to one half).**

$$\forall z:\operatorname{C}\left(\operatorname{Set}.\operatorname{Icc}\left(((0):\mathbb{R}), 6\right), \mathbb{C}\right), (\operatorname{CStarSchoenberg}.\operatorname{orderedDeriv}\left(a, z\right) = 0) \Rightarrow (\neg z \in \operatorname{cstarDisc}\left(\operatorname{SMul}.\operatorname{smul}\left(\frac{((1):\mathbb{C})}{((2):\mathbb{C})}, ((1):\operatorname{C}\left(\operatorname{Set}.\operatorname{Icc}\left(((0):\mathbb{R}), 6\right), \mathbb{C}\right))\right), 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarSendov.no_critical_in_half_disc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

A continuous zero follows one of the two branches on the entire connected interval. The first branch is farther than one from 1/2 at t=6; the second is farther than one at t=0.

**Lemma 1.24 (Positive barycentric representations).**

$$\forall z:\operatorname{C}\left(\operatorname{Set}.\operatorname{Icc}\left(((0):\mathbb{R}), 6\right), \mathbb{C}\right), (\operatorname{CStarSchoenberg}.\operatorname{orderedDeriv}\left(a, z\right) = 0) \Rightarrow (\operatorname{IsConvexForm}\left(a, z\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarSendov.critical_convex_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The positive pointwise weights are inverse squared distances, divided by their sum. None of the distances vanishes, so the weights are continuous and invertible.

**Definition 1.25 (Krishna's Conjecture 2.5).**

$$(claimSendov) \Leftrightarrow (\forall A:Type, [\operatorname{CStarAlgebra}\left(A\right)] [\operatorname{PartialOrder}\left(A\right)] [\operatorname{StarOrderedRing}\left(A\right)] \forall n:\mathbb{N}, (2 \le n) \Rightarrow (\forall a:\operatorname{Fin}\left(n\right) \to A, (\forall j:\operatorname{Fin}\left(n\right), (a)\left(j\right) \in \operatorname{cstarDisc}\left(0, 1\right)) \Rightarrow (\forall b:\operatorname{Fin}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right)\right) \to A, (\forall k:\operatorname{Fin}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right)\right), \operatorname{CStarSchoenberg}.\operatorname{orderedDeriv}\left(a, (b)\left(k\right)\right) = 0) \Rightarrow ((\forall k:\operatorname{Fin}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right)\right), (b)\left(k\right) \in \operatorname{cstarDisc}\left(0, 1\right)) \Rightarrow ((\forall k:\operatorname{Fin}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right)\right), \operatorname{IsConvexForm}\left(a, (b)\left(k\right)\right)) \Rightarrow (\forall j:\operatorname{Fin}\left(n\right), \exists z:A, (\operatorname{CStarSchoenberg}.\operatorname{orderedDeriv}\left(a, z\right) = 0) \land (z \in \operatorname{cstarDisc}\left((a)\left(j\right), 1\right))))))))$$

*Formalization.* `D5/S3/Quantum/Algebra/CStarSendov.claimSendov` (`✓ std3`).

*Citation.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

Conjecture 2.5, p. 3: “Let 𝒜 be a unital C*-algebra. Let n ∈ ℕ∖{1} and p(z)=(z−a₁)(z−a₂)⋯(z−aₙ)∈𝒜[z] be such that a₁, a₂, …, aₙ ∈ 𝔻̅*(0,1). Define p′(z)=∑_{j=1}ⁿ (z−a₁)⋯(z−aⱼ)̂⋯(z−aₙ), ∀z∈𝒜, where the term with cap is missing. Assume that p′ admits roots in 𝒜, say b₁, b₂, …, bₙ₋₁ ∈ 𝔻̅*(0,1) and each bₖ can be written in the form of Equation (1). Then for each aⱼ, 1≤j≤n, there exists a zero b of p′ such that b ∈ 𝔻̅*(aⱼ,1).” The encoding uses zero-based Fin indices, degrees 2≤n, and unital algebras in Type with PartialOrder and StarOrderedRing. The derivative is the existing orderedDeriv, omitting one factor at a time. The conclusion allows any zero, rather than only the listed b values.

**Theorem 1.26 (Conjecture 2.5 is false).**

$$\neg claimSendov$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CStarSendov.result` (`✓ std3`). ∎

*Resolves.* `Problems/krishna-2022-cstar-sendov` (refuted) by `D5/S3/Quantum/Algebra/CStarSendov.result` and `D5/S3/Quantum/Algebra/CStarSendovCommutative.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"krishna-2022-cstar-sendov","declaration_gid":"D5/S3/Quantum/Algebra/CStarSendov.result","resolution_kind":"refuted"} -->

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"krishna-2022-cstar-sendov","declaration_gid":"D5/S3/Quantum/Algebra/CStarSendovCommutative.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. Mahesh Krishna (2022). *C*-algebraic Gauss-Lucas Theorem and C*-algebraic Sendov's Conjecture*. DOI: [10.48550/arXiv.2203.06916](https://doi.org/10.48550/arXiv.2203.06916). URL: <https://arxiv.org/abs/2203.06916v1>.

*Commentary.*

The cubic in C(Set.Icc 0 6,ℂ) satisfies all the disc and barycentric hypotheses. The two critical branches exchange between the endpoints, and neither is uniformly within one of the constant root 1/2.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.IsConvexForm`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.a`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.bminus`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.bplus`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.bs`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.c`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.cfun`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.claimSendov`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.critical_both`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.critical_convex_form`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.critical_in_disc`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.cstarDisc`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.cx`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.cy`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.dfun`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.no_critical_in_half_disc`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.ordered_deriv_apply`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.ramp`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.result`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.rootI`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.rootR`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.rootU`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.rootV`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.roots_in_disc`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.s`
- Truth anchor: `D5/S3/Quantum/Algebra/CStarSendov.sfun`
- Dependency: [D5/S3/Quantum/Algebra/CStarSchoenberg](CStarSchoenberg.md)
