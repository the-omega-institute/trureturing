# The modified Bessel product need not be log-convex in its order

## Abstract

Half-integer modified Bessel values contradict log-convexity in the order.

**Definition 1.1 (The second-kind function at noninteger orders).**

$$\forall nu \in \mathbb {R},\; \forall u \in \mathbb {R},\; \operatorname {besselK}\left(nu, u\right) = \frac{\frac{\operatorname {Real.pi}}{2} \cdot \left(\operatorname {besselI}\left(-nu, u\right) - \operatorname {besselI}\left(nu, u\right)\right)}{\operatorname {Real.sin}\left(nu \cdot \operatorname {Real.pi}\right)}$$

*Formalization.* `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.besselK` (`✓ std3`).

*Citation.* NIST Digital Library of Mathematical Functions (2026). *Modified Bessel Functions: Definitions and Basic Properties; Connection Formulas*. URL: <https://dlmf.nist.gov/10.25>.

*Commentary.*

DLMF §10.25(ii), equation 10.25.2 (https://dlmf.nist.gov/10.25.E2), defines the first-kind function by: “I_ν(z) = (½z)^ν Σ_{k=0}^∞ (¼z²)^k / (k! Γ(ν+k+1)).” The page states that the principal branch of I_ν(z) “is analytic in ℂ∖(−∞,0]”.

The first-kind function besselI in every formula is the existing D5.S3.Analytic.BesselRatioLogConcavity.Result.besselI. At real z=u>0, the principal branch agrees with the real power: (u/2)^nu (u²/4)^k=(u/2)^(2k+nu). Thus the owner's summand (u/2)^(2k+nu)/(k! Gamma(k+nu+1)) has exactly the DLMF normalization.

DLMF §10.27(ii), equation 10.27.4 (https://dlmf.nist.gov/10.27.E4), gives: “K_ν(z) = ½π (I_{−ν}(z) − I_ν(z)) / sin(νπ)”, followed by “When ν is an integer limiting values are taken”. Equation 10.27.1 (https://dlmf.nist.gov/10.27.E1) states: “I_{−n}(z) = I_n(z), n an integer.”

For positive u and noninteger nu, besselK is this standard connection formula with the same first-kind normalization. Lean's real quotient is a total operation; only noninteger orders enter the assertion below, so no value assigned by that operation at an integer is used. Integer-order K values require the stated limiting convention and are outside this definition's asserted correspondence.

**Definition 1.2 (The product at a fixed argument).**

$$\forall u \in \mathbb {R},\; \forall nu \in \mathbb {R},\; \operatorname {P}\left(u, nu\right) = \operatorname {besselI}\left(nu, u\right) \cdot \operatorname {besselK}\left(nu, u\right)$$

*Formalization.* `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.P` (`✓ std3`).

*Citation.* Á. Baricz and S. Ponnusamy (2013). *On Turán type inequalities for modified Bessel functions*. URL: <https://arxiv.org/abs/1010.3346>.

*Commentary.*

On printed p. 1 of arXiv:1010.3346v1, §1, Baricz and Ponnusamy write: “Let us denote with Iν and Kν the modified Bessel functions of the first and second kind, respectively. For definitions, recurrence formulas and other properties of modified Bessel functions of the first and second kind we refer to the classical book of G.N. Watson [Wa].”

The product is P(u,nu)=Iν(u)Kν(u). The argument u is its first parameter, while the order nu is its second parameter. The defining-series and connection-formula quotations above are from DLMF; the paper's passage identifies the functions and refers the reader to Watson.

**Definition 1.3 (The necessary midpoint product inequality).**

$$claim = \left(\forall u \in \mathbb {R},\; (0 < u) \Rightarrow (\forall nu \in \mathbb {R},\; \forall h \in \mathbb {R},\; (-1 < nu) \Rightarrow ((0 < h) \Rightarrow ((\forall n \in \mathbb {Z},\; nu \ne n) \Rightarrow ((\forall n \in \mathbb {Z},\; nu + h \ne n) \Rightarrow ((\forall n \in \mathbb {Z},\; nu + 2 \cdot h \ne n) \Rightarrow ((\operatorname {P}\left(u, nu + h\right))^{2} \le \operatorname {P}\left(u, nu\right) \cdot \operatorname {P}\left(u, nu + 2 \cdot h\right)))))))\right)$$

*Formalization.* `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.claim` (`✓ std3`).

*Citation.* Á. Baricz and S. Ponnusamy (2013). *On Turán type inequalities for modified Bessel functions*. URL: <https://arxiv.org/abs/1010.3346>.

*Commentary.*

The final Conjecture in §3, printed page 7 of arXiv:1010.3346v1, reads: “Motivated by Theorems 1 and 2 we conjecture the following. Conjecture. The function ν ↦ I_ν(u)K_ν(u) is log-convex on (−1, ∞) for all u > 0 fixed.”

Theorem 1(4), printed page 4, states: “the function ν ↦ I_{√ν}(u)K_{√ν}(u) is log-convex on (0, ∞) for all u > 0 fixed;”

Theorem 2, printed page 6, with equation (19) joined to its sentence, states: “The function ν ↦ I_ν(u)K_ν(u) is decreasing and (0, ∞) for all u > 0 fixed. Moreover, for all ν ≥ 1/2 and u > 0 we have 2I_ν(u)K_ν(u) ≤ I_{ν−1}(u)K_{ν−1}(u) + I_{ν+1}(u)K_{ν+1}(u).” The word ‘and’ in the first sentence is retained from the source text.

For a positive function, log-convexity on (−1,∞) implies 2 log P(u,nu+h)≤log P(u,nu)+log P(u,nu+2h), hence P(u,nu+h)^2≤P(u,nu)P(u,nu+2h). The orders nu, nu+h and nu+2h all lie in the interval when nu>−1 and h>0. The formal assertion restricts to triples of noninteger orders, where the connection formula is valid. It is therefore weaker than the conjecture, and its refutation refutes the conjecture. The square-root parametrization in Theorem 1(4) is a different assertion.

**Theorem 1.4 (The half-integer Gamma normalization).**

$$\forall k \in \mathbb {N},\; \operatorname {Nat.factorial}\left(k\right) \cdot \operatorname {Real.Gamma}\left(k + \frac{1}{2}\right) \cdot (4)^{k} = \operatorname {Nat.factorial}\left(2 \cdot k\right) \cdot \operatorname {Real.sqrt}\left(\operatorname {Real.pi}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.gamma_factorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's Gamma duplication formula at k+1/2, together with the Gamma values at positive integers, gives the even-factorial identity after real-power normalization.

**Theorem 1.5 (The terms at order minus one half).**

$$\forall k \in \mathbb {N},\; \frac{(\frac{1}{2})^{2 \cdot k + -\frac{1}{2}}}{\operatorname {Nat.factorial}\left(k\right) \cdot \operatorname {Real.Gamma}\left(k + -\frac{1}{2} + 1\right)} = \frac{a}{\operatorname {Nat.factorial}\left(2 \cdot k\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.minus_term` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The private real constant a is (1/2)^(−1/2)/sqrt(pi). The half-integer Gamma identity converts each defining term of I−1/2(1) into a/(2k)!. Natural indices in real expressions are coerced to real numbers.

**Theorem 1.6 (The terms at order one half).**

$$\forall k \in \mathbb {N},\; \frac{(\frac{1}{2})^{2 \cdot k + \frac{1}{2}}}{\operatorname {Nat.factorial}\left(k\right) \cdot \operatorname {Real.Gamma}\left(k + \frac{1}{2} + 1\right)} = \frac{a}{\operatorname {Nat.factorial}\left(2 \cdot k + 1\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.plus_term` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One Gamma step and one factorial step transform the order-one-half summand into a/(2k+1)!.

**Theorem 1.7 (The elementary square-root factor).**

$$a = \operatorname {Real.sqrt}\left(\frac{2}{\operatorname {Real.pi}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.a_eq_sqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive real-power factor (1/2)^(−1/2) divided by sqrt(pi) equals sqrt(2/pi). Positivity determines the square root uniquely.

**Theorem 1.8 (The first two half-integer evaluations).**

$$(\operatorname {besselI}\left(-\frac{1}{2}, 1\right) = \operatorname {Real.sqrt}\left(\frac{2}{\operatorname {Real.pi}}\right) \cdot \operatorname {Real.cosh}\left(1\right)) \land (\operatorname {besselI}\left(\frac{1}{2}, 1\right) = \operatorname {Real.sqrt}\left(\frac{2}{\operatorname {Real.pi}}\right) \cdot \operatorname {Real.sinh}\left(1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.half_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the even and odd factorial terms gives cosh(1) and sinh(1), respectively. The prefactor is sqrt(2/pi).

**Theorem 1.9 (A Gamma recurrence for the summands).**

$$\forall nu \in \mathbb {R},\; \forall k \in \mathbb {N},\; (k + nu + 1 \ne 0) \Rightarrow (\operatorname {summand}\left(nu, k\right) = 2 \cdot \left(k + nu + 1\right) \cdot \operatorname {summand}\left(nu + 1, k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here summand(nu,k) denotes the defining Bessel summand at argument one. The Gamma recurrence relates adjacent orders at the same index, provided k+nu+1 is nonzero.

**Theorem 1.10 (An index-shift identity).**

$$\forall nu \in \mathbb {R},\; \forall k \in \mathbb {N},\; \operatorname {summand}\left(nu + 2, k\right) = 2 \cdot \left(k + 1\right) \cdot \operatorname {summand}\left(nu + 1, k + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Increasing the natural index raises the exponent by two and the factorial by one step. A factor 2(k+1) relates the resulting summands.

**Theorem 1.11 (The summand form of the order recurrence).**

$$\forall nu \in \mathbb {R},\; \forall k \in \mathbb {N},\; (k + 1 + nu + 1 \ne 0) \Rightarrow (\operatorname {summand}\left(nu, k + 1\right) = \operatorname {summand}\left(nu + 2, k\right) + 2 \cdot \left(nu + 1\right) \cdot \operatorname {summand}\left(nu + 1, k + 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combining the adjacent-order Gamma identity with the index shift gives the additive relation between three consecutive orders.

**Theorem 1.12 (The order recurrence at argument one).**

$$\forall nu \in \mathbb {R},\; (-2 < nu) \Rightarrow ((\forall k \in \mathbb {N},\; k + nu + 1 \ne 0) \Rightarrow (\operatorname {besselI}\left(nu, 1\right) = \operatorname {besselI}\left(nu + 2, 1\right) + 2 \cdot \left(nu + 1\right) \cdot \operatorname {besselI}\left(nu + 1, 1\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nu>−2 the series at nu+1 and nu+2 converge. The summand relation then proves convergence at nu and identifies its sum. Splitting off index zero yields Iν(1)=Iν+2(1)+2(nu+1)Iν+1(1). The nonzero hypotheses exclude the Gamma recurrence's exceptional arguments.

**Theorem 1.13 (The order minus three halves).**

$$\operatorname {besselI}\left(-\frac{3}{2}, 1\right) = \operatorname {besselI}\left(\frac{1}{2}, 1\right) - \operatorname {besselI}\left(-\frac{1}{2}, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.recurrence_minus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The order recurrence at nu=−3/2 expresses I−3/2(1) as I1/2(1)−I−1/2(1).

**Theorem 1.14 (The order three halves).**

$$\operatorname {besselI}\left(\frac{3}{2}, 1\right) = \operatorname {besselI}\left(-\frac{1}{2}, 1\right) - \operatorname {besselI}\left(\frac{1}{2}, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.recurrence_plus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The order recurrence at nu=−1/2 expresses I3/2(1) as I−1/2(1)−I1/2(1). This is sqrt(2/pi)(cosh(1)−sinh(1)).

**Theorem 1.15 (Three exact product values).**

$$(\operatorname {P}\left(1, -\frac{1}{2}\right) = \frac{1 + \operatorname {Real.exp}\left(-2\right)}{2}) \land ((\operatorname {P}\left(1, \frac{1}{2}\right) = \frac{1 - \operatorname {Real.exp}\left(-2\right)}{2}) \land (\operatorname {P}\left(1, \frac{3}{2}\right) = 2 \cdot \operatorname {Real.exp}\left(-2\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.product_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sine values at −pi/2, pi/2 and 3pi/2 are −1, 1 and −1. Substituting the four first-kind values into the connection formula gives P(1,−1/2)=(1+exp(−2))/2, P(1,1/2)=(1−exp(−2))/2 and P(1,3/2)=2exp(−2). The factor pi cancels the square 2/pi of the common prefactor.

**Theorem 1.16 (A rational upper bound on the exponential).**

$$(0 < \operatorname {Real.exp}\left(-2\right)) \land (\operatorname {Real.exp}\left(-2\right) < \frac{1}{7})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.exp_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential is positive. The lower bound exp(1)>8/3 implies exp(1)^2>7, so exp(−2)=1/exp(1)^2<1/7.

**Theorem 1.17 (The strict reversal of the midpoint inequality).**

$$\operatorname {P}\left(1, -\frac{1}{2}\right) \cdot \operatorname {P}\left(1, \frac{3}{2}\right) < (\operatorname {P}\left(1, \frac{1}{2}\right))^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put t=exp(−2). The product difference is (1+t)t−(1−t)^2/4=(3t^2+6t−1)/4. A rational bound on exp(1) gives an upper bound on t for which this expression is strictly negative.

**Theorem 1.18 (Half-integer orders are noninteger).**

$$\forall k \in \mathbb {Z},\; \forall n \in \mathbb {Z},\; (\operatorname {Int.cast}\left(k\right):\mathbb {R}) + \frac{1}{2} \ne (\operatorname {Int.cast}\left(n\right):\mathbb {R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.half_noninteger` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For integers k and n, the real number k+1/2 differs from n because doubling would equate an odd integer with an even one.

**Theorem 1.19 (Refutation of order log-convexity).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/baricz-ponnusamy-2013-bessel-product-order-log-convexity` (refuted) by `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"baricz-ponnusamy-2013-bessel-product-order-log-convexity","declaration_gid":"D5/S3/Analytic/BesselProductOrderLogConvexity/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Á. Baricz and S. Ponnusamy (2013). *On Turán type inequalities for modified Bessel functions*. URL: <https://arxiv.org/abs/1010.3346>.

*Commentary.*

Take u=1, nu=−1/2 and h=1. All three orders are noninteger and greater than −1. The strict product comparison contradicts the asserted three-point inequality. Thus the positive modified Bessel product is not log-convex in its order on the entire interval (−1,∞) for every positive argument. The conclusion concerns the order itself, rather than the square-root parametrization.

## References

- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.P`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.a_eq_sqrt`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.besselK`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.claim`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.exp_bound`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.gamma_factorial`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.half_noninteger`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.half_values`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.lower`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.minus_term`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.plus_term`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.product_values`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.recurrence`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.recurrence_minus`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.recurrence_plus`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.result`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.shift`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.step`
- Truth anchor: `D5/S3/Analytic/BesselProductOrderLogConvexity/Result.witness`
- Dependency: [D5/S3/Analytic/BesselRatioLogConcavity/Result](../BesselRatioLogConcavity/Result.md)
