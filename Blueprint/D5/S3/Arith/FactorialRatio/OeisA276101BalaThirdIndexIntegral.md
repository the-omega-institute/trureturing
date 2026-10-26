# Bala A276101: integrality at every natural index

## Abstract

Bala A276101 integrality.

**Definition 1.1 (a).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{factorial}\left(10 \cdot n\right): \mathbb{R}) \cdot \operatorname{Real}.\operatorname{Gamma}\left(\frac{(n: \mathbb{R})}{3} + 1\right)}{(\operatorname{Nat}.\operatorname{factorial}\left(5 \cdot n\right): \mathbb{R}) \cdot \operatorname{Real}.\operatorname{Gamma}\left(\frac{10 \cdot (n: \mathbb{R})}{3} + 1\right) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot n\right): \mathbb{R})}$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.a` (`✓ std3`).

*Citation.* Peter Bala (2016). *Some integer ratios of factorials*. URL: <https://oeis.org/A276098/a276098.pdf>.

*Commentary.*

OEIS A276101, NAME (unpaginated): "a(n) = (10*n)!*(n/3)!/((5*n)!*(10*n/3)!*(2*n)!)." Bala, page 1: "throughout these notes x! is shorthand for Γ(x + 1)". Natural factorials are cast to the reals.

**Definition 1.2 (claim).**

$$\operatorname{claim} = (\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; \operatorname{a}\left(n\right) = (z: \mathbb{R}))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.claim` (`✓ std3`).

*Citation.* Peter Bala (2016). *Some integer ratios of factorials*. URL: <https://oeis.org/A276098/a276098.pdf>.

*Commentary.*

OEIS A276101, COMMENTS (unpaginated): "This is only conjecturally an integer sequence." Bala, page 5: "are also integral for n ≥ 0." Naturals include zero, and integrality means equality to the real cast of an integer.

**Definition 1.3 (Parameters).**

$$\forall d \in \mathbb{N},\; \forall M \in \mathbb{N},\; \forall B \in \mathbb{N},\; \forall C \in \mathbb{N},\; \forall L \in \mathbb{N},\; \operatorname{Parameters}\left(d, M, B, C, L\right) = (((d = 3) \land ((M = 10) \land ((B = 5) \land ((C = 2) \land (L = 3))))) \lor ((d = 5) \land ((M = 6) \land ((B = 3) \land ((C = 2) \land (L = 1))))))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.Parameters` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2016). *Some integer ratios of factorials*. URL: <https://oeis.org/A276098/a276098.pdf>.

*Commentary.*

The two parameter systems for the third-index and fifth-index Gamma ratios.

**Definition 1.4 (progression).**

$$\forall d \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{progression}\left(d, L, n\right) = \prod_{k \in \operatorname{Finset}.\operatorname{range}\left(L \cdot n\right)} (n + d \cdot \left(k + 1\right))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.progression` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2016). *Some integer ratios of factorials*. URL: <https://oeis.org/A276098/a276098.pdf>.

*Commentary.*

The product of n+d(k+1) over k in Finset.range (Ln), with the empty product equal to one.

**Theorem 1.5 (progression_ne_zero).**

$$\forall d \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall n \in \mathbb{N},\; (0 < d) \implies (\operatorname{progression}\left(d, L, n\right) \neq 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.progression_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2016). *Some integer ratios of factorials*. URL: <https://oeis.org/A276098/a276098.pdf>.

*Commentary.*

Every factor of the progression is positive when d is positive.

**Theorem 1.6 (nonmultiple_dvd).**

$$\forall d \in \mathbb{N},\; \forall M \in \mathbb{N},\; \forall B \in \mathbb{N},\; \forall C \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall n \in \mathbb{N},\; (\operatorname{Parameters}\left(d, M, B, C, L\right)) \implies ((\neg (d \mid n)) \implies (\operatorname{Nat}.\operatorname{factorial}\left(B \cdot n\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(C \cdot n\right) \cdot \operatorname{progression}\left(d, L, n\right) \mid \operatorname{Nat}.\operatorname{factorial}\left(M \cdot n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.nonmultiple_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2016). *Some integer ratios of factorials*. URL: <https://oeis.org/A276098/a276098.pdf>.

*Commentary.*

For either parameter system, if d does not divide n, the product of the two denominator factorials and the progression divides the numerator factorial.

**Theorem 1.7 (gamma_ratio).**

$$\forall d \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall n \in \mathbb{N},\; (0 < d) \implies (\frac{\operatorname{Real}.\operatorname{Gamma}\left(\frac{(n: \mathbb{R})}{(d: \mathbb{R})} + 1\right)}{\operatorname{Real}.\operatorname{Gamma}\left(\frac{(1 + d \cdot L: \mathbb{R}) \cdot (n: \mathbb{R})}{(d: \mathbb{R})} + 1\right)} = \frac{(d: \mathbb{R})^{L \cdot n}}{(\operatorname{progression}\left(d, L, n\right): \mathbb{R})})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.gamma_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2016). *Some integer ratios of factorials*. URL: <https://oeis.org/A276098/a276098.pdf>.

*Commentary.*

For every positive natural d, the Gamma recurrence reduces this ratio to a power of d divided by the progression product.

**Theorem 1.8 (ordinary_dvd).**

$$\forall m \in \mathbb{N},\; \operatorname{Nat}.\operatorname{factorial}\left(15 \cdot m\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(10 \cdot m\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(6 \cdot m\right) \mid \operatorname{Nat}.\operatorname{factorial}\left(30 \cdot m\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.ordinary_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2016). *Some integer ratios of factorials*. URL: <https://oeis.org/A276098/a276098.pdf>.

*Commentary.*

The product (15m)!(10m)!(6m)! divides (30m)!m!.

**Theorem 1.9 (result).**

$$\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; \operatorname{a}\left(n\right) = (z: \mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2016). *Some integer ratios of factorials*. URL: <https://oeis.org/A276098/a276098.pdf>.

*Commentary.*

Every natural index gives the real cast of an integer. Gamma recurrence and prime valuations prove the assertion for third indices, including zero.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.Parameters`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.a`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.claim`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.gamma_ratio`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.nonmultiple_dvd`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.ordinary_dvd`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.progression`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.progression_ne_zero`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral.result`
- Dependency: [D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility](BalaChebyshevFiveDivisibility.md)
- Dependency: [D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral](OeisA347855BalaThirdIndexIntegral.md)
