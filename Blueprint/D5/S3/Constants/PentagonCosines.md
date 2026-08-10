# Pentagon Cosines

## Abstract

The doubled pentagon cosines read the golden ratio, its inverse, and root five.

**Theorem 1.1 (The pentagon angles read the golden ratio exactly).**

$$2\operatorname{cos}(\pi/5)=\varphi,\qquad 2\operatorname{cos}(2\pi/5)=\varphi^{-1},\qquad 2\operatorname{cos}(\pi/5)+2\operatorname{cos}(2\pi/5)=\sqrt{5}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/PentagonCosines.pentagon_golden_cosines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Doubling the cosine at the acute pentagon angle pi over five yields the golden ratio itself, and doubling it at the obtuse angle two pi over five yields the inverse golden ratio. The two doubles sum to sqrt(5), the square root of the discriminant five shared by both readings, and the obtuse double is additionally proved irrational, so no rational register accommodates the five-fold turn. These are classical pentagon identities, proved here natively over the pinned library.

The proof starts from the library's closed form for the cosine of pi over five, namely (1 + sqrt(5)) / 4, derives the obtuse value (sqrt(5) - 1) / 4 by the double-angle formula, and identifies the two doubles with the golden ratio and its inverse through the library's golden-ratio and golden-conjugate identities. The sum clause is the difference identity between the golden ratio and its conjugate, and the irrationality clause transports the irrationality of the golden ratio through inversion.

## References

- Truth anchor: `D5/S3/Constants/PentagonCosines.pentagon_golden_cosines`
