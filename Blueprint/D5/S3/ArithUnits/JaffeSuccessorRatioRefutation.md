# Jaffe's unrestricted successor-ratio conjecture is false

## Abstract

The primitive Frobenius successor ratio exceeds five for an admissible pair of integers.

**Definition 1.1 (Primitive nonnegative integer coefficients).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall n \in \mathbb{Z},\; \operatorname{Represented}\left(a, b, n\right) \Leftrightarrow \left(\exists x \in \mathbb{Z},\; \exists y \in \mathbb{Z},\; 0 \le x \land \left(0 \le y \land \left(\operatorname{gcd}\left(\operatorname{natAbs}\left(x\right), \operatorname{natAbs}\left(y\right)\right) = 1 \land a \cdot x + b \cdot y = n\right)\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.Represented` (`✓ std3`).

*Citation.* Grace Natalie Jaffe (2026). *Denominators in the Farey Sequence, the Stern Sequence, and the Frobenius Problem with Relatively Prime Multipliers*. URL: <https://arxiv.org/abs/2610.17267v1>.

*Commentary.*

Represented(a,b,n) means that n = ax + by for nonnegative integers x and y with gcd(x,y)=1. The gcd is the natural gcd of their absolute values. Both coordinate axes are included. Passing between nonnegative integers and natural coefficients preserves the equality and coprimality.

**Definition 1.2 (The full integer complement).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \forall n \in \mathbb{Z},\; n \in \operatorname{missing}\left(a, b\right) \Leftrightarrow \left(\neg \operatorname{Represented}\left(a, b, n\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.missing` (`✓ std3`).

*Citation.* Grace Natalie Jaffe (2026). *Denominators in the Farey Sequence, the Stern Sequence, and the Frobenius Problem with Relatively Prime Multipliers*. URL: <https://arxiv.org/abs/2610.17267v1>.

*Commentary.*

The set missing(a,b) consists of all integers without a primitive nonnegative representation. Its domain is the whole integer line, including the negative integers.

**Definition 1.3 (Greatest missing integer or infinity).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \left(\forall m \in \mathbb{Z},\; \operatorname{IsGreatest}\left(\operatorname{missing}\left(a, b\right), m\right) \Rightarrow \operatorname{sourceG}\left(a, b\right) = m\right) \land \left(\left(\neg \left(\exists m \in \mathbb{Z},\; \operatorname{IsGreatest}\left(\operatorname{missing}\left(a, b\right), m\right)\right)\right) \Rightarrow \operatorname{sourceG}\left(a, b\right) = \infty\right)$$

*Formalization.* `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.sourceG` (`✓ std3`).

*Citation.* Grace Natalie Jaffe (2026). *Denominators in the Farey Sequence, the Stern Sequence, and the Frobenius Problem with Relatively Prime Multipliers*. URL: <https://arxiv.org/abs/2610.17267v1>.

*Commentary.*

sourceG(a,b) takes values in the extended real numbers. When the integer complement has a greatest element m, its value is the real embedding of m. When there is no greatest element, its value is positive infinity. For positive coprime A and B at least three, the counting argument below proves an actual greatest missing integer at least one.

**Definition 1.4 (The next integer coprime to the first argument).**

$$\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; \operatorname{successor}\left(a, b\right) = \operatorname{sInf}\left(\{c\in\mathbb{Z}: b < c \land \operatorname{gcd}\left(\operatorname{natAbs}\left(a\right), \operatorname{natAbs}\left(c\right)\right) = 1\}\right)$$

*Formalization.* `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.successor` (`✓ std3`).

*Citation.* Grace Natalie Jaffe (2026). *Denominators in the Farey Sequence, the Stern Sequence, and the Frobenius Problem with Relatively Prime Multipliers*. URL: <https://arxiv.org/abs/2610.17267v1>.

*Commentary.*

successor(a,b) is the integer infimum of the integers c strictly greater than b and coprime to a. For a,b at least three this set is nonempty: a(b+1)+1 is greater than b and coprime to a. It is bounded below by b, so the integer infimum belongs to the set and is its least element.

**Definition 1.5 (The whole unrestricted Conjecture 7.3).**

$$fullClaim \Leftrightarrow \left(\forall a \in \mathbb{Z},\; \forall b \in \mathbb{Z},\; 3 \le a \Rightarrow \left(3 \le b \Rightarrow \left(\operatorname{gcd}\left(\operatorname{natAbs}\left(a\right), \operatorname{natAbs}\left(b\right)\right) = 1 \Rightarrow \frac{\operatorname{sourceG}\left(a, \operatorname{successor}\left(a, b\right)\right)}{\operatorname{sourceG}\left(a, b\right)} \le 5\right)\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.fullClaim` (`✓ std3`).

*Citation.* Grace Natalie Jaffe (2026). *Denominators in the Farey Sequence, the Stern Sequence, and the Frobenius Problem with Relatively Prime Multipliers*. URL: <https://arxiv.org/abs/2610.17267v1>.

*Commentary.*

For every pair of coprime integers a,b at least three, the claim bounds sourceG(a,successor(a,b))/sourceG(a,b) by five. No relation a<b is assumed. The coefficients, complement and successor have exactly the meanings given above. The same assertion is Conjecture 8.3 in the earlier thesis.

**Theorem 1.6 (The full conjecture has a counterexample).**

$$\neg fullClaim$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/jaffe-primitive-frobenius-successor-ratio` (refuted) by `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jaffe-primitive-frobenius-successor-ratio","declaration_gid":"D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Grace Natalie Jaffe (2026). *Denominators in the Farey Sequence, the Stern Sequence, and the Frobenius Problem with Relatively Prime Multipliers*. URL: <https://arxiv.org/abs/2610.17267v1>.

*Commentary.*

Take a=87841397512641630 and b=7. The integer a is coprime to 7 and 49, and each integer from 8 through 48 is noncoprime to a. Hence successor(a,7)=49. Let H(n) count all nonnegative solutions of Ax+By=n, and let P(n) count the primitive ones. Residues modulo B place H(n) between floor(n/(AB)) and floor(n/(AB))+1. Partitioning by gcd(x,y) and applying Mobius inversion gives AB P(n) >= phi(n)-AB tau(n), where tau(n) is the positive-divisor count. Factoring phi and tau over prime powers gives n tau(n)^2 <= 16^7 phi(n)^2. For primes at least seven the corresponding factor has constant one; a factor sixteen suffices for each smaller prime, of which there are at most seven. Therefore every n>16^7(AB)^2 has a primitive representation. Since 1 is missing when A,B>=3, the entire integer complement has a greatest element at least one. Apply this to (a,7) and (a,49), obtaining actual finite positive maxima m and M. A primitive representation of 7m for (a,49) would force its first coefficient to be divisible by 7. Dividing that coefficient preserves coprimality and would represent m for (a,7), a contradiction. Thus M>=7m and M/m>=7>5. The quotient uses these actual maxima; their numerical values are unnecessary. Finiteness and scaling are prior ingredients of the source's Theorems 4.3 and 7.1. The added condition a<b would define a different assertion, whose truth is not established by this counterexample.

## References

- Truth anchor: `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.Represented`
- Truth anchor: `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.fullClaim`
- Truth anchor: `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.missing`
- Truth anchor: `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.result`
- Truth anchor: `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.sourceG`
- Truth anchor: `D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.successor`
