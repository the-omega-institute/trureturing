# The whole A252505 identity and its native counting bridges

## Abstract

Native counting and inverse definitions for the whole A252505 convolution.

The universal convolution is open in Lean. The statements below give the unchanged target and its native counting and recursion interfaces. No settling theorem or Proved open-problem resolution is asserted.

**Definition 1.1 (The prime fourth-power exclusion).**

$$\forall d \in Nat,\; \operatorname{FourthPowerFree}\left(d\right) \Leftrightarrow \left(\forall p \in Nat,\; \operatorname{Nat}.\operatorname{Prime}\left(p\right) \Rightarrow Not (p^{4} \mid d)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.FourthPowerFree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

For a positive divisor d, every prime p is excluded when p^4 divides d. No restriction on the size or number of prime factors is imposed.

**Definition 1.2 (The actual fourth-power-free divisor count).**

$$\forall n \in Nat,\; \operatorname{a}\left(n\right) = (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((fun d \mapsto \operatorname{FourthPowerFree}\left(d\right)), \operatorname{Nat}.\operatorname{divisors}\left(n\right)\right)\right):Int)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

OEIS A252505 NAME counts the positive fourth-power-free divisors. Nat.divisors contains exactly those positive divisors when n is positive. The count is cast to Int.

**Definition 1.3 (The original rational equation).**

$$\forall n \in Nat,\; \forall x \in Nat,\; \forall y \in Nat,\; \operatorname{UnitFractionPair}\left(n, (x,y)\right) \Leftrightarrow \left(0 < x \land \left(0 < y \land \left(x \le y \land \frac{1}{(n:Rat)} = \frac{1}{(x:Rat)} + \frac{1}{(y:Rat)}\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.UnitFractionPair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

Both denominators are positive naturals; their order is non-strict, so x=y is included. The equation is an equality in Rat.

**Definition 1.4 (The actual unit-fraction pair count).**

$$\forall n \in Nat,\; \operatorname{b}\left(n\right) = (\operatorname{Nat}.\operatorname{card}\left(Subtype\left((fun xy \mapsto \operatorname{UnitFractionPair}\left(n, xy\right))\right)\right):Int)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.b` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

OEIS A018892 is represented by the cardinality of the original solution subtype of Nat times Nat, rather than by an assumed divisor formula. The factor-pair equivalence proves this subtype finite for every positive n.

**Definition 1.5 (The ordinary positive divisor count).**

$$\forall n \in Nat,\; \operatorname{tau}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Nat}.\operatorname{divisors}\left(n\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.tau` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

tau(n) is the number of positive divisors, including one and n when n is positive.

**Definition 1.6 (The ordinary ceiling divisor sum).**

$$\forall n \in Nat,\; \operatorname{h}\left(n\right) = \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{divisors}\left(n\right), (fun d \mapsto (\operatorname{Nat}.\operatorname{ceil}\left(\frac{(\operatorname{tau}\left(d\right):Rat)}{2}\right):Int))\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.h` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

OEIS A140773 sums the ceiling of tau(d)/2 over all positive divisors d. The cast to Rat precedes division; Nat.ceil agrees with the ordinary ceiling because this rational is nonnegative.

**Definition 1.7 (The integer parity).**

$$\forall n \in Nat,\; \operatorname{g}\left(n\right) = \operatorname{h}\left(n\right) \bmod 2$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.g` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

OEIS A369255 is the Int remainder h(n) modulo two, hence zero or one.

**Definition 1.8 (The canonical inverse with the source recursion).**

$$\operatorname{c}\left(1\right) = 1 \land \left(\forall n \in Nat,\; 1 < n \Rightarrow \operatorname{c}\left(n\right) = 0 - \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{properDivisors}\left(n\right), (fun d \mapsto \operatorname{g}\left(\operatorname{Nat}.\operatorname{div}\left(n, d\right)\right) \cdot \operatorname{c}\left(d\right))\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.c` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

The implementation directly reuses ArithmeticFunction.dirichletInverse over Int. Its value at one is one, and dirichletInverseFun_apply_ne supplies precisely this proper-divisor recursion. The private c_recursion proof verifies both clauses. The positive-domain uniqueness theorem below identifies it with the independently specified A378214; index zero is outside the target.

**Definition 1.9 (The independent recursive specification).**

$$\forall v \in Nat \to Int,\; \operatorname{InverseRecursion}\left(v\right) = \left(\operatorname{v}\left(1\right) = 1 \land \left(\forall n \in Nat,\; 1 < n \Rightarrow \operatorname{v}\left(n\right) = 0 - \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{properDivisors}\left(n\right), (fun d \mapsto \operatorname{g}\left(\operatorname{Nat}.\operatorname{div}\left(n, d\right)\right) \cdot \operatorname{v}\left(d\right))\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.InverseRecursion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

This predicate fixes the positive-domain values and imposes no value at zero.

**Definition 1.10 (The unchanged complete conjecture).**

$$claim = \left(\forall n \in Nat,\; 1 \le n \Rightarrow \operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{divisors}\left(n\right), (fun d \mapsto \operatorname{b}\left(d\right) \cdot \operatorname{c}\left(\operatorname{Nat}.\operatorname{div}\left(n, d\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

OEIS A252505 FORMULA: a(n) = Sum_{d|n} A018892(d)*A378214(n/d). [Conjectured]. This definition includes n=1, arbitrary prime support and every exponent. It is an unproved proposition in this module.

**Definition 1.11 (Finite ordered factor pairs).**

$$\forall n \in Nat,\; \operatorname{factorPairs}\left(n\right) = \operatorname{Finset}.\operatorname{filter}\left((fun uv \mapsto \operatorname{Prod}.\operatorname{fst}\left(uv\right) \le \operatorname{Prod}.\operatorname{snd}\left(uv\right)), \operatorname{Nat}.\operatorname{divisorsAntidiagonal}\left(n^{2}\right)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.factorPairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

These are all positive pairs u<=v with uv=n^2. The equality case is retained.

**Theorem 1.12 (Actual solutions equal the finite factor-pair count).**

$$\forall n \in Nat,\; 0 < n \Rightarrow \operatorname{b}\left(n\right) = (\operatorname{Finset}.\operatorname{card}\left(\operatorname{factorPairs}\left(n\right)\right):Int)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.unit_fraction_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

Clearing nonzero rational denominators gives xy=n(x+y), which forces x>n and y>n. Subtract n from both entries. The inverse adds n to each factor; both inverse laws and the non-strict order are checked.

**Theorem 1.13 (The faithful divisor formula).**

$$\forall n \in Nat,\; 0 < n \Rightarrow 2 \cdot \operatorname{b}\left(n\right) = (\operatorname{tau}\left(n^{2}\right):Int) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.unit_fraction_divisor_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

Swap the two factors. Each off-diagonal orbit has two entries; the unique fixed pair is (n,n). Thus 2b(n)=tau(n^2)+1. This derives the formula from the rational solution definition, including x=y=2n.

**Theorem 1.14 (Uniqueness on the full positive domain).**

$$\forall v \in Nat \to Int,\; \operatorname{InverseRecursion}\left(v\right) \Rightarrow \left(\forall n \in Nat,\; 0 < n \Rightarrow \operatorname{v}\left(n\right) = \operatorname{c}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.inverse_recursion_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The OEIS Foundation Inc. (2026). *OEIS A252505 and the linked unit-fraction and inverse sequences*. URL: <https://oeis.org/A252505>.

*Commentary.*

Strong induction uses only positive proper divisors, each strictly smaller than n. The n=1 clause comes directly from the specification. The arbitrary value v(0) is immaterial.

The remaining whole gap is b=a*g for the independently defined functions. The remaining native fourth-power-free and ceiling exponent-box bridges require a real whole-proof consumer. A finite-prime-support series proof must then encode divisor convolution, prove its series identities, prove the zero-or-one coefficient law, and descend the integral identity before reducing modulo two. Final inverse cancellation is then required. These missing steps are not certified by the native bridges above.

## References

- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.FourthPowerFree`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.InverseRecursion`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.UnitFractionPair`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.a`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.b`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.c`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.claim`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.factorPairs`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.g`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.h`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.inverse_recursion_unique`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.tau`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.unit_fraction_count`
- Truth anchor: `D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.unit_fraction_divisor_formula`
