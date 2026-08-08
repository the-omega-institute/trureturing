# Golden Names

## Abstract

Bounded Zeckendorf strings form injectively valued Fibonacci-sized layers.

A length-Q golden name reuses the canonical W-digit representation and requires every occupied Fibonacci index to be below Q plus two. This is equivalent to a length-Q binary word with no adjacent occupied positions.

**Definition 1.1 (Bounded Zeckendorf golden name).**

Lean statement: `D5/S0/Tower/GoldenNames.GoldenName`

*Formalization.* `D5/S0/Tower/GoldenNames.GoldenName` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The representation is a bounded subtype of the repository's existing WDigitString type, so Zeckendorf canonicality remains the single source of the binary nonadjacency constraint.

**Theorem 1.2 (Golden-name layers have Fibonacci cardinality).**

$$\forall Q \in N,\; \operatorname{card}\left(\operatorname{GoldenName}\left(Q\right)\right) = \operatorname{Fib}\left(Q + 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenNames.golden_name_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restricting mathlib's Zeckendorf equivalence to values below Fib(Q+2) gives an equivalence between the name layer and that finite initial interval. The empty and one-position layers follow without separate hypotheses.

**Definition 1.3 (Negative golden-power name value).**

Lean statement: `D5/S0/Tower/GoldenNames.nameValue`

*Formalization.* `D5/S0/Tower/GoldenNames.nameValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An occupied Fibonacci index k contributes goldenRatio to the integer power k minus Q plus two. These exponents are exactly minus one through minus Q in the position order.

**Theorem 1.4 (Golden-name values are injective).**

$$\forall Q \in N,\; \operatorname{Injective}\left(\operatorname{nameValue}\left(Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenNames.nameValue_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common positive golden power clears the negative exponents. Mathlib's golden-power Fibonacci identity and golden-ratio irrationality force the Fibonacci sums to agree, after which Zeckendorf uniqueness identifies the names.

## References

- Truth anchor: `D5/S0/Tower/GoldenNames.GoldenName`
- Truth anchor: `D5/S0/Tower/GoldenNames.golden_name_card`
- Truth anchor: `D5/S0/Tower/GoldenNames.nameValue`
- Truth anchor: `D5/S0/Tower/GoldenNames.nameValue_injective`
- Dependency: [D5/S0/Conventions/WDigits](../Conventions/WDigits.md)
