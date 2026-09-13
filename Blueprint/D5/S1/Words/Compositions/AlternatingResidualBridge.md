# Alternating Words and Residual Intervals

## Abstract

Blocked alternating words correspond to interlaced residual pairs.

Let a and b permute 1 through m, and write A and B for their prefix sums, starting at zero. The Lean permutations use Fin m, with one added to each value. The results include m=0. This chapter treats explicitly alternating words; the passage from all Wronskian contribution permutations to these words remains to be proved.

**Definition 1.1 (Nonnegative heights).**

$$\operatorname {Good}\left(h, w\right) \iff \forall k , 0 \le k \le \operatorname {length}\left(w\right) \implies 0 \le h + \operatorname {sum}\left(\operatorname {take}\left(k, w\right)\right)$$

*Formalization.* `D5/S1/Words/Compositions/AlternatingResidualBridge.Good` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Good requires every height, including the initial and final heights, to be nonnegative.

**Definition 1.2 (Blocked disjoint pairs).**

$$\operatorname {Unswappable}\left(h, \operatorname {cons}\left(x, \operatorname {cons}\left(y, w\right)\right)\right) \iff \operatorname {not}\left(( 0 \le h + x \land 0 \le h + y )\right) \land \operatorname {Unswappable}\left(h + x + y, w\right)$$

*Formalization.* `D5/S1/Words/Compositions/AlternatingResidualBridge.Unswappable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A complete pair is blocked when its two orders cannot both start legally at the current height. Continue after the pair; an empty list or a singleton has no complete pair and satisfies this condition.

**Definition 1.3 (Expanding pairs).**

$$\operatorname {alternating}\left(\operatorname {cons}\left(( a , b ), l\right)\right) = \operatorname {cons}\left(a, \operatorname {cons}\left(- b, \operatorname {alternating}\left(l\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Compositions/AlternatingResidualBridge.alternating` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entries of each pair are natural numbers. Expand a pair to its first entry and the negation of its second entry, both as integers. The empty list expands to the singleton zero.

**Definition 1.4 (Encoding two permutations).**

$$\operatorname {encode}\left(a, b\right) = ( a _ {1} , - b _ {1} , ... , a _ {m} , - b _ {m} , 0 )$$

*Formalization.* `D5/S1/Words/Compositions/AlternatingResidualBridge.encode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read the displayed a and b entries in one-based notation. This is the explicit alternating word ending in zero.

**Theorem 1.5 (The interval characterization).**

$$\operatorname {Good}\left(0, \operatorname {encode}\left(a, b\right)\right) \land \operatorname {Unswappable}\left(0, \operatorname {encode}\left(a, b\right)\right) \iff \operatorname {InResidual}\left(a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/AlternatingResidualBridge.encode_rule_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Before block i the height is A at i-1 minus B at i-1. The reversed order is illegal exactly when A at i-1 is less than B at i; the block endpoint is nonnegative exactly when B at i is at most A at i. Induction over the blocks proves both implications, including the initial and final heights.

**Theorem 1.6 (Recovering the two permutations).**

$$\operatorname {encode}\left(a, b\right) = \operatorname {encode}\left(c, d\right) \implies a = c \land b = d$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/AlternatingResidualBridge.encode_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality at alternating positions recovers the entries of a and b separately. Equality of the finite lists therefore gives equality of both permutations.

**Theorem 1.7 (Summing the product signs).**

$$\sum _ {a} \sum _ {b : \operatorname {Good}\left(0, \operatorname {encode}\left(a, b\right)\right) \land \operatorname {Unswappable}\left(0, \operatorname {encode}\left(a, b\right)\right)} \operatorname {sign}\left(a\right) \operatorname {sign}\left(b\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/AlternatingResidualBridge.encoded_product_sign_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sums range over permutations of Fin m. Apply the interval characterization, factor out sign(a), and use the residual identity. Only a equal to the identity contributes. This formula uses the product of the two signs; identifying it with the sign of an ambient contribution permutation is a separate remaining step.

## References

- Truth anchor: `D5/S1/Words/Compositions/AlternatingResidualBridge.Good`
- Truth anchor: `D5/S1/Words/Compositions/AlternatingResidualBridge.Unswappable`
- Truth anchor: `D5/S1/Words/Compositions/AlternatingResidualBridge.alternating`
- Truth anchor: `D5/S1/Words/Compositions/AlternatingResidualBridge.encode`
- Truth anchor: `D5/S1/Words/Compositions/AlternatingResidualBridge.encode_injective`
- Truth anchor: `D5/S1/Words/Compositions/AlternatingResidualBridge.encode_rule_iff`
- Truth anchor: `D5/S1/Words/Compositions/AlternatingResidualBridge.encoded_product_sign_sum`
- Dependency: [D5/S1/Words/Compositions/ResidualPermutationSign](ResidualPermutationSign.md)
