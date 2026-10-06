# Signed Binary Weight

## Abstract

The literal minimum over signed-power representations satisfies exact scaling and recurrences.

**Definition 1.1 (Minimum signed-power weight).**

$$\forall x \in \mathbb{Z},\; \operatorname{signedWeight}\left(x\right) = \operatorname{sInf}\left(\{k:\mathbb{N} \mid \exists l \in \operatorname{List}\left(\operatorname{Bool} \times \mathbb{N}\right),\; \operatorname{length}\left(l\right) = k \land \operatorname{sum}\left(\operatorname{map}\left(t:\operatorname{Bool} \times \mathbb{N} \mapsto \operatorname{ite}\left(\operatorname{fst}\left(t\right), \operatorname{cast}\left(2, \mathbb{Z}\right)^{\operatorname{snd}\left(t\right)}, \operatorname{neg}\left(\operatorname{cast}\left(2, \mathbb{Z}\right)^{\operatorname{snd}\left(t\right)}\right)\right), l\right)\right) = x\}\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/SignedWeight.signedWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A representation is a finite list of pairs consisting of a Boolean sign and a natural exponent. A true sign contributes the positive power; a false sign contributes the negative power. Repetitions are permitted. The natural infimum is the minimum number of terms summing to the integer x.

**Theorem 1.2 (Exact arithmetic of the minimum).**

$$\left(\left(\left(\left(\operatorname{signedWeight}\left(0\right) = 0 \land \operatorname{signedWeight}\left(1\right) = 1\right) \land \left(\forall x \in \mathbb{Z},\; \operatorname{signedWeight}\left(\operatorname{neg}\left(x\right)\right) = \operatorname{signedWeight}\left(x\right)\right)\right) \land \left(\forall x \in \mathbb{Z},\; \forall y \in \mathbb{Z},\; \operatorname{signedWeight}\left(x + y\right) \le \operatorname{signedWeight}\left(x\right) + \operatorname{signedWeight}\left(y\right)\right)\right) \land \left(\forall x \in \mathbb{Z},\; \operatorname{signedWeight}\left(2 \cdot x\right) = \operatorname{signedWeight}\left(x\right)\right)\right) \land \left(\forall x \in \mathbb{Z},\; \operatorname{signedWeight}\left(2 \cdot x + 1\right) = 1 + \operatorname{min}\left(\operatorname{signedWeight}\left(x\right), \operatorname{signedWeight}\left(x + 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/SignedWeight.signed_weight_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Optimal signed representations exist for every integer. Scaling removes a zero low digit. An odd integer has a positive or negative unit term, giving the exact two-branch recurrence. The argument constructs optimal lists and bounds every signed representation, including repetitions.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/SignedWeight.signedWeight`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/SignedWeight.signed_weight_arithmetic`
