# Every canonical increasing digit pair has the endpoint complement property

## Abstract

Every canonical increasing digit pair has the endpoint complement property

**Definition 1.1 (initial).**

$$initial = tuple\left(badStart, endpointStart, 0, 0, false, true\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.initial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructor lists fields bad, endpoint, previousX, previousY, strict and valid in that order.

**Definition 1.2 (invalid).**

$$invalid = tuple\left(0, 0, 0, 0, false, false\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.invalid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The invalid signature is absorbing under the monitor update.

**Definition 1.3 (step).**

$$\forall s \in Signature,\; \forall symbol \in Fin\left(4\right),\; step\left(s, symbol\right) = if\left(boolOr\left(not\left(valid\left(s\right)\right), boolOr\left(boolAnd\left(eqBool\left(previousX\left(s\right), 1\right), eqBool\left(div\left(val\left(symbol\right), 2\right), 1\right)\right), boolOr\left(boolAnd\left(eqBool\left(previousY\left(s\right), 1\right), eqBool\left(mod\left(val\left(symbol\right), 2\right), 1\right)\right), boolAnd\left(not\left(strict\left(s\right)\right), decide\left(mod\left(val\left(symbol\right), 2\right) < div\left(val\left(symbol\right), 2\right)\right)\right)\right)\right)\right), invalid, tuple\left(maskStep\left(badRows, bad\left(s\right), val\left(symbol\right)\right), maskStep\left(endpointMasks, endpoint\left(s\right), val\left(symbol\right)\right), div\left(val\left(symbol\right), 2\right), mod\left(val\left(symbol\right), 2\right), boolOr\left(strict\left(s\right), decide\left(div\left(val\left(symbol\right), 2\right) < mod\left(val\left(symbol\right), 2\right)\right)\right), true\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The expression is this literal update. Let x=val(symbol) div 2 and y=val(symbol) mod 2, where div is truncated natural division. Return invalid if not valid, if previousX=x=1, if previousY=y=1, or if strict is false and y<x. Otherwise return (maskStep(badRows,bad,val(symbol)),maskStep(endpointMasks,endpoint,val(symbol)),x,y,strict OR decide(x<y),true).

**Definition 1.4 (hasAccept).**

$$\forall mask \in \mathbb{N},\; \forall accept \in \mathbb{N},\; hasAccept\left(mask, accept\right) = notEqualBool\left(bitAnd\left(mask, accept\right), 0\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.hasAccept` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

bitAnd is natural bitwise AND. notEqualBool returns true precisely when its arguments differ.

**Definition 1.5 (conclusion).**

$$\forall s \in Signature,\; conclusion\left(s\right) = \left(valid\left(s\right) = true \Rightarrow \left(strict\left(s\right) = true \Rightarrow hasAccept\left(bad\left(s\right), badAccept\right) = not\left(hasAccept\left(endpoint\left(s\right), endpointAccept\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.conclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A valid strictly increasing canonical pair is accepted by exactly one of the mismatch and endpoint languages.

**Theorem 1.6 (every_word).**

$$\forall w \in List\left(Fin\left(4\right)\right),\; conclusion\left(foldl\left(step, initial, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.every_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete monitor certificate is closed under all four digit-pair symbols and satisfies the terminal implication at every listed state. Induction transports those finite statements to every word; invalid or non-strict words retain the implication without a claim about complementarity.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.conclusion`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.every_word`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.hasAccept`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.initial`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.invalid`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.step`
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/LanguageData](LanguageData.md)
- Dependency: [D5/S1/Words/Palindromes/FridPrefix/MaskReachability](MaskReachability.md)
