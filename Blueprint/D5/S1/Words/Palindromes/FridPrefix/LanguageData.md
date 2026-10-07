# Finite languages and the closed endpoint-complement monitor

## Abstract

Finite languages and the closed endpoint-complement monitor

**Definition 1.1 (badRows).**

$$badRows:List\left(List\left(\mathbb{N}\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageData.badRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal 138-row transition mask table tracks two canonical interior words, comparisons with the endpoints, and signed reflection carries. Each row has four paired-digit symbols.

**Definition 1.2 (endpointMasks).**

$$endpointMasks:List\left(List\left(\mathbb{N}\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageData.endpointMasks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal seventeen-row transition masks encode endpointRows on symbols 2x+y, with x and y binary.

**Definition 1.3 (Signature).**

$$Signature:Type$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageData.Signature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record fields are bad : Nat, endpoint : Nat, previousX : Nat, previousY : Nat, strict : Bool, and valid : Bool. It derives DecidableEq; no extra condition is imposed by the type.

**Definition 1.4 (instDecidableEqSignature).**

$$instDecidableEqSignature:DecidableEq\left(Signature\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageData.instDecidableEqSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The derived instance decides equality of signatures by comparing their four natural coordinates and two Boolean coordinates.

**Definition 1.5 (certificate).**

$$certificate:List\left(Signature\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageData.certificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal 105 monitor signatures include the invalid sink and all monitor states reachable from the initial signature. Closure and the endpoint-complement assertion are kernel checked for every listed state.

**Definition 1.6 (badStart).**

$$badStart = 1$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageData.badStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural numeral is a bit mask; bit q indicates membership of state q in this start or accept set.

**Definition 1.7 (endpointStart).**

$$endpointStart = 1$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageData.endpointStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural numeral is a bit mask; bit q indicates membership of state q in this start or accept set.

**Definition 1.8 (badAccept).**

$$badAccept = 255212434400583447092553078896731357568$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageData.badAccept` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural numeral is a bit mask; bit q indicates membership of state q in this start or accept set.

**Definition 1.9 (endpointAccept).**

$$endpointAccept = 2568$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/LanguageData.endpointAccept` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural numeral is a bit mask; bit q indicates membership of state q in this start or accept set.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageData.Signature`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageData.badAccept`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageData.badRows`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageData.badStart`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageData.certificate`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageData.endpointAccept`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageData.endpointMasks`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageData.endpointStart`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/LanguageData.instDecidableEqSignature`
