# Finite Record Extension Count

## Abstract

A finite candidate class restricted by fixed record values is bounded by its free choices.

**Theorem 1.1 (Restricted record classes have at most the free-choice count).**

$$\operatorname{card}(RestrictedExtensions(candidate, record, prescribed)) \le \operatorname{card}(Y)^{\operatorname{card}(D) - \operatorname{card}(record)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/RecordExtensionCount.restricted_extension_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D and Y be finite types. A record is a finite set of positions in D, and prescribed supplies the fixed Y-value at each recorded position. RestrictedExtensions contains exactly the functions in an arbitrary candidate class that agree with those fixed values.

All functions extending the record are equivalent to functions from the complement of the recorded positions into Y. Their exact cardinality is therefore card(Y) raised to card(D) minus card(record). Forgetting candidate membership embeds the restricted class into this full extension space and gives the displayed upper bound.

This is an honest partial closure of the finite upper-bound clause. It does not assert that a complexity-filtered candidate class eventually contains every extension, so the separate threshold and eventual-equality clause remains unresolved.

Pinned Mathlib was searched before proving. No direct theorem for functions agreeing with a fixed record was found. The proof wraps Fintype.card_fun, Fintype.card_subtype_compl, and Nat.card_le_card_of_injective after supplying the explicit record-extension equivalence.

## References

- Truth anchor: `D5/S0/Diagonal/RecordExtensionCount.restricted_extension_card_le`
