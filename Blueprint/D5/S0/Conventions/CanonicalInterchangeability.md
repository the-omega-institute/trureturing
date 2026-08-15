# Canonical Interchangeability

## Abstract

Faithful digit specifications are canonically interchangeable through decoding.

For any two faithful digit specifications whose word carriers decode equivalently to natural numbers, composing the decodings gives a bijection of digit words and a commuting decoding triangle.

**Theorem 1.1 (Faithful digit specifications are canonically interchangeable).**

$$(\forall W_{1}, W_{2}, d_{1}: W_{1}\equiv\mathbb{N}, d_{2}: W_{2}\equiv\mathbb{N}, \operatorname{Bijective}(w\mapsto d_{2}^{-1}(d_{1}(w))) \land (\forall w, d_{2}(d_{2}^{-1}(d_{1}(w)))=d_{1}(w)) \land (\forall \varphi, w, \varphi(d_{1}(w))\Leftrightarrow\varphi(d_{2}(d_{2}^{-1}(d_{1}(w)))))) \land \operatorname{Bijective}(\operatorname{wEncoding}^{-1})$$

*Proof.* Machine-checked in Lean as `D5/S0/Conventions/CanonicalInterchangeability.canonical_interchangeability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first conjunct quantifies over every pair of faithful digit specifications whose word carriers decode equivalently to the natural numbers: composing one decoding with the inverse of the other is a bijection of digit words, that composite commutes with decoding, and any property factoring only through the decoded natural number holds of a word exactly when it holds of its transported image. The second conjunct exhibits the W-digit specification as a concrete inhabitant of the quantified domain, so the statement is not vacuous.

## References

- Truth anchor: `D5/S0/Conventions/CanonicalInterchangeability.canonical_interchangeability`
