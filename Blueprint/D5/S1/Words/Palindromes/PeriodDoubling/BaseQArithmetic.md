# Literal Endpoint Charge

## Abstract

Accepted q paths have the literal arithmetic charge Q(j) - Q(n).

**Definition 1.1 (The nonadjacent digit formula).**

$$\forall X \in \mathbb{N},\; \forall h \in \mathbb{N},\; \operatorname{tripleSignedDigits}\left(X, h\right) = \operatorname{ofFn}\left(i:\operatorname{Fin}\left(h\right) \mapsto \operatorname{cast}\left(\operatorname{mod}\left(\operatorname{div}\left(3 \cdot X, 2^{\operatorname{val}\left(i\right) + 1}\right), 2\right), \mathbb{Z}\right) - \operatorname{cast}\left(\operatorname{mod}\left(\operatorname{div}\left(X, 2^{\operatorname{val}\left(i\right) + 1}\right), 2\right), \mathbb{Z}\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/BaseQArithmetic.tripleSignedDigits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Digits are in increasing order of position: digit i is bit i+1 of 3X minus bit i+1 of X. div and mod are natural integer quotient and remainder. The chosen length is a separate parameter.

**Definition 1.2 (Q from positions, sign changes and endpoint parity).**

$$\forall n \in \mathbb{N},\; \operatorname{signedDigitCharge}\left(n\right) = \operatorname{sum}\left(\operatorname{map}\left(z:\mathbb{Z} \times \mathbb{N} \mapsto 1 + 2 \cdot \operatorname{mod}\left(\operatorname{snd}\left(z\right), 2\right), \operatorname{filter}\left(z:\mathbb{Z} \times \mathbb{N} \mapsto \operatorname{neqBool}\left(\operatorname{fst}\left(z\right), 0\right), \operatorname{zipIdx}\left(\operatorname{tripleSignedDigits}\left(\operatorname{div}\left(n + 1, 2\right), \operatorname{log}\left(2, 3 \cdot \operatorname{div}\left(n + 1, 2\right)\right) + 1\right), 0\right)\right)\right)\right) + \operatorname{length}\left(\operatorname{filter}\left(z:(\mathbb{Z} \times \mathbb{N}) \times (\mathbb{Z} \times \mathbb{N}) \mapsto \operatorname{neqBool}\left(\operatorname{fst}\left(\operatorname{fst}\left(z\right)\right), \operatorname{fst}\left(\operatorname{snd}\left(z\right)\right)\right), \operatorname{zip}\left(\operatorname{filter}\left(z:\mathbb{Z} \times \mathbb{N} \mapsto \operatorname{neqBool}\left(\operatorname{fst}\left(z\right), 0\right), \operatorname{zipIdx}\left(\operatorname{tripleSignedDigits}\left(\operatorname{div}\left(n + 1, 2\right), \operatorname{log}\left(2, 3 \cdot \operatorname{div}\left(n + 1, 2\right)\right) + 1\right), 0\right)\right), \operatorname{tail}\left(\operatorname{filter}\left(z:\mathbb{Z} \times \mathbb{N} \mapsto \operatorname{neqBool}\left(\operatorname{fst}\left(z\right), 0\right), \operatorname{zipIdx}\left(\operatorname{tripleSignedDigits}\left(\operatorname{div}\left(n + 1, 2\right), \operatorname{log}\left(2, 3 \cdot \operatorname{div}\left(n + 1, 2\right)\right) + 1\right), 0\right)\right)\right)\right)\right)\right) + \operatorname{OptionElim}\left(0, z:\mathbb{Z} \times \mathbb{N} \mapsto \operatorname{toNat}\left(\operatorname{neqBool}\left(\operatorname{eqBool}\left(\operatorname{mod}\left(n, 2\right), 1\right), \operatorname{decide}\left(\operatorname{fst}\left(z\right) < 0\right)\right)\right), \operatorname{headOption}\left(\operatorname{filter}\left(z:\mathbb{Z} \times \mathbb{N} \mapsto \operatorname{neqBool}\left(\operatorname{fst}\left(z\right), 0\right), \operatorname{zipIdx}\left(\operatorname{tripleSignedDigits}\left(\operatorname{div}\left(n + 1, 2\right), \operatorname{log}\left(2, 3 \cdot \operatorname{div}\left(n + 1, 2\right)\right) + 1\right), 0\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/BaseQArithmetic.signedDigitCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take X = div(n+1,2) and h = log(2,3X)+1. Enumerate its nonadjacent digits, discard zeros, and sum the weights 1+2(i mod 2), consecutive sign changes, and endpoint parity XOR the negativity of the first surviving sign. The last indicator is zero when no digit survives. OptionElim returns its first argument for none and applies its displayed function for some; neqBool, eqBool and decide denote Boolean tests.

**Definition 1.3 (Endpoint and first-sign memory checker).**

$$\forall i \in \mathbb{N},\; \operatorname{memoryRowCheck}\left(i\right) = \operatorname{all}\left(\lambda e:\mathbb{N} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \mapsto \operatorname{decide}\left(\left(\left(\operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right), 2\right), 0\right) = \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(i\right)\right), 2\right), 0\right) \land \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right), 3\right), 0\right) = \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(i\right)\right), 3\right), 0\right)\right) \land \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right), 14\right), 0\right) = \operatorname{ite}\left(\operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(i\right)\right), 14\right), 0\right) = 0, \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right), 10\right), 0\right), \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(i\right)\right), 14\right), 0\right)\right)\right) \land \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right), 15\right), 0\right) = \operatorname{ite}\left(\operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(i\right)\right), 15\right), 0\right) = 0, \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{fst}\left(e\right)\right)\right), 12\right), 0\right), \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(i\right)\right), 15\right), 0\right)\right)\right), \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{baseTable}\left(i\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/BaseQArithmetic.memoryRowCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every outgoing edge must preserve the two endpoint parities and update both first-nonzero-sign memories only while their incoming memory is zero. This Boolean checker is reused by the charge identification and by the lowest-position arithmetic interpretation.

**Theorem 1.4 (Exact charge of every accepting path).**

$$\forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall s \in \operatorname{Fin}\left(1492\right),\; \forall t \in \operatorname{Fin}\left(1492\right),\; \forall xs \in \operatorname{List}\left(\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}\right),\; \forall p \in \operatorname{Path}\left(\operatorname{baseAutomaton}\left(\operatorname{true}\right), s, t, xs\right),\; \left(\left(\left(\left(\left(s \in \operatorname{start}\left(\operatorname{baseAutomaton}\left(\operatorname{true}\right)\right) \land t \in \operatorname{accept}\left(\operatorname{baseAutomaton}\left(\operatorname{true}\right)\right)\right) \land \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(s\right)\right)\right), 2\right), 0\right) = \operatorname{cast}\left(\operatorname{mod}\left(n, 2\right), \mathbb{Z}\right)\right) \land \operatorname{getD}\left(\operatorname{getElemOption}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(s\right)\right)\right), 3\right), 0\right) = \operatorname{cast}\left(\operatorname{mod}\left(j, 2\right), \mathbb{Z}\right)\right) \land \operatorname{foldr}\left(\lambda a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} x:\mathbb{Z} \mapsto \operatorname{fst}\left(\operatorname{snd}\left(\operatorname{snd}\left(a\right)\right)\right) + 2 \cdot x, 0, xs\right) = \operatorname{cast}\left(\operatorname{div}\left(n, 2\right), \mathbb{Z}\right)\right) \land \operatorname{foldr}\left(\lambda a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} x:\mathbb{Z} \mapsto \operatorname{snd}\left(\operatorname{snd}\left(\operatorname{snd}\left(a\right)\right)\right) + 2 \cdot x, 0, xs\right) = \operatorname{cast}\left(\operatorname{div}\left(j, 2\right), \mathbb{Z}\right)\right) \Rightarrow \operatorname{pathCharge}\left(\lambda [\operatorname{Fin}\left(1492\right)] a:\mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} [\operatorname{Fin}\left(1492\right)] \mapsto \operatorname{fst}\left(\operatorname{snd}\left(a\right)\right), p\right) + \operatorname{baseOffset}\left(\operatorname{fst}\left(\operatorname{baseTable}\left(\operatorname{val}\left(t\right)\right)\right)\right) = \operatorname{cast}\left(\operatorname{signedDigitCharge}\left(j\right), \mathbb{Z}\right) - \operatorname{cast}\left(\operatorname{signedDigitCharge}\left(n\right), \mathbb{Z}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/BaseQArithmetic.base_path_Q_semantics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an accepting charge-mode path whose source parities and binary folds encode n and j, the sum of q edge charges plus the terminal phase correction is Q(j)-Q(n). Component 2 or 3 of the source is the endpoint parity; the last two components of an edge label are bits of the integer quotients div(n,2) and div(j,2). The proof checks all sign-memory transitions and identifies the padded output streams with the unique nonadjacent expansions of the rounded halves. The dummy initial zero contributes no weight.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseQArithmetic.base_path_Q_semantics`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseQArithmetic.memoryRowCheck`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseQArithmetic.signedDigitCharge`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/BaseQArithmetic.tripleSignedDigits`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseChargeArithmetic](BaseChargeArithmetic.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/CanonicalSignedDigits](CanonicalSignedDigits.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/TripleBinaryDigits](TripleBinaryDigits.md)
