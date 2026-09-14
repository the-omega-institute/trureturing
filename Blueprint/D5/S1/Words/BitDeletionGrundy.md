# The Bit-Deletion Grundy Function

## Abstract

Define the OEIS A398916 bit-deletion game and prove both registered conjectures.

OEIS A398916 was contributed by Do Thanh Nhan on August 14, 2026, with the conjecture comments updated on August 20, 2026. The entry states both universal claims here only as conjectures. The entry proves the contextual formula a(2^n) = (n mod 2) + 1 and lists initial values, including a(37)=0; those facts are source context and are not restated here. The negative literature search is ASSUMED-UNVERIFIED for unindexed results.

**Definition 1.1 (Minimum excluded value).**

$$\forall S: \operatorname{Finset}(\mathbb{N}), \operatorname{mex}(S) = \operatorname{mexScan}(S, \operatorname{card}(S) + 1, 0)$$

*Formalization.* `D5/S1/Words/BitDeletionGrundy.mex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite set S of natural numbers, mex uses a bounded scan from zero with card(S)+1 units of fuel. The pigeonhole bound guarantees that this executable scan reaches the mathematical minimum excluded value.

**Theorem 1.2 (The bounded scan is mex).**

$$\forall S: \operatorname{Finset}(\mathbb{N}), (\operatorname{mex}(S) \neg\in S) \land (\forall k: \mathbb{N}, k < \operatorname{mex}(S) \Rightarrow k \in S)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BitDeletionGrundy.mex_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The returned value is absent from S and every smaller natural belongs to S.

**Definition 1.3 (Leading-zero normalization).**

$$(\operatorname{normalize}([]) = []) \land (\forall w: List Bool, \operatorname{normalize}(\operatorname{cons}(0, w)) = \operatorname{normalize}(w)) \land (\forall w: List Bool, \operatorname{normalize}(\operatorname{cons}(1, w)) = \operatorname{cons}(1, w))$$

*Formalization.* `D5/S1/Words/BitDeletionGrundy.normalize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Normalization recursively removes leading zero bits, preserving an empty word and stopping at the first leading one.

**Definition 1.4 (Positional one-bit erasures).**

$$\forall \alpha: Type, (\operatorname{erasures}([]) = []) \land (\forall b: \alpha, \forall w: \operatorname{List}(\alpha), \operatorname{erasures}(\operatorname{cons}(b, w)) = \operatorname{cons}(w, \operatorname{map}((v \mapsto \operatorname{cons}(b, v)), \operatorname{erasures}(w))))$$

*Formalization.* `D5/S1/Words/BitDeletionGrundy.erasures` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The erasure list contains the tail deletion first, followed by every recursive suffix deletion with the original head restored.

**Definition 1.5 (Bit deletion on binary words).**

$$(\operatorname{wordGrundy}([]) = 0) \land (\forall w: List Bool, \operatorname{wordGrundy}(\operatorname{cons}(0, w)) = \operatorname{wordGrundy}(w)) \land (\forall w: List Bool, \operatorname{wordGrundy}(\operatorname{cons}(1, w)) = \operatorname{mex}(\{\operatorname{wordGrundy}(\operatorname{normalize}(v)) \mid v \in \operatorname{erasures}(\operatorname{cons}(1, w))\}))$$

*Formalization.* `D5/S1/Words/BitDeletionGrundy.wordGrundy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Words are MSB-first lists of bits. A leading zero is stripped. At a leading one, every positional one-bit deletion is normalized by stripping new leading zeros, duplicate results are identified as a finite set, and mex is applied. The empty word has value zero.

**Definition 1.6 (The even-suffix transition).**

$$\forall h: Fin 4, \operatorname{transition0}(h) = \operatorname{ite}((h = 1), 3, 1)$$

*Formalization.* `D5/S1/Words/BitDeletionGrundy.transition0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T_0 sends state value 1 to 3 and every other value in Fin 4 to 1.

**Definition 1.7 (The odd-suffix transition).**

$$\forall h: Fin 4, \operatorname{transition1}(h) = \operatorname{ite}((h = 0), 2, 0)$$

*Formalization.* `D5/S1/Words/BitDeletionGrundy.transition1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T_1 sends state value 0 to 2 and every other value in Fin 4 to 0.

**Definition 1.8 (Word-length parity).**

$$(\operatorname{parity}([]) = 0) \land (\forall b: Bool, \forall w: List Bool, \operatorname{parity}(\operatorname{cons}(b, w)) = \operatorname{not}(\operatorname{parity}(w)))$$

*Formalization.* `D5/S1/Words/BitDeletionGrundy.parity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty word has even parity, and every cons toggles the suffix parity.

**Definition 1.9 (The parity-indexed transition).**

$$(\forall h: Fin 4, \operatorname{transition}(0, h) = \operatorname{transition0}(h)) \land (\forall h: Fin 4, \operatorname{transition}(1, h) = \operatorname{transition1}(h))$$

*Formalization.* `D5/S1/Words/BitDeletionGrundy.transition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

False parity selects transition0 and true parity selects transition1.

**Definition 1.10 (The closed-form automaton).**

$$(\operatorname{formula}([]) = 0) \land (\forall w: List Bool, \operatorname{formula}(\operatorname{cons}(0, w)) = \operatorname{formula}(w)) \land (\forall w: List Bool, \operatorname{formula}(\operatorname{cons}(1, w)) = \operatorname{transition}(\operatorname{parity}(w), \operatorname{formula}(w)))$$

*Formalization.* `D5/S1/Words/BitDeletionGrundy.formula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula reads an MSB-first word recursively from the right. A zero is ignored; a one applies T_0 when the remaining suffix has even length and T_1 when it has odd length. Here parity(w) is false for even length and true for odd length.

**Theorem 1.11 (Appending two zeros preserves the formula).**

$$\forall w: List Bool, \operatorname{formula}(\operatorname{append}(w, [0, 0])) = \operatorname{formula}(w)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BitDeletionGrundy.formula_append_zero_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two appended zero bits leave both the parity phase and the formula value unchanged.

**Theorem 1.12 (The automaton computes the word game).**

$$\forall w: List Bool, \operatorname{wordGrundy}(w) = \operatorname{val}(\operatorname{formula}(w))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BitDeletionGrundy.wordGrundy_eq_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The (p,h,M) automaton records suffix parity p, candidate value h, and the finite set M of deletion values. A table of 30 reachable states is closed under cons-0 and cons-1; kernel decide proves closure, state realization, and the cons-1 mex certificate. Strong induction on word length then identifies wordGrundy with val(formula). The injective four-bit code for M is only an implementation device for kernel reduction, not a change to the function computed by the automaton.

**Definition 1.13 (Natural successors by one binary-digit deletion).**

$$\forall n: \mathbb{N}, \operatorname{bitDeletionSuccessors}(n) = \operatorname{image}(\operatorname{ofDigits}(2), \operatorname{toFinset}(\operatorname{erasures}(\operatorname{digits}(2, n))))$$

*Formalization.* `D5/S1/Words/BitDeletionGrundy.bitDeletionSuccessors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n in N, remove each positional digit from Mathlib's little-endian Nat.digits 2 n and re-encode the remaining list with Nat.ofDigits 2. The result is a Finset, so duplicate numerical outcomes are identified. Nat.ofDigits drops any high zero digits automatically, which agrees with leading-zero normalization. The word model corresponds to the natural-number recurrence under binary decoding.

**Theorem 1.14 (Every natural successor is smaller).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, (m \in \operatorname{bitDeletionSuccessors}(n)) \Rightarrow m < n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BitDeletionGrundy.bitDeletionSuccessors_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deleting one digit shortens the canonical digit list by one. The ofDigits bound below two to the shortened binary length, together with the lower bound for the original canonical length, proves m<n. This is the well-foundedness side of that natural-number recurrence, to which this module's word model corresponds under binary decoding.

**Definition 1.15 (The OEIS sequence function).**

$$\forall n: \mathbb{N}, \operatorname{g}(n) = \operatorname{wordGrundy}(\operatorname{map}((d \mapsto (d = 1)), \operatorname{reverse}(\operatorname{digits}(2, n))))$$

*Formalization.* `D5/S1/Words/BitDeletionGrundy.g` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib Nat.digits is little-endian. Reversal gives the canonical MSB-first binary expansion, and mapping a digit to the proposition d=1 gives its Boolean word. At n=0 this word is empty, hence g(0)=0.

**Theorem 1.16 (The natural-number mex recurrence).**

$$\forall n: \mathbb{N}, \operatorname{g}(n) = \operatorname{mex}(\operatorname{image}(g, \operatorname{bitDeletionSuccessors}(n)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BitDeletionGrundy.g_mex_bitDeletionSuccessors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The digit-decoding correspondence identifies every normalized word deletion with exactly one Nat.ofDigits successor, and identifies its wordGrundy value with g. Rewriting the word mex equation therefore gives the natural-number recurrence under binary decoding.

**Theorem 1.17 (No Grundy value exceeds three).**

$$\forall n: \mathbb{N}, \operatorname{g}(n) \leq 3$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BitDeletionGrundy.g_le_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The automaton formula lies in Fin 4, so the word-game identification bounds every natural-number Grundy value by three.

**Theorem 1.18 (Multiplication by four preserves the value).**

$$\forall n: \mathbb{N}, \operatorname{g}(4 \cdot n) = \operatorname{g}(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BitDeletionGrundy.g_four_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero n, Nat.digits_base_pow_mul identifies multiplication by four with appending the two bits 00 to the MSB-first word. The formula's two-zero invariance proves the claim; n=0 is immediate.

**Theorem 1.19 (Both OEIS A398916 conjectures).**

$$(\forall n: \mathbb{N}, \operatorname{g}(n) \leq 3) \land (\forall n: \mathbb{N}, \operatorname{g}(4 \cdot n) = \operatorname{g}(n))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/BitDeletionGrundy.conjectures` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Together these conclusions state that all values are at most three and g(4n)=g(n) for every natural n.

## References

- Truth anchor: `D5/S1/Words/BitDeletionGrundy.bitDeletionSuccessors`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.bitDeletionSuccessors_lt`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.conjectures`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.erasures`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.formula`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.formula_append_zero_zero`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.g`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.g_four_mul`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.g_le_three`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.g_mex_bitDeletionSuccessors`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.mex`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.mex_spec`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.normalize`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.parity`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.transition`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.transition0`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.transition1`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.wordGrundy`
- Truth anchor: `D5/S1/Words/BitDeletionGrundy.wordGrundy_eq_formula`
- Dependency: [D5/S1/Recurrence/ComplementaryGoldenRatioLimit](../Recurrence/ComplementaryGoldenRatioLimit.md)
