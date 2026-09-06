# Odd Reduced Abelian Complexity of the Thue-Morse Word

## Abstract

The all-start reduced abelian complexity of the Thue-Morse word obeys the odd-index recurrence and equals three at every power of two plus one.

The word is indexed from zero: thueMorse(s) is the parity of the number of one-bits of s, and therefore equals the paper's one-based letter t_(s+1). Campbell, Currie, and Rampersad stated the odd-index equality as an apparent pattern in arXiv:2509.16034v1, Section 3, without a proof. Every result below is derived in this repository; the paper is context, not a source of any assumed theorem.

**Definition 1.1 (The zero-indexed Thue-Morse word).**

$$thueMorse: \mathbb{N} \to \operatorname{Bool}, thueMorse = Nat.binaryRec(false, (bit, \mathord{\cdot}, parity) \mapsto bit \neq parity).$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nat.binaryRec starts at false and updates the accumulated parity by Boolean inequality with the next low binary digit. Thus this is exactly binary popcount parity, not a sampled finite prefix. The middle argument is ignored, as in Lean's anonymous binder.

**Definition 1.2 (The literal factor at a natural start).**

$$\forall length, start\in\mathbb{N}, \operatorname{factor}(length, start) = List.map(i \mapsto \operatorname{thueMorse}(start + i), List.range(length)).$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.factor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

List.range lists the indices from zero through length minus one in order. Mapping each index to thueMorse(start+i) gives the actual factor, including the empty list when length is zero.

**Definition 1.3 (Collapse every maximal constant run).**

$$\forall word\in List(\operatorname{Bool}), \operatorname{runCompress}(word) = List.destutter((a, b: \operatorname{Bool}) \mapsto a \neq b, word).$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.runCompress` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is Mathlib's List.destutter applied with the inequality relation on Boolean letters. It retains one letter from each maximal constant run and sends the empty list to the empty list.

**Definition 1.4 (Count false first and true second).**

$$\forall word\in List(\operatorname{Bool}), \operatorname{parikh}(word) = (List.count(false, word), List.count(true, word)).$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.parikh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both coordinates are natural numbers. List.count counts occurrences of the specified Boolean letter, with false in the first coordinate and true in the second.

**Definition 1.5 (The Parikh vector after run reduction).**

$$\forall length, start\in\mathbb{N}, \operatorname{reducedParikh}(length, start) = \operatorname{if}(\operatorname{thueMorse}(start), (\operatorname{natDiv}(\operatorname{if}(length = 0, 0, 1 + Finset.sum(Finset.range(length - 1), i \mapsto \operatorname{if}(\operatorname{thueMorse}(start + i) = \operatorname{thueMorse}(start + i + 1), 0, 1))), 2), \operatorname{if}(length = 0, 0, 1 + Finset.sum(Finset.range(length - 1), i \mapsto \operatorname{if}(\operatorname{thueMorse}(start + i) = \operatorname{thueMorse}(start + i + 1), 0, 1))) - \operatorname{natDiv}(\operatorname{if}(length = 0, 0, 1 + Finset.sum(Finset.range(length - 1), i \mapsto \operatorname{if}(\operatorname{thueMorse}(start + i) = \operatorname{thueMorse}(start + i + 1), 0, 1))), 2)), (\operatorname{if}(length = 0, 0, 1 + Finset.sum(Finset.range(length - 1), i \mapsto \operatorname{if}(\operatorname{thueMorse}(start + i) = \operatorname{thueMorse}(start + i + 1), 0, 1))) - \operatorname{natDiv}(\operatorname{if}(length = 0, 0, 1 + Finset.sum(Finset.range(length - 1), i \mapsto \operatorname{if}(\operatorname{thueMorse}(start + i) = \operatorname{thueMorse}(start + i + 1), 0, 1))), 2), \operatorname{natDiv}(\operatorname{if}(length = 0, 0, 1 + Finset.sum(Finset.range(length - 1), i \mapsto \operatorname{if}(\operatorname{thueMorse}(start + i) = \operatorname{thueMorse}(start + i + 1), 0, 1))), 2))).$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedParikh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here runs(length,start) counts maximal constant runs in the indicated factor. Run reduction is alternating, so a false initial letter gives r-floor(r/2) false letters and floor(r/2) true letters; a true initial letter reverses those coordinates. The displayed natDiv operation is natural-number floor division, exactly Lean's Nat.div.

**Theorem 1.6 (The arithmetic and literal reduced Parikh vectors agree).**

$$\forall length, start\in\mathbb{N}, \operatorname{reducedParikh}(length, start) = \operatorname{parikh}(\operatorname{runCompress}(\operatorname{factor}(length, start))).$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedParikh_eq_parikh_runCompress` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

List induction proves the alternating counts after literal run compression. A second induction identifies the list run count with the transition sum used by the arithmetic definition. The identity holds at every natural length and start, including length zero.

**Definition 1.7 (Reduced abelian equivalence at a common length).**

$$\forall length, start1, start2\in\mathbb{N}, \operatorname{ReducedAbelianEquivalent}(length, start1, start2) \iff \operatorname{reducedParikh}(length, start1) = \operatorname{reducedParikh}(length, start2).$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.ReducedAbelianEquivalent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two factors of the same supplied length are equivalent precisely when the Parikh vectors of their run reductions are equal.

**Definition 1.8 (The canonical code for a reduced abelian class).**

$$\forall length, start\in\mathbb{N}, \operatorname{reducedAbelianCode}(length, start) = (\operatorname{if}(length = 0, 0, 1 + Finset.sum(Finset.range(length - 1), i \mapsto \operatorname{if}(\operatorname{thueMorse}(start + i) = \operatorname{thueMorse}(start + i + 1), 0, 1))), \operatorname{if}(\operatorname{Odd}(\operatorname{if}(length = 0, 0, 1 + Finset.sum(Finset.range(length - 1), i \mapsto \operatorname{if}(\operatorname{thueMorse}(start + i) = \operatorname{thueMorse}(start + i + 1), 0, 1)))), \operatorname{thueMorse}(start), false)).$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The run count is always retained. For even run count the two initial letters have the same reduced Parikh vector, so the Boolean coordinate is canonically false; for odd run count it records the actual first letter.

**Theorem 1.9 (Reduced Parikh equality is exactly code equality).**

$$\forall length, start1, start2\in\mathbb{N}, \operatorname{ReducedAbelianEquivalent}(length, start1, start2) \iff \operatorname{reducedAbelianCode}(length, start1) = \operatorname{reducedAbelianCode}(length, start2).$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianEquivalent_iff_code_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate sum recovers the run count. With equal run counts, the two alternating Parikh vectors agree automatically in the even case and agree exactly when their initial letters agree in the odd case. This is the preregistered class-code equivalence.

**Definition 1.10 (Reduced abelian classes over all natural starts).**

$$\forall length\in\mathbb{N}, \operatorname{reducedAbelianClasses}(length) = \{(a, b) \mid (a \leq length \land b \leq length) \land (\exists start\in\mathbb{N}, \operatorname{reducedParikh}(length, start) = (a, b))\}.$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianClasses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite ambient square contains coordinate pairs from zero through length. Filtering it by existence of an arbitrary natural start retains exactly every reduced Parikh vector that occurs anywhere in the infinite word. No prefix bound or sampling hypothesis appears.

**Definition 1.11 (Reduced abelian complexity).**

$$\forall length\in\mathbb{N}, \operatorname{R}(length) = \operatorname{card}(\operatorname{reducedAbelianClasses}(length)).$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R(length) is the cardinality of the all-start finite class set, matching the source definition rather than the number seen in a chosen prefix.

**Theorem 1.12 (Odd indices reflect to half length).**

$$\forall n\in\mathbb{N}, \operatorname{R}(2 \times n + 1) = \operatorname{R}(n + 1).$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianComplexity_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transition identities transition(2q)=1 and transition(2q+1)=1-transition(q) prove, for starts of either parity, runs(2n+1,p)=2n+2-runs(n+1,floor(p/2)). The reflection preserves run-count parity.

For every factor, the explicit start 2^(start+length+1)+start gives a factor with the same run count and complementary initial letter, by the high-power shift identity thueMorse(2^k+x)=not thueMorse(x), for x<2^k. The constructed shift satisfies this bound. This supplies the odd-start surjectivity case.

Reflection is therefore a bijection on the canonical codes. The code equivalence transfers that bijection to reduced Parikh classes, and taking finite cardinalities proves the equality for every n.

**Theorem 1.13 (Length two has three reduced abelian classes).**

$$\operatorname{R}(2) = 3.$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianComplexity_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three reduced Parikh classes are (1,0), (0,1), and (1,1), witnessed at starts 5, 1, and 0.

**Theorem 1.14 (Power of two plus one has complexity three).**

$$\forall k\in\mathbb{N}, \operatorname{R}(2^{k} + 1) = 3.$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianComplexity_two_pow_add_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A kernel-decided certificate constructs and exhausts the three length-two classes (1,0), (0,1), and (1,1). Induction then rewrites each successor power through the odd recurrence. No native_decide step is used.

## References

- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.R`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.ReducedAbelianEquivalent`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.factor`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.parikh`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianClasses`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianCode`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianComplexity_odd`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianComplexity_two`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianComplexity_two_pow_add_one`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedAbelianEquivalent_iff_code_eq`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedParikh`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.reducedParikh_eq_parikh_runCompress`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.runCompress`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd.thueMorse`
