# Yanev's Binary Run Compression Formula

## Abstract

Binary run compression satisfies Yanev's formula at every natural index, including zero.

The variable n ranges over the natural numbers N, including zero. The operator digits_2(n) is Nat.digits 2 n, the little-endian binary digit list, with the empty list at zero. The operator ofDigits_2 decodes a little-endian list using Nat.ofDigits 2. Boolean equality on naturals is denoted by beq; splitBy(beq,l) partitions a list l into maximal contiguous equal-digit blocks, in their original order. The operator head! denotes List.head!, returning the first entry of a nonempty list and zero on the empty list. The operator map applies a function to every list entry, and length denotes List.length. Thus runs(n) counts blocks and a(n) decodes their heads. The operator mod is natural-number remainder. Addition, multiplication, and powers are on naturals, and subtraction is truncated natural subtraction.

**Definition 1.1 (The number of binary runs).**

$$\forall n: \mathbb{N}, \operatorname{runs}\left(n\right) = \operatorname{length}\left(\operatorname{splitBy}\left(\operatorname{beq}, \left(\operatorname{digits}_{2}\right)\left(n\right)\right)\right)$$

*Formalization.* `D5/S1/Digit/YanevRunCompressionClosedForm.runs` (`✓ std3`).

*Citation.* Reinhard Zumkeller; Velin Yanev (2016). *OEIS A090079, binary run compression*. URL: <https://oeis.org/A090079>.

*Commentary.*

Every block is nonempty. The block count is the number of maximal constant runs, unchanged by reversing the digit order. At zero it is zero.

**Definition 1.2 (Literal run compression).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \left(\operatorname{ofDigits}_{2}\right)\left(\operatorname{map}\left(\operatorname{head!}, \operatorname{splitBy}\left(\operatorname{beq}, \left(\operatorname{digits}_{2}\right)\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Digit/YanevRunCompressionClosedForm.a` (`✓ std3`).

*Citation.* Reinhard Zumkeller; Velin Yanev (2016). *OEIS A090079, binary run compression*. URL: <https://oeis.org/A090079>.

*Commentary.*

Keeping one head per block replaces each nonempty run of zeros or ones by one copy of that digit. Little-endian decoding implements the operation in the OEIS NAME. The empty digit list gives a(0)=0.

**Theorem 1.3 (Yanev's closed form).**

$$\forall n: \mathbb{N}, 3 \cdot \operatorname{a}\left(n\right) = (2^{(\operatorname{runs}\left(n\right) + 1)} + \operatorname{mod}\left(n, 2\right)) - 2$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/YanevRunCompressionClosedForm.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a090079-yanev-run-compression-closed-form` (proved) by `D5/S1/Digit/YanevRunCompressionClosedForm.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a090079-yanev-run-compression-closed-form","declaration_gid":"D5/S1/Digit/YanevRunCompressionClosedForm.result","resolution_kind":"proved"} -->

*Citation.* Reinhard Zumkeller; Velin Yanev (2016). *OEIS A090079, binary run compression*. URL: <https://oeis.org/A090079>.

*Commentary.*

The cited formula uses A005811(n) for the number of binary runs. Its integer parity term (1-(-1)^n)/2 = n mod 2. The statement is multiplied by 3 to stay in N. For nonzero n the compressed word alternates, has binary entries, and ends in one. The proof instantiates the digit and splitBy APIs and normalizes using the inlined alternating-list evaluation identity; its head is n mod 2. The zero case follows from the definitions.

## References

- Truth anchor: `D5/S1/Digit/YanevRunCompressionClosedForm.a`
- Truth anchor: `D5/S1/Digit/YanevRunCompressionClosedForm.result`
- Truth anchor: `D5/S1/Digit/YanevRunCompressionClosedForm.runs`
