# Literal inverses and safe shared charge suffixes

## Abstract

Prefix-parity inverses realize short-window charges by actual shared endpoint words.

**Theorem 1.1 (Short words are legal in either alphabet).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.short_legal`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.short_legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least two and m less than k, every complete m-bit word is DBonacciAdmissible. Both the exceptional first-zero execution and the fixed suffix use this internal admissibility.

**Theorem 1.2 (A cleared incoming seam succeeds).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.short_safe_execution`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.short_safe_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a valid incoming tail and a short nonempty word, either incoming tail zero or literal first bit zero gives the exact successful native scalar, phase and tail updates. The terminal tail equals its zero-tail evaluation and remains below k. For the exceptional first word, its actual first bit is zero.

**Definition 1.3 (Literal bit scalars).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.bitScalar`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.bitScalar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A true literal bit contributes one in ZMod 2; a false bit contributes zero.

**Definition 1.4 (The zero extension of one word).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.extendedBit`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.extendedBit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Offsets inside the word carry that literal bit scalar; all offsets beyond the word carry zero.

**Theorem 1.5 (The native ordered adjacent-bit charge).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.increment_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.increment_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least three and a word shorter than k, its original matched scalar increment at negative phase j is the sum of the bit scalar at offset j and its predecessor, with zero extension at both ends. The formula applies to every modular phase.

The reader uses the original integer KBonacci weights and the matched scalar in ZMod(2). The period is k+1. A row q is a function from natural offsets to ZMod(2); only offsets zero through m are used. The literal word prefixWord(m,q) has bit i equal to the decision that the sum of q(h) over h<i+1 is nonzero. windowCharge(k,m,q,j) is q(val(j)) when val(j)<=m and zero otherwise. All row sums and scalar differences are in ZMod(2).

**Theorem 1.6 (An even ordered window has a physical prefix-parity inverse).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall q \in \mathbb{N} \to \operatorname{ZMod}\left(2\right),\; \left(\left(\left(3 \le k \land 1 \le m\right) \land m < k\right) \land \sum_{h\in \operatorname{range}\left(m + 1\right)} q\left(h\right) = 0\right) \Rightarrow \left(\left(\left(\left(\forall j \in \operatorname{ZMod}\left(k + 1\right),\; \operatorname{wordIncrement}\left(k, -j, \operatorname{prefixWord}\left(m, q\right)\right) = \operatorname{windowCharge}\left(k, m, q, j\right)\right) \land \left(\operatorname{prefixWord}\left(m, q\right)\left(\langle 0\rangle_{m}\right) = false \Leftrightarrow q\left(0\right) = 0\right)\right) \land \left(\operatorname{prefixWord}\left(m, q\right)\left(\langle m - 1\rangle_{m}\right) = false \Leftrightarrow q\left(m\right) = 0\right)\right) \land \left(\forall w \in \operatorname{Fin}\left(m\right) \to Bool,\; \left(\forall j \in \operatorname{ZMod}\left(k + 1\right),\; \operatorname{wordIncrement}\left(k, -j, w\right) = \operatorname{windowCharge}\left(k, m, q, j\right)\right) \Rightarrow w = \operatorname{prefixWord}\left(m, q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.short_window_charge_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k>=3 and 1<=m<k, the prescribed even row is exactly the native increment of this m-bit word at every ambient phase -j, including zero increment outside the ordered window. Its first bit is zero exactly when q(0)=0, and its last bit is zero exactly when q(m)=0. Every m-bit word with these same increments at all phases equals prefixWord(m,q). A displayed angle index with value r and subscript n denotes the Fin(n) element of value r, with its proof r<n supplied by the hypotheses. No phase reading is used to choose the word.

The adjacent coefficient and marker identities of `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CoprimeSingletonLower` evaluate the literal increment. Prefix cancellation then recovers every row entry, with the final entry supplied by the even total charge.

**Theorem 1.7 (The predicted archive has one available scalar per row).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall rows \in \operatorname{List}\left(\mathbb{N} \to \operatorname{ZMod}\left(2\right)\right),\; \forall v \in \operatorname{ZMod}\left(2\right),\; \forall j \in \operatorname{ZMod}\left(k + 1\right),\; \operatorname{length}\left(\operatorname{chargeArchive}\left(k, m, rows, v, j\right)\right) = \operatorname{length}\left(rows\right) \land \left(\neg none \in \operatorname{chargeArchive}\left(k, m, rows, v, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.charge_archive_live` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary widths, rows, starting scalar and modular phase, chargeArchive has exactly as many entries as rows and contains no none entry. Each recursion step records some of the next scalar. No evenness or seam condition is needed for this predicted archive property. Physical endpoint success follows when native execution equals this archive, as in `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder`.

**Theorem 1.8 (One literal suffix realizes every row on each joint actual source).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall alphabet \in Bool,\; \forall rows \in \operatorname{List}\left(\mathbb{N} \to \operatorname{ZMod}\left(2\right)\right),\; \forall v \in \operatorname{ZMod}\left(2\right),\; \forall j \in \operatorname{ZMod}\left(k + 1\right),\; \forall s \in \mathbb{N},\; \left(\left(\left(\left(\left(\left(3 \le k \land 1 \le m\right) \land m < k\right) \land \operatorname{safeRows}\left(m, rows\right)\right) \land s < k\right) \land \left(\forall q \in \mathbb{N} \to \operatorname{ZMod}\left(2\right),\; q \in \operatorname{headOption}\left(rows\right) \Rightarrow \left(s = 0 \lor q\left(0\right) = 0\right)\right)\right) \land \operatorname{gcd}\left(m, k + 1\right) \mid \operatorname{val}\left(-j\right)\right) \Rightarrow \operatorname{let} actions=\operatorname{chargeBlocks}\left(k, m, alphabet, rows\right) \operatorname{in} (\left(\left(\left(\operatorname{length}\left(actions\right) = \operatorname{length}\left(rows\right) \land \operatorname{fixedBlockArchive}\left(actions, \operatorname{some}\left((v,-j,s)\right)\right) = \operatorname{chargeArchive}\left(k, m, rows, v, j\right)\right) \land \operatorname{length}\left(\operatorname{fixedBlockArchive}\left(actions, \operatorname{some}\left((v,-j,s)\right)\right)\right) = \operatorname{length}\left(rows\right)\right) \land \left(\neg none \in \operatorname{fixedBlockArchive}\left(actions, \operatorname{some}\left((v,-j,s)\right)\right)\right)\right) \land \left(\exists N \in \mathbb{N},\; \exists source \in \operatorname{Fin}\left(N\right) \to Bool,\; \left(\left(\left(\left(\left(m \mid N \land \operatorname{DBonacciAdmissible}\left(k, N, source\right)\right) \land \operatorname{runBits}\left(k, source, \operatorname{some}\left((0,0,0)\right)\right) = \operatorname{some}\left((v,-j,s)\right)\right) \land \operatorname{originalWordValue}\left(k, source\right) = v\right) \land \operatorname{tailAfter}\left(0, source\right) = s\right) \land \left(\forall b \in \mathbb{N},\; \left(b + 1\right) \cdot m \le N \Rightarrow \operatorname{DBonacciAdmissible}\left(k, m, (\lambda (i:\operatorname{Fin}\left(m\right)), source\left(\langle b \cdot m + \operatorname{val}\left(i\right)\rangle_{N}\right))\right)\right)\right) \land \operatorname{fixedBlockArchive}\left(actions, \operatorname{runBits}\left(k, source, \operatorname{some}\left((0,0,0)\right)\right)\right) = \operatorname{chargeArchive}\left(k, m, rows, v, j\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.actual_shared_charge_suffix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

safeRows(m,rows) requires each row to have even total charge. For successive rows q and r it also requires q(m)=0 or r(0)=0. The first row requires a cleared incoming tail or q(0)=0. headOption is the optional head, with no member for an empty list. chargeBlocks maps the rows to the very prefixWord words, as allowed complete blocks for alphabet; its proof arguments 2<=k and m<k are omitted in the displayed applications. This one list depends on the rows and the reader, and is shared by all values, phases, tails and response children.

chargeArchive is empty for an empty row list. For q::rest, put next=v+windowCharge(k,m,q,j); its archive is some(next) followed by chargeArchive(k,m,rest,next,j-m). This is exactly the native complete-endpoint archive, of length rows.length with no rejected endpoint. Each of its words has m literal bits and costs one issued complete block. An all-one word is included when its incoming tail has been cleared.

The endpoint subgroup condition supplies one legal complete-block source realizing value v, phase -j and tail s simultaneously. Its original-weight scalar is v, every constituent source block is internally legal, and appending this same suffix gives the same predicted archive. This uses `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel` and the native archive of `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells`. The history witness proves joint reachability; it provides no reset, copied source, free padding or intermediate reading.

At an acquired child with current phase -jINITIAL+(a+1)m, the relative index in this statement is jINITIAL-(a+1)m. Each later row therefore acts at its actual chronological index. This coordinate calculation does not reveal the INITIAL phase. A decoder must still return the INITIAL label, rather than a label of the updated record. The result supplies the physical inversion and the seams with an adjacent zero; it does not select label codes, prove a decoder, handle a seam whose adjacent bits are both one, or assert a minimum fee for a full INITIAL target.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.actual_shared_charge_suffix`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.bitScalar`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.charge_archive_live`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.extendedBit`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.increment_derivative`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.short_legal`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.short_safe_execution`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.short_window_charge_inverse`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CoprimeSingletonLower](CoprimeSingletonLower.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CoprimeSingletonLower](CoprimeSingletonLower.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells](EndpointCells.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel](LiteralModel.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder](PhysicalWindowDecoder.md)
