# Internal zeros and literal seam safety

## Abstract

A zero inside each complete word controls the inherited run across its next seam.

**Theorem 1.1 (Internal zero execution).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(m\right) \to Bool,\; \forall i \in \operatorname{Fin}\left(m\right),\; \forall v \in \operatorname{ZMod}\left(2\right),\; \forall phase \in \operatorname{ZMod}\left(k + 1\right),\; \forall s \in \mathbb{N},\; \left(\left(\left(\left(2 \le k \land m < k\right) \land w\left(i\right) = false\right) \land s < k\right) \land \left(s + \operatorname{val}\left(i\right) < k \lor w\left(\langle 0\rangle_{m}\right) = false\right)\right) \Rightarrow \left(\operatorname{runBits}\left(k, w, \operatorname{some}\left(\langle v,phase,s\rangle\right)\right) = \operatorname{some}\left(\langle v + \operatorname{wordIncrement}\left(k, phase, w\right),phase + m,\operatorname{tailAfter}\left(0, w\right)\rangle\right) \land \operatorname{tailAfter}\left(0, w\right) \le m - 1 - \operatorname{val}\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety.internal_zero_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The word has m<k bits and a marked zero at position i. If the incoming tail plus i is below k, every bit before that mark is safe. Alternatively a zero at the first position clears any legal inherited tail. The marked zero makes the terminal tail independent of the incoming tail and bounds it by m-1-i. The scalar and phase are those of the original literal executor. The bound uses the mark, so later seams may have two adjacent one bits. It does not require a zero at either block boundary.

Subtraction in the tail bound is natural subtraction. The index i:Fin(m) already implies m>0. Only the complete endpoint is observed; the internal zero is a literal bit of the paid word.

**Theorem 1.2 (One common literal suffix).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall alphabet \in Bool,\; \forall marked \in \operatorname{List}\left((\mathbb{N} \to \operatorname{ZMod}\left(2\right)) \times \operatorname{Fin}\left(m\right)\right),\; \forall v \in \operatorname{ZMod}\left(2\right),\; \forall j \in \operatorname{ZMod}\left(k + 1\right),\; \forall s \in \mathbb{N},\; \left(\left(\left(\left(\left(\left(\left(\left(3 \le k \land 1 \le m\right) \land m < k\right) \land \left(\forall e \in (\mathbb{N} \to \operatorname{ZMod}\left(2\right)) \times \operatorname{Fin}\left(m\right),\; e \in marked \Rightarrow \sum_{h\in \operatorname{range}\left(m + 1\right)} \operatorname{row}\left(e\right)\left(h\right) = 0\right)\right) \land \left(\forall e \in (\mathbb{N} \to \operatorname{ZMod}\left(2\right)) \times \operatorname{Fin}\left(m\right),\; e \in marked \Rightarrow \operatorname{prefixWord}\left(m, \operatorname{row}\left(e\right)\right)\left(\operatorname{second}\left(e\right)\right) = false\right)\right) \land \operatorname{IsChain}\left((\lambda (a:(\mathbb{N} \to \operatorname{ZMod}\left(2\right)) \times \operatorname{Fin}\left(m\right)), (\lambda (b:(\mathbb{N} \to \operatorname{ZMod}\left(2\right)) \times \operatorname{Fin}\left(m\right)), m + \operatorname{mark}\left(b\right) \le k + \operatorname{mark}\left(a\right))), marked\right)\right) \land s < k\right) \land \left(\forall e \in (\mathbb{N} \to \operatorname{ZMod}\left(2\right)) \times \operatorname{Fin}\left(m\right),\; e \in \operatorname{headOption}\left(marked\right) \Rightarrow \left(s + \operatorname{mark}\left(e\right) < k \lor \operatorname{row}\left(e\right)\left(0\right) = 0\right)\right)\right) \land \operatorname{gcd}\left(m, k + 1\right) \mid \operatorname{val}\left(-j\right)\right) \Rightarrow \left(\left(\left(\left(\operatorname{length}\left(\operatorname{chargeBlocks}\left(k, m, alphabet, \operatorname{mapFirst}\left(marked\right)\right)\right) = \operatorname{length}\left(marked\right) \land \operatorname{fixedBlockArchive}\left(\operatorname{chargeBlocks}\left(k, m, alphabet, \operatorname{mapFirst}\left(marked\right)\right), \operatorname{some}\left(\langle v,-j,s\rangle\right)\right) = \operatorname{chargeArchive}\left(k, m, \operatorname{mapFirst}\left(marked\right), v, j\right)\right) \land \operatorname{length}\left(\operatorname{fixedBlockArchive}\left(\operatorname{chargeBlocks}\left(k, m, alphabet, \operatorname{mapFirst}\left(marked\right)\right), \operatorname{some}\left(\langle v,-j,s\rangle\right)\right)\right) = \operatorname{length}\left(marked\right)\right) \land \left(\neg none \in \operatorname{fixedBlockArchive}\left(\operatorname{chargeBlocks}\left(k, m, alphabet, \operatorname{mapFirst}\left(marked\right)\right), \operatorname{some}\left(\langle v,-j,s\rangle\right)\right)\right)\right) \land \left(\exists N \in \mathbb{N},\; \exists source \in \operatorname{Fin}\left(N\right) \to Bool,\; \left(\left(\left(\left(\left(m \mid N \land \operatorname{DBonacciAdmissible}\left(k, N, source\right)\right) \land \operatorname{runBits}\left(k, source, \operatorname{some}\left(\langle 0,0,0\rangle\right)\right) = \operatorname{some}\left(\langle v,-j,s\rangle\right)\right) \land \operatorname{originalWordValue}\left(k, source\right) = v\right) \land \operatorname{tailAfter}\left(0, source\right) = s\right) \land \left(\forall b \in \mathbb{N},\; \left(b + 1\right) \cdot m \le N \Rightarrow \operatorname{DBonacciAdmissible}\left(k, m, (\lambda (i:\operatorname{Fin}\left(m\right)), source\left(\langle b \cdot m + \operatorname{val}\left(i\right)\rangle_{N}\right))\right)\right)\right) \land \operatorname{fixedBlockArchive}\left(\operatorname{chargeBlocks}\left(k, m, alphabet, \operatorname{mapFirst}\left(marked\right)\right), \operatorname{runBits}\left(k, source, \operatorname{some}\left(\langle 0,0,0\rangle\right)\right)\right) = \operatorname{chargeArchive}\left(k, m, \operatorname{mapFirst}\left(marked\right), v, j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety.actual_internal_zero_charge_suffix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An entry is a pair consisting of an ordered charge row and a marked Fin(m) position. Here row(e) is its first projection, second(e) its second projection, mark(e) the natural value of that position, and mapFirst(marked)=marked.map(Prod.fst). chargeBlocks omits the proof arguments 2<=k and m<k in the display. IsChain applies the displayed relation only to consecutive entries. headOption denotes List.head?.

Every row is even and its prefix-parity word is zero at the marked position. For adjacent marks a,b the gap bound m+mark(b)<=k+mark(a) makes the outgoing tail from a safe up to b. The first word also satisfies the stated incoming condition. Thus the one common list of words gives exactly chargeArchive, with one completed live reading for every issued block. Its relative phase changes by minus m each time, so the charge windows follow their actual chronology.

The source witness realizes the value, phase and inherited tail jointly using original weights and legal complete history blocks. The same suffix works in either alphabet. This uses `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel` and the row inverse in `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse`. The theorem supplies physical safety and the whole archive. It does not construct the charge rows, distinguish phase labels, synthesize stopping or decoding, or establish an adaptive-to-preset price inequality.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety.actual_internal_zero_charge_suffix`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety.internal_zero_execution`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse](WindowChargeInverse.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel](LiteralModel.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse](WindowChargeInverse.md)
