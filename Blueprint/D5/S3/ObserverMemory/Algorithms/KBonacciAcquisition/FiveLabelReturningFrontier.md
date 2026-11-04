# Five labels and a returning width-seven frontier

## Abstract

Five distinct threshold-band labels at width seven have original adaptive and preset paid-block price 2Q+2.

**Definition 1.1 (Immutable initial threshold labels).**

$$(\forall (Y:\operatorname{Type}), ((\forall (Q:\mathbb{N}), ((\forall (labels:\operatorname{Fin}\left(7\right) \to Y), ((\forall (bottom:Y), ((\operatorname{initialLabel}\left(Q, labels, bottom, \operatorname{none}\right) = bottom \land (\forall (v:\operatorname{ZMod}\left(2\right)), ((\forall (p:\operatorname{ZMod}\left(7 \cdot Q + 1\right)), ((\forall (s:\mathbb{N}), (\operatorname{let} j=\operatorname{val}\left(-p\right) \operatorname{in} (\operatorname{initialLabel}\left(Q, labels, bottom, \operatorname{some}\left((v,p,s)\right)\right) = \operatorname{ifThenElse}\left(\operatorname{natSub}\left(7 \cdot Q, 6\right) \leq s, labels\left(6\right), \operatorname{ifThenElse}\left((1 \leq j \land j \leq 5), labels\left(j\right), labels\left(0\right)\right)\right)))))))))))))))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelReturningFrontier.initialLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let Q be a natural number and k=7Q. The entries zero through six of labels are respectively A, B1, B2, B3, B4, B5 and R. The value bottom is the separately known label of the initially rejected source. For a legal record q, put j=(-q.phase).val. Initial tails at least k-6 receive R; smaller initial tails receive Bj at phases 1 through 5 and A elsewhere. The initial value does not change this prescription. The expression ifThenElse denotes its ordinary conditional branches.

**Definition 1.2 (The fixed literal stream).**

$$(\forall (Q:\mathbb{N}), (\operatorname{attainingWords}\left(Q\right) = \operatorname{cons}\left(\operatorname{word}\left(1111110\right), \operatorname{append}\left(\operatorname{replicate}\left(\operatorname{natSub}\left(Q, 1\right), \operatorname{word}\left(1010101\right)\right), \operatorname{cons}\left(\operatorname{word}\left(0000100\right), \operatorname{append}\left(\operatorname{replicate}\left(\operatorname{natSub}\left(Q, 1\right), \operatorname{word}\left(0000000\right)\right), \operatorname{list}\left(\operatorname{word}\left(0000110\right), \operatorname{word}\left(1000000\right)\right)\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelReturningFrontier.attainingWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function word reads the displayed seven binary digits in their literal left-to-right order, preserving leading zeros. Concatenate 1111110, Q-1 copies of 1010101, 0000100, Q-1 copies of 0000000, 0000110 and 1000000. Each member is a function from Fin 7 to Bool. The repetitions contain complete paid blocks; no time displacement is free.

**Definition 1.3 (Decode the acquired archive).**

$$(\forall (Y:\operatorname{Type}), ((\forall (Q:\mathbb{N}), ((\forall (labels:\operatorname{Fin}\left(7\right) \to Y), ((\forall (bottom:Y), ((\forall (v:\operatorname{ZMod}\left(2\right)), ((\forall (ar:\operatorname{Archive}\left(7\right)), (\operatorname{archiveDecoder}\left(Q, labels, bottom, v, ar\right) = \operatorname{ifThenElse}\left(\operatorname{compatible}\left(Q, v, ar\right), \operatorname{initialLabel}\left(Q, labels, bottom, \operatorname{chosenRecord}\left(Q, v, ar\right)\right), bottom\right)))))))))))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelReturningFrontier.archiveDecoder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For fixed Q, labels, bottom and free value v, compatible(Q,v,ar) is the proposition that there are a phase p modulo 7Q+1 and a tail s<7Q with scriptArchive(attainingWords Q,some(v,p,s))=ar. When this proposition holds, chosenRecord is the legal record obtained by choosing such a phase and then such a tail. The decoder returns initialLabel of that record; when the proposition fails it returns bottom. These choices use only the observed archive, the free value and the known parameters. For Q≥2 the archive-separation argument below proves that every compatible record has the same initial label.

**Theorem 1.4 (Both global prices and the actual named-stream trace).**

$$(\forall (Y:\operatorname{Type}), ((\forall (Q:\mathbb{N}), (((2 \leq Q) \implies ((\forall (labels:\operatorname{Fin}\left(7\right) \to Y), (((\operatorname{Injective}\left(labels\right)) \implies ((\forall (bottom:Y), ((\forall (alphabet:\operatorname{Bool}), ((\operatorname{GlobalAdaptivePrice}\left(7 \cdot Q, 7, \operatorname{positivek}, alphabet, \operatorname{initialLabel}\left(Q, labels, bottom\right)\right) = \operatorname{cast}\left(2 \cdot Q + 2, \operatorname{ENat}\right) \land (\operatorname{GlobalPresetPrice}\left(7 \cdot Q, 7, \operatorname{positivek}, alphabet, \operatorname{initialLabel}\left(Q, labels, bottom\right)\right) = \operatorname{cast}\left(2 \cdot Q + 2, \operatorname{ENat}\right) \land (\operatorname{length}\left(\operatorname{attainingWords}\left(Q\right)\right) = 2 \cdot Q + 2 \land (\forall (history:\operatorname{List}\left(\operatorname{AllowedBlock}\left(7 \cdot Q, 7, alphabet\right)\right)), (\operatorname{let} w=\operatorname{flattenHistory}\left(history\right) \operatorname{in} (\operatorname{let} f=\operatorname{initialLabel}\left(Q, labels, bottom\right) \operatorname{in} (\operatorname{let} pi=\operatorname{policy}\left(Q, labels, bottom\right) \operatorname{in} (\operatorname{let} q=\operatorname{OriginalRecord}\left(7 \cdot Q, \operatorname{positivek}, w\right) \operatorname{in} (\operatorname{let} issued=\operatorname{ifThenElse}\left(q = \operatorname{none}, \operatorname{nil}, \operatorname{scriptArchive}\left(\operatorname{attainingWords}\left(Q\right), q\right)\right) \operatorname{in} ((\operatorname{PaidTrace}\left(pi, \operatorname{output}\left(7 \cdot Q, \operatorname{positivek}, w\right), q, \operatorname{nil}, issued, f\left(q\right)\right) \land (\operatorname{map}\left(\operatorname{fst}, issued\right) = \operatorname{ifThenElse}\left(q = \operatorname{none}, \operatorname{nil}, \operatorname{attainingWords}\left(Q\right)\right) \land (\operatorname{length}\left(issued\right) = \operatorname{ifThenElse}\left(q = \operatorname{none}, 0, 2 \cdot Q + 2\right) \land \operatorname{execute}\left(7 \cdot Q, \operatorname{positivek}, pi, 2 \cdot Q + 2, w, \operatorname{output}\left(7 \cdot Q, \operatorname{positivek}, w\right), \operatorname{nil}\right) = \operatorname{some}\left((f\left(q\right),\operatorname{length}\left(issued\right))\right))))))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelReturningFrontier.original_five_label_returning_frontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume Q is at least two and labels is injective. Thus the five band labels are pairwise different and differ from A, and R differs from every low-tail label. The parameter alphabet selects either all seven-bit words or the internally legal seven-bit words. Since 7<7Q, these alphabets coincide, while every actual seam still uses the original absorbing-rejection transition.

GlobalAdaptivePrice and GlobalPresetPrice use the original complete-block reader and the full prior of actual finite block histories. The free initial observation is the legal value or rejection. Every later choice uses only that remembered observation and the chronological archive of its own issued words and endpoint replies. Empty histories, rejected histories, both legal free values, every initial phase and every legal initial tail remain included. The conclusion concerns the immutable initial label, even after a zero clears its tail.

For the trace formula, flattenHistory concatenates the seven bits of every initial history block. The record q is OriginalRecord of that actual word w. The policy pi stops with bottom on initial rejection; on free legal value v it follows finalSelector for attainingWords Q, then applies archiveDecoder Q labels bottom v. This decoder selects the initial label of any legal initial record producing that same archive and free value. Archive separation proves this selection independent of the representative. The decoder uses no initial phase, hidden clock, intermediate reading, reset or second execution.

The issued archive is empty exactly on initial rejection and is scriptArchive of the displayed literal list on every legal initial record. PaidTrace retains its actual endpoint replies, map(fst,issued) retains exactly the displayed words, and execute returns the immutable label together with the archive length. This length is zero on initial rejection and 2Q+2 otherwise. The positivity argument positivek is the proof that k>0 supplied by Q≥2. All four trace assertions belong to the same original history.

For the lower bound compare actual initial tails k-7 and k-6 at one common phase and legal value. Their labels differ. A root whose first zero occurs before six leading ones merges them irreversibly. A root with seven leading ones rejects both. Therefore every correct root is 1111110. It clears all low tails and has zero response on phases 1 through 5. The joint actual-source theorem supplies these records as complete-block histories; it does not combine marginal reachability witnesses.

Before a total fee of 2Q+2, after the root the only potentially informative band endpoints have indices Q and 2Q. At every other index through 2Q the relative band phase lies beyond the full window. The common-tail compression theorem removes only these silent nodes, preserving early stops and uniform rejection. A binary protocol with at most two informative endpoints has at most four distinct label leaves. It cannot return the five different initial band labels. This rules out every smaller lawful adaptive budget.

The first Q displayed blocks reject precisely the high initial tails and screen all outside phases. The root has full charge support {0,6}. Each later scan word has charge one on all eight ordered window vertices, including its endpoints. Every outside phase not screened by the root is covered by a later scan window. The continuing zero-difference archive therefore contains exactly initial phases 1 through 5.

The remaining query words are issued at indices Q, 2Q and 2Q+1. Their actual full-window masks are {3,4}, {2,4} and {5,6}. The five initial band phases consequently have distinct acquired difference codes 000, 010, 100, 110 and 001 in increasing phase order. Phase six is absent from this same continuing scan archive. Phase five returns at the left endpoint of the last window and uses this excluded donor; the stream does not wait until 3Q.

The root ends in zero. Every suffix word has a zero at local position one; the internal-zero execution theorem bounds all inherited seams, including consecutive 1010101 blocks. Its marked-zero spacing is seven and k is at least fourteen. Charge inversion recovers exactly the displayed literal words and their actual tails. The Q-1 all-zero words between the first two queries remain in the archive and are paid. The complete length is 1+(Q-1)+1+(Q-1)+2=2Q+2. The preset construction supplies the upper bound; preset inclusion and the adaptive lower bound give both equal prices.

These conclusions apply for every Q≥2, including Q=2. They use neither a calendar guard with three common visits nor an unrestricted subset-query alphabet. The reader, joint record realization, inversion, common-tail compression and paid-trace interfaces are the cited original mathematical suppliers. The source-specific combination gives this threshold target and its named literal stream; it asserts no general arbitrary-target optimum or literature priority.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelReturningFrontier.archiveDecoder`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelReturningFrontier.attainingWords`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelReturningFrontier.initialLabel`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FiveLabelReturningFrontier.original_five_label_returning_frontier`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection](DonorCorrection.md)
