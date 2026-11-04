# Two adjacent low-tail labels

## Abstract

The threshold-three immutable target has original adaptive and preset price Q+1 at odd width and Q+2 at even width.

**Theorem 1.1 (The first zero of a literal list).**

$$(\forall (bits:\operatorname{List}\left(\operatorname{Bool}\right)), (bits = \operatorname{replicate}\left(\operatorname{length}\left(bits\right), \operatorname{true}\right) \lor \left(\exists a \in \mathbb{N},\; \exists rest \in \operatorname{List}\left(\operatorname{Bool}\right),\; bits = \operatorname{append}\left(\operatorname{replicate}\left(a, \operatorname{true}\right), \operatorname{cons}\left(\operatorname{false}, rest\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.first_zero_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite Boolean list is either all ones, or is a run of a leading ones followed by its first zero and a remaining literal suffix. The list can be empty, in which case the all-one alternative holds with length zero.

**Theorem 1.2 (A first-tour window misses an INITIAL phase).**

$$(\forall (Q:\mathbb{N}), ((\forall (m:\mathbb{N}), ((\forall (t:\mathbb{N}), ((\forall (j:\mathbb{N}), ((((2 \leq Q \land (4 \leq m \land (t < Q \land (j \leq Q \cdot m \land (j < t \cdot m \lor \left(t + 1\right) \cdot m < j)))))) \implies ((\forall (B:\operatorname{Fin}\left(m\right) \to \operatorname{Bool}), (\operatorname{wordIncrement}\left(Q \cdot m, -\operatorname{cast}\left(j\right) + \operatorname{cast}\left(t \cdot m\right), B\right) = 0))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.response_off` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary literal m-bit block B, first-tour index t<Q, and INITIAL index j<=Qm, the response is zero if j<tm or (t+1)m<j. The phase expression is evaluated in ZMod(Qm+1). This applies to every controller's own block and requires no assumption about its root, labels or acquired tail.

**Definition 1.3 (The immutable initial target).**

$$(\forall (Y:\operatorname{Type}), ((\forall (Q:\mathbb{N}), ((\forall (m:\mathbb{N}), ((\forall (labels:\operatorname{Fin}\left(4\right) \to Y), ((\forall (bottom:Y), ((\operatorname{initialLabel}\left(Q, m, labels, bottom, \operatorname{none}\right) = bottom \land (\forall (v:\operatorname{ZMod}\left(2\right)), ((\forall (p:\operatorname{ZMod}\left(Q \cdot m + 1\right)), ((\forall (s:\mathbb{N}), (\operatorname{let} j=\operatorname{val}\left(-p\right) \operatorname{in} (\operatorname{initialLabel}\left(Q, m, labels, bottom, \operatorname{some}\left((v,p,s)\right)\right) = \operatorname{ifThenElse}\left(\operatorname{natSub}\left(Q \cdot m, 3\right) \leq s, labels\left(3\right), \operatorname{ifThenElse}\left(j = 1, labels\left(1\right), \operatorname{ifThenElse}\left(j = 2, labels\left(2\right), labels\left(0\right)\right)\right)\right)))))))))))))))))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.initialLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For k=Qm, the four entries of labels are A, B, C and R. Bottom is an arbitrary separately known label, without a distinctness condition. A legal INITIAL record with tail at least k-3 receives R. At smaller INITIAL tails its phase j=(-phase).val receives B at one, C at two and A elsewhere. The free scalar value is immaterial to this label map. The target of the updated record is never substituted for this INITIAL target.

**Theorem 1.4 (The extra block at every even width).**

$$(\forall (Y:\operatorname{Type}), ((\forall (Q:\mathbb{N}), ((\forall (m:\mathbb{N}), ((((2 \leq Q \land (4 \leq m \land \operatorname{Even}\left(m\right)))) \implies ((\forall (labels:\operatorname{Fin}\left(4\right) \to Y), (((\operatorname{Injective}\left(labels\right)) \implies ((\forall (bottom:Y), ((\forall (alphabet:\operatorname{Bool}), ((\forall (d:\mathbb{N}), (((\operatorname{OriginalAdaptiveFeasible}\left(Q \cdot m, m, \operatorname{positivek}, alphabet, \operatorname{initialLabel}\left(Q, m, labels, bottom\right), d\right)) \implies (Q + 2 \leq d))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.even_adaptive_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume Q is at least two, m is at least four and even, and labels is injective. Every feasible original adaptive budget d is at least Q+2. OriginalAdaptiveFeasible quantifies one lawful selector over all actual complete-block histories, both free values and every legal INITIAL tail. The alphabet parameter includes both original Bool control alphabets. Early stopping and absorbing rejection remain part of the original execute recursion.

Compare actual INITIAL tails k-4 and k-3 with the same phase and value. Their targets differ. A first zero before position three merges them; a first zero after position three, or an all-one root, rejects both. Correctness therefore forces exactly three leading ones followed by zero. The remaining root suffix is unrestricted. Joint original-history realization supplies these complete records.

Follow the single chronological archive with zero endpoint differences. Phases one and two have zero root response. Before index Q all later windows miss both phases. They retain a common scalar and current tail. Different labels B and C exclude stopping and uniform rejection at every earlier node. Thus this archive is traversed by actual sources under the controller's own chosen actions.

If all outside INITIAL phases were screened during these Q blocks, every strictly interior outside vertex of each window would have response one. At the root, the three forced leading bits and the zero at position three, followed by those required interior differences, force its last bit to zero at even width. To screen the shared boundary the next block must start with one. Its required alternating interior differences force its last bit to zero again. Induction leaves the final phase k unqueried, contradicting complete screening. Consequently some outside INITIAL source survives. Its phase can depend on the policy and need not be m.

That survivor, B and C traverse the same acquired archive, with the same scalar and current tail. They have three distinct immutable labels. A remaining budget of at most one block admits at most two different successful endpoint differences; rejection is uniform for their common tail and cannot separate them. The original own-charge separation theorem therefore rules out every total budget at most Q+1.

The policy-dependent survivor is used on the actual lower-bound path; no fixed outside phase is assumed.

**Definition 1.5 (The first final query).**

$$(\forall (m:\mathbb{N}), ((\forall (i:\operatorname{Fin}\left(m\right)), (\operatorname{queryWord}\left(m, i\right) = \operatorname{decide}\left(\operatorname{val}\left(i\right) = 1\right)))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.queryWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The one is at local index one; all other bits are zero.

**Definition 1.6 (The even-width final query).**

$$(\forall (m:\mathbb{N}), ((\forall (i:\operatorname{Fin}\left(m\right)), (\operatorname{finalWord}\left(m, i\right) = \operatorname{decide}\left(\operatorname{val}\left(i\right) = 0\right)))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.finalWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The one is at local index zero; all other bits are zero.

**Definition 1.7 (The literal attaining stream).**

$$(\forall (Q:\mathbb{N}), ((\forall (m:\mathbb{N}), (\operatorname{attainingWords}\left(Q, m\right) = \operatorname{cons}\left(\operatorname{rootWord}\left(m\right), \operatorname{append}\left(\operatorname{replicate}\left(\operatorname{natSub}\left(Q, 1\right), \operatorname{middleWord}\left(m\right)\right), \operatorname{cons}\left(\operatorname{queryWord}\left(m\right), \operatorname{ifThenElse}\left(\operatorname{mod}\left(m, 2\right) = 0, \operatorname{list}\left(\operatorname{finalWord}\left(m\right)\right), \operatorname{nil}\right)\right)\right)\right)))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.attainingWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a local index i<m, rootWord is true exactly when i<3 or i is even. The middleWord bit is true exactly when i has parity one at even m and parity zero at odd m. The queryWord has its only one at index one; finalWord has its only one at index zero. Thus at odd m the stream is 111(01)^((m-3)/2), Q-1 copies of (10)^((m-1)/2)1, and 01 followed by m-2 zeros. At even m it is 1110(10)^((m-4)/2), Q-1 copies of (01)^(m/2), 01 followed by m-2 zeros, and 1 followed by m-1 zeros. Repetition exponents count literal pairs. Every displayed block is paid.

**Definition 1.8 (Decode the acquired original archive).**

$$(\forall (Y:\operatorname{Type}), ((\forall (Q:\mathbb{N}), ((\forall (m:\mathbb{N}), ((\forall (labels:\operatorname{Fin}\left(4\right) \to Y), ((\forall (bottom:Y), ((\forall (v:\operatorname{ZMod}\left(2\right)), ((\forall (ar:\operatorname{Archive}\left(m\right)), (\operatorname{archiveDecoder}\left(Q, m, labels, bottom, v, ar\right) = \operatorname{ifThenElse}\left(\operatorname{compatible}\left(Q, m, v, ar\right), \operatorname{initialLabel}\left(Q, m, labels, bottom, \operatorname{chosenRecord}\left(Q, m, v, ar\right)\right), bottom\right)))))))))))))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.archiveDecoder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compatibility means that some original phase and tail s<Qm, with the given free value, produce exactly this scriptArchive. chosenRecord selects one such record. The decoder returns its INITIAL target; if no compatible record exists it returns bottom. Archive separation proves that all compatible records have the same INITIAL target. The choices use only the acquired chronological archive and the remembered free scalar.

**Theorem 1.9 (Exact prices and the same-history paid trace).**

$$(\forall (Y:\operatorname{Type}), ((\forall (Q:\mathbb{N}), ((\forall (m:\mathbb{N}), ((((2 \leq Q \land 4 \leq m)) \implies ((\forall (labels:\operatorname{Fin}\left(4\right) \to Y), (((\operatorname{Injective}\left(labels\right)) \implies ((\forall (bottom:Y), ((\forall (alphabet:\operatorname{Bool}), ((\operatorname{GlobalAdaptivePrice}\left(Q \cdot m, m, \operatorname{positivek}, alphabet, \operatorname{initialLabel}\left(Q, m, labels, bottom\right)\right) = \operatorname{cast}\left(Q + 1 + \operatorname{ifThenElse}\left(\operatorname{mod}\left(m, 2\right) = 0, 1, 0\right), \operatorname{ENat}\right) \land (\operatorname{GlobalPresetPrice}\left(Q \cdot m, m, \operatorname{positivek}, alphabet, \operatorname{initialLabel}\left(Q, m, labels, bottom\right)\right) = \operatorname{cast}\left(Q + 1 + \operatorname{ifThenElse}\left(\operatorname{mod}\left(m, 2\right) = 0, 1, 0\right), \operatorname{ENat}\right) \land (\operatorname{length}\left(\operatorname{attainingWords}\left(Q, m\right)\right) = Q + 1 + \operatorname{ifThenElse}\left(\operatorname{mod}\left(m, 2\right) = 0, 1, 0\right) \land ((\forall (s:\mathbb{N}), ((\operatorname{tailAfter}\left(s, \operatorname{queryWord}\left(m\right)\right) = 0 \land \operatorname{tailAfter}\left(s, \operatorname{finalWord}\left(m\right)\right) = 0))) \land ((\operatorname{map}\left(\operatorname{ofFn}, \operatorname{attainingWords}\left(2, 4\right)\right) = \operatorname{list}\left(\operatorname{bits}\left(1110\right), \operatorname{bits}\left(0101\right), \operatorname{bits}\left(0100\right), \operatorname{bits}\left(1000\right)\right) \land \operatorname{map}\left(\operatorname{ofFn}, \operatorname{attainingWords}\left(2, 5\right)\right) = \operatorname{list}\left(\operatorname{bits}\left(11101\right), \operatorname{bits}\left(10101\right), \operatorname{bits}\left(01000\right)\right)) \land (\forall (history:\operatorname{List}\left(\operatorname{AllowedBlock}\left(Q \cdot m, m, alphabet\right)\right)), (\operatorname{let} w=\operatorname{flattenHistory}\left(history\right) \operatorname{in} (\operatorname{let} f=\operatorname{initialLabel}\left(Q, m, labels, bottom\right) \operatorname{in} (\operatorname{let} pi=\operatorname{policy}\left(Q, m, labels, bottom\right) \operatorname{in} (\operatorname{let} q=\operatorname{OriginalRecord}\left(Q \cdot m, \operatorname{positivek}, w\right) \operatorname{in} (\operatorname{let} issued=\operatorname{ifThenElse}\left(q = \operatorname{none}, \operatorname{nil}, \operatorname{scriptArchive}\left(\operatorname{attainingWords}\left(Q, m\right), q\right)\right) \operatorname{in} ((\operatorname{PaidTrace}\left(pi, \operatorname{output}\left(Q \cdot m, \operatorname{positivek}, w\right), q, \operatorname{nil}, issued, f\left(q\right)\right) \land (\operatorname{map}\left(\operatorname{fst}, issued\right) = \operatorname{ifThenElse}\left(q = \operatorname{none}, \operatorname{nil}, \operatorname{attainingWords}\left(Q, m\right)\right) \land (\operatorname{length}\left(issued\right) = \operatorname{ifThenElse}\left(q = \operatorname{none}, 0, Q + 1 + \operatorname{ifThenElse}\left(\operatorname{mod}\left(m, 2\right) = 0, 1, 0\right)\right) \land \operatorname{execute}\left(Q \cdot m, \operatorname{positivek}, pi, Q + 1 + \operatorname{ifThenElse}\left(\operatorname{mod}\left(m, 2\right) = 0, 1, 0\right), w, \operatorname{output}\left(Q \cdot m, \operatorname{positivek}, w\right), \operatorname{nil}\right) = \operatorname{some}\left((f\left(q\right),\operatorname{length}\left(issued\right))\right))))))))))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.original_threshold_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be at least two, m at least four and labels injective into an arbitrary universe-polymorphic type Y. The arbitrary bottom label need not differ from any entry. The alphabet parameter includes both original Bool alphabets. Set fee=Q+1 at odd m and fee=Q+2 at even m. Both global prices equal fee. The original complete-block prior includes all phases, both scalar values, all legal INITIAL tails, the empty history and rejected histories.

In the trace formula flattenHistory concatenates the literal bits of the given initial history. The policy stops with bottom on a free rejected observation; otherwise it follows finalSelector for the displayed stream and then applies archiveDecoder at the remembered free value. Its issued archive is empty on initial rejection and the actual scriptArchive on every legal record. The PaidTrace, exact issued word list, paid length and execute equality all refer to this same history. The returned value is the immutable initial label. positivek denotes the positivity proof supplied by the displayed hypotheses.

The root rejects precisely INITIAL tails at least k-3. Its acquired charge and all later legal charges are differences of consecutive actual endpoint readings. The first Q blocks have zero support exactly {1,2} at odd width and {1,2,m} at even width. Any earlier positive scan difference belongs to A; root rejection belongs to R. At index Q, queryWord has the actual INITIAL mask {0,1}, so it identifies B. At odd width the remaining zero identifies C. At even width the remaining pair is C at phase two and A at phase m. The finalWord at index Q+1 has INITIAL mask {m-1,m} and separates these two sources. No root suffix or intermediate support is substituted for INITIAL phases.

The root contains zero at position three and leaves tail at most m-4. Every following word contains zero at local position zero or one. The internal-zero execution theorem proves all actual seams legal for k=Qm; absorbing rejection and the exact literal tail are retained. QueryWord and finalWord end in zero. Their trailing zeros are literal paid symbols. There is no unpaid clearing, reset or time displacement.

For the baseline lower bound the existing original_cost_lower theorem is applied to the three distinct tail-zero labels A, B and C, with gcd(m,Qm+1)=1. Its first-window wait is Q and its binary depth is two, giving Q+1. The even-width actual-policy survivor theorem supplies the extra block. The original script-preset construction supplies the upper bound; preset inclusion and the adaptive lower bound yield both exact global prices. For Q=2,m=4 the literal list is 1110|0101|0100|1000 and fee four. For Q=2,m=5 it is 11101|10101|01000 and fee three.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.archiveDecoder`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.attainingWords`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.even_adaptive_lower`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.finalWord`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.first_zero_form`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.initialLabel`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.original_threshold_three`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.queryWord`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels.response_off`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection](DonorCorrection.md)
