# Own-path padded charge arrays

## Abstract

Chronological own-path differences separate arbitrary INITIAL phase labels.

**Definition 1.1 (Own successful differences).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges.ownCharge`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges.ownCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting from the current scalar, phase, tail, remembered free reading and actual archive, ownCharge follows the selector for a finite remaining budget. A successful issued word contributes its literal increment and recurses at the next scalar, phase, tail and completed archive. A stop, exhausted budget or rejection gives zero for all remaining coordinates. The rejection case retires a common-tail candidate archive; correctness will force every INITIAL label in that archive to agree.

**Definition 1.2 (The full phase array).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges.phaseCharges`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges.phaseCharges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For k=2m-2, a constant phase table is retired at the root and has the zero array. Otherwise phaseCharges evaluates ownCharge at INITIAL scalar zero, phase minus j, tail zero, free reading some zero and empty archive. Each phase follows its own acquired path. These finite design coordinates are not extra observations available to a controller.

**Theorem 1.3 (Support, cleared root and label separation).**

$$\forall Y \in Type,\; \forall m \in \mathbb{N},\; \forall alphabet \in Bool,\; \forall f \in \operatorname{Option}\left(\operatorname{LiveRecord}\left(2 \cdot m - 2\right)\right) \to Y,\; \forall table \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right) \to Y,\; \forall pi \in \operatorname{Selector}\left(m, Y\right),\; \forall d \in \mathbb{N},\; \left(\left(5 \le m \land \left(\forall v \in \operatorname{ZMod}\left(2\right),\; \forall j \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right),\; \forall s \in \mathbb{N},\; s < 2 \cdot m - 2 \Rightarrow f\left(\operatorname{some}\left(\langle v,-j,s\rangle\right)\right) = table\left(j\right)\right)\right) \land \left(\forall history \in \operatorname{List}\left(\operatorname{AllowedBlock}\left(2 \cdot m - 2, m, alphabet\right)\right),\; \operatorname{output}\left(2 \cdot m - 2, \operatorname{flattenWords}\left(history\right)\right) = \operatorname{some}\left(0\right) \Rightarrow \left(\exists c \in \mathbb{N},\; c \le d \land \operatorname{execute}\left(2 \cdot m - 2, pi, d, \operatorname{flattenWords}\left(history\right), \operatorname{some}\left(0\right), nil\right) = \operatorname{some}\left((f\left(\operatorname{OriginalRecord}\left(2 \cdot m - 2, \operatorname{flattenWords}\left(history\right)\right)\right),c)\right)\right)\right)\right) \Rightarrow \left(\left(\left(\forall t \in \mathbb{N},\; \forall j \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right),\; m < \operatorname{val}\left(j - t \cdot m\right) \Rightarrow \operatorname{phaseCharges}\left(table, pi, d, t, j\right) = 0\right) \land \operatorname{phaseCharges}\left(table, pi, d, 0, 0\right) = 0\right) \land \left(\forall j \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right),\; \forall l \in \operatorname{ZMod}\left(2 \cdot m - 2 + 1\right),\; \left(\forall t \in \mathbb{N},\; t < d \Rightarrow \operatorname{phaseCharges}\left(table, pi, d, t, j\right) = \operatorname{phaseCharges}\left(table, pi, d, t, l\right)\right) \Rightarrow table\left(j\right) = table\left(l\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges.original_adaptive_charge_array` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Y is arbitrary, including higher universes. In the display k abbreviates 2m-2; flattenWords is the original history flatMap of each complete literal word. output, execute and OriginalRecord are the original scanner definitions, with their positive-k proof arguments omitted. nil is the empty acquired archive. Subtraction inside val is in ZMod(k+1), after casting t*m into that group. Natural subtraction in k remains truncated.

The controller is arbitrary. Its correctness premise covers every actual complete-block history with free reading zero, in either original alphabet, and the target premise retains both scalar values and every legal inherited tail. Coprimality and the joint-history realization supply every phase and tail in that premise. A nonconstant table forbids a leading-one root: tail k-1 would reject all phases into one absorbing native execution. Its first bit is therefore zero and clears every inherited tail. The root phase-zero increment is zero.

At a successful action, literal legality depends on the common tail and word, not on phase or scalar. The endpoint increment selects the next common-scalar, common-tail archive. Equal padded columns follow the same archive through the earlier stop. A common rejection gives the same absorbing continuation and hence a common label; replacing that continuation by zeros loses no label distinction. The support condition follows the actual chronological phase shift t*m, retaining waits and every issued word at its own index.

This theorem constructs the supported adaptive design array. Its rows need not have even full-window parity and need not be a common preset word. It establishes no donor correction, phase-separating fallback stream, preset decoder, finite price or four-block inequality.

**Theorem 1.4 (Correct original histories give every actual native source).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges.native_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges.native_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary k>=2, m>=1, either original alphabet, target f, saved value v, budget d and selector, suppose the selector returns the INITIAL target within d paid complete words on every original history whose free scalar is v. For every phase with gcd(m,k+1) dividing its representative and every inherited legal tail s<k, NativeExecute from (v,phase,s) returns f of that INITIAL record with some fee c<=d. Actual-history realization and scanner agreement transfer correctness without supplying the controller a history, phase, tail or clock.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges.native_fiber`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges.original_adaptive_charge_array`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges.ownCharge`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges.phaseCharges`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety](InternalZeroSafety.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost](OriginalNarrowCost.md)
