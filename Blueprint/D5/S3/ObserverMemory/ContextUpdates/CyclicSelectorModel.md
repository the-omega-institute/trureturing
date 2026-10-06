# Cyclic Selector Model

## Abstract

The cyclic selector model keeps every labelled source coordinate and the complete observation trace.

`D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorModel` defines G = ZMod 2 times ZMod m. A source consists of one receiver, r-1 labelled senders and the second coordinate of a kernel offset h. Its clock is the receiver plus the sender sum plus h. An observation keeps the receiver, this clock and every sender reply; the reply subtracts the selected element exactly for a nonzero binary coordinate.

The selector is (1,0) or (1,m/2), chosen by f at the receiver phase. After j natural repetitions, the receiver gains (0,j), the first labelled sender loses (0,j), and all other coordinates stay fixed. The trace of horizon n records the observations at every time from zero through n. The recovery function takes two snapshots and their known times. Its arithmetic companion returns the same coordinate construction together with a specified group-operation and comparison ledger.

Forward and backward first-change distances use the least positive index at which f differs from its initial value, with zero reserved for absence of a change. A run start has f(s-1) different from f(s), and a run position is a start paired with an index below its forward distance. Constant windows include both endpoints. Their phase count and the quotient count of sources with equal complete traces are definitions on the actual source and phase spaces.

These definitions do not assert recovery, the validity of the operation ledger, fiber sizes or first-change bounds. The theorem in `D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorRecovery` proves those conclusions under its stated hypotheses, including even m at least two and r at least three. Distances and constant windows remain defined when f is constant; no positive first-change boundary is postulated in that case.

## References

- Dependency: [D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality](../PredictionCertificates/LocalCertificateMinimality.md)
- Dependency: [D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence](../RefinementClosure/FiniteHorizonKernelRecurrence.md)
- Narrative reference: [D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorRecovery](CyclicSelectorRecovery.md)
