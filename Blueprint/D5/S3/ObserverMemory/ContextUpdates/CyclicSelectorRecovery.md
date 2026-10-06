# Cyclic Selector Recovery

## Abstract

Cyclic selector boundaries give exact run positions and recover original group sources.

**Theorem 1.1 (Actual cyclic runs and labelled source recovery).**

Lean statement: `D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorRecovery.cyclic_selector_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorRecovery.cyclic_selector_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m be even and at least two, r at least three, and f a fixed function from ZMod m to ZMod 2. Put G = ZMod 2 times ZMod m. A source contains a receiver a, r-1 labelled sender coordinates x_i, and a kernel offset h=(0,h_z). Its clock is t=a+sum_i x_i+h. The two selectors are tau_0=(1,0) and tau_1=(1,m/2). A sender replies with p_c(x)=x-chi(x)c, where chi is the binary first coordinate. The complete snapshot records a, t and every labelled reply.

The run geometry, labelled recovery, exact trace fibers and snapshot realization are supplied by `D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorModel.cyclic_selector_source_geometry`. The cardinality argument constructs a surjective trace-class label on the original sources and proves its exact kernel before counting those classes.

Every proposed snapshot (a,t,(u_i)) with replies u_i in H is realized by choosing binary bits with sum chi(t)-chi(a), setting x_i=u_i+epsilon_i c, and setting h=t-a-sum_i x_i. The parity equation puts h in H. Conversely every source producing that snapshot has exactly these bits and coordinates. This direct construction includes two senders. The statement describes every actual preimage without assuming source recovery from a single snapshot.

At time j the receiver has translation (0,j), sender 2 has translation -(0,j), and the other senders and h are unchanged. The clock remains fixed. A trace of horizon n retains all snapshots at times zero through n. For two fixed sources with the same initial snapshot, their traces agree exactly when the sources are equal or f is constant on that entire phase window. A later return of the selector cannot remove an earlier trace difference.

For nonconstant f, delta(z) is the least positive forward distance to a different label and beta(z) the corresponding backward distance. Actual run starts satisfy f(s-1) different from f(s). Every phase z has the unique start s=z-(beta(z)-1) and position k=beta(z)-1. Conversely a start and a position k less than delta(s) give the phase s+k. These inverse maps use cyclic addition throughout, including across phase zero. At that position delta(s+k)=delta(s)-k, with every delta between one and m-1.

For nonconstant f and every nonnegative horizon n, the number of phases whose labels stay constant through times zero to n is the sum over actual starts s of max(delta(s)-n,0). The longest actual run has length L between one and m-1. Every phase has delta at most L, every depth from one through L is attained, and no constant window remains exactly when n is at least L. Length-one runs and the two-phase circle are included.

Every actual snapshot fiber has q=2^(r-2) sources. At each fixed receiver phase there are C=4*m^r actual H-valued snapshots. A source-derived trace-class label retains its snapshot and, exactly when the selector window changes, its parity bitstring. The proved surjection and kernel identity give N_n=C*(q*m-(q-1)*A_n), where A_n counts constant windows. Thus N_0=4*m^(r+1) and the original source has 2^r*m^(r+1) elements. Ambient group-valued reply tuples are excluded from this image count.

Two supplied observations at known times p and q from one original source recover every original coordinate when their selectors differ. Add the known time translation to sender 2's replies at each endpoint, subtract the normalized replies, and compare with zero to read each sender's binary coordinate. Reconstruct that sender from its first normalized reply and selector, undo the receiver translation, then subtract the receiver plus reconstructed sender sum from the clock to obtain h. The identity returns the original source and assumes a common source for both endpoints. The concrete arithmetic schedule normalizes both replies for each sender, subtracts them, compares with zero, reconstructs the coordinate, and adds it to the sum. It counts exactly 5*(r-1)+3 group operations and 3*(r-1)+1 comparisons, bounded by 5*r and 3*r. Two time-residue conversions and one public f evaluation are separate primitives. This ledger supplies no bit-time, acquisition, communication, or physical-time bound.

At every phase, a source with zero senders and offset is distinct from the source obtained by flipping exactly senders 2 and 3 by the initial selector. They have the same initial snapshot, including when r=3. Their traces agree exactly on constant selector windows. On such a window the common snapshot at time j is computable from the initial snapshot by translating the receiver by (0,j) and sender 2's reply by -(0,j). For constant f this formula and the ambiguity persist at every time; no finite first-change boundary is assigned to the constant circle.

## References

- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorModel.cyclic_selector_source_geometry`
- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorRecovery.cyclic_selector_recovery`
- Dependency: [D5/S3/ObserverMemory/ContextUpdates/CyclicSelectorModel](CyclicSelectorModel.md)
- Dependency: [D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality](../PredictionCertificates/LocalCertificateMinimality.md)
- Dependency: [D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence](../RefinementClosure/FiniteHorizonKernelRecurrence.md)
