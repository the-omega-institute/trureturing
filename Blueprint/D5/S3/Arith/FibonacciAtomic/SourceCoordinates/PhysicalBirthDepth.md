# Physical Births and Observable Orientations

## Abstract

Complete depths recover physical branch orientations above the terminal two-child boundary.

The physical ports persist: false is a and true is b. A label true is alpha, and false is beta. Descriptor(born,initial) stores immutable creation data. Birth(time,index,bit) stores the branch update, positive global birth index and actual stream bit. In the formulas snapshot(z,n) means (orbit z n).1; source forgets metadata but retains physical child order and current terminal labels. born and initial project a descriptor; bit, time and index project a birth. shape(U) means decompose(U).1. select(c,A,B) returns A for true and B for false. apply(z,j) is the stream value z(j), and negate is Boolean negation. Natural subtraction is truncated. No descriptor, rank or prefix is an extra observer readout.

**Definition 1.1 (Immutable creation descriptor).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.Descriptor`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.Descriptor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

born is the creation update, and initial is the label at creation, retained even after an alpha leaf becomes beta.

**Definition 1.2 (Actual branch event).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.Birth`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.Birth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

time is the update when an old beta branches; index is its global one-based event index and bit is the consumed stream value.

**Definition 1.3 (Physical finite tree).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.Physical`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.Physical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A leaf stores its descriptor and current label. A branch stores its original descriptor, its birth event and its ordered a and b children.

**Definition 1.4 (Persistent root metadata).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.descriptor`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.descriptor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both constructors expose the original descriptor of this same physical node.

**Definition 1.5 (Existing ordered source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.source`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.source` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A physical leaf becomes the existing Source.of of its current label. A branch becomes Source.mul of its a and b children in that order.

**Definition 1.6 (Simultaneous old-leaf update).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.update`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.update` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recursion visits only the input tree. Old alpha becomes beta without consuming a bit. Old beta consumes z(j+1), increments the counter and creates beta at a exactly when that bit is true. Both new descriptors have born=time and their actual initial labels. Newborns are returned without further recursion. Old branches and their metadata persist. Their a subtree is updated first, then b with the returned counter, so beta events follow physical lexicographic order.

**Definition 1.7 (Alpha-origin physical orbit).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.orbit`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.orbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At cut zero the tree is a single alpha with descriptor (0,true) and counter zero. Cut n+1 applies update z (n+1) to the complete previous tree and its global counter. This quantifies every stream, with no law on z.

**Definition 1.8 (Literal reached cone).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.at`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.at` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Lookup follows the original physical Boolean address; the empty address returns the whole tree and a nonempty suffix crossing a leaf returns none. The returned subtree keeps every descriptor and branch event.

**Definition 1.9 (Descriptor rank).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.rank`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.rank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rank(n,T)=n-born(descriptor(T))+indicator(initial(T)=false). The theorem derives this rank from the actual old-leaf orbit, rather than assuming a desired chronology or identifying physical order with a fixed semantic substitution.

**Definition 1.10 (Complete-function maximum).**

$$\forall T: Source, (\forall L: Nat, (\forall m: Nat, ((\operatorname{DepthMaximum}\left(T, L, m\right)) \iff ((\forall u: Address, ((\operatorname{length}\left(u\right) = L) \implies (\operatorname{depth}\left(T, u\right) \leq m))) \land \\(\exists u: Address, ((\operatorname{length}\left(u\right) = L) \land \\(\operatorname{depth}\left(T, u\right) = m)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.DepthMaximum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A bound on the entire tape cube and an attained value at that same horizon. No descriptors or labels are arguments of the observed tape function.

**Definition 1.11 (Depth-only comparison).**

$$\forall A: Source, (\forall B: Source, (\forall L: Nat, ((\operatorname{Beats}\left(A, B, L\right)) \iff (\exists u: Address, ((\operatorname{length}\left(u\right) = L) \land \\(\forall v: Address, ((\operatorname{length}\left(v\right) = L) \implies (\operatorname{depth}\left(B, v\right) < \operatorname{depth}\left(A, u\right)))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.Beats` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is one left tape whose depth exceeds every right-tape depth. At a sufficient horizon this compares the two attained maxima using depth only.

**Definition 1.12 (Full-root depth comparison).**

$$\forall T: Source, (\forall p: Address, (\forall L: Nat, ((\operatorname{RootBeats}\left(T, p, L\right)) \iff (\exists u: Address, ((\operatorname{length}\left(u\right) = L) \land \\(\forall v: Address, ((\operatorname{length}\left(v\right) = L) \implies (\operatorname{depth}\left(T, \operatorname{append}\left(p, \operatorname{cons}\left(true, v\right)\right)\right) < \operatorname{depth}\left(T, \operatorname{append}\left(p, \operatorname{cons}\left(false, u\right)\right)\right)))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.RootBeats` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This comparison uses only values of the same full-root depth function on tapes with the fixed physical prefix p followed by a or b. cons(c,u) prepends the direction c; append retains the complete root literal.

**Definition 1.13 (Whole reached-cone law).**

$$\forall n: Nat, (\forall z: Nat \to Bool, (\forall p: Address, (\forall T: Physical, ((\operatorname{ConeLaw}\left(n, z, p, T\right)) \iff ((\operatorname{born}\left(\operatorname{descriptor}\left(T\right)\right) \leq n) \land \\(\operatorname{rank}\left(n, T\right) + \operatorname{length}\left(p\right) \leq n) \land \\(\operatorname{height}\left(\operatorname{source}\left(T\right)\right) = \operatorname{rank}\left(n, T\right) - 1) \land \\((\operatorname{rank}\left(n, T\right) \leq 1) \iff (\exists d: Descriptor, (\exists c: Bool, (T = \operatorname{leaf}\left(d, c\right))))) \land \\(\forall u: Address, (\operatorname{depth}\left(\operatorname{source}\left(T\right), u\right) \leq \operatorname{rank}\left(n, T\right) - 1)) \land \\(\forall L: Nat, ((\operatorname{rank}\left(n, T\right) - 1 \leq L) \implies (\operatorname{DepthMaximum}\left(\operatorname{source}\left(T\right), L, \operatorname{rank}\left(n, T\right) - 1\right)))) \land \\(\forall u: Address, ((\operatorname{rank}\left(n, T\right) - 1 \leq \operatorname{length}\left(u\right)) \implies ((\operatorname{PaidWalk}\left(\operatorname{source}\left(\operatorname{snapshot}\left(z, n\right)\right), p, u, \operatorname{probes}\left(\operatorname{source}\left(T\right), p, u\right), \operatorname{depth}\left(\operatorname{source}\left(T\right), u\right)\right)) \land \\(\operatorname{length}\left(\operatorname{probes}\left(\operatorname{source}\left(T\right), p, u\right)\right) = \operatorname{depth}\left(\operatorname{source}\left(T\right), u\right) + 1) \land \\(\operatorname{Run}\left(controller, \operatorname{walk}\left(p, u, 0\right), n, \operatorname{source}\left(\operatorname{snapshot}\left(z, n\right)\right), \operatorname{eventTrace}\left(n, \operatorname{source}\left(\operatorname{snapshot}\left(z, n\right)\right), \operatorname{probes}\left(\operatorname{source}\left(T\right), p, u\right)\right), \operatorname{depth}\left(\operatorname{source}\left(T\right), u\right)\right))))) \land \\(\forall u: Address, (\forall v: Address, ((\operatorname{rank}\left(n, T\right) - 1 \leq \operatorname{length}\left(u\right)) \implies (\operatorname{depth}\left(\operatorname{source}\left(T\right), \operatorname{append}\left(u, v\right)\right) = \operatorname{depth}\left(\operatorname{source}\left(T\right), u\right))))) \land \\(\forall L: Nat, ((n - 1 \leq L) \implies (\operatorname{rank}\left(n, T\right) - 1 \leq L - \operatorname{length}\left(p\right)))) \land \\(\forall u: Address, (\operatorname{depth}\left(\operatorname{source}\left(\operatorname{snapshot}\left(z, n\right)\right), \operatorname{append}\left(p, u\right)\right) = \operatorname{length}\left(p\right) + \operatorname{depth}\left(\operatorname{source}\left(T\right), u\right))) \land \\(\forall u: Address, (\forall v: Address, ((2 \leq n) \implies ((\operatorname{length}\left(u\right) = 2 \times n - 1 - \operatorname{length}\left(p\right)) \implies ((\operatorname{length}\left(v\right) = \operatorname{length}\left(p\right)) \implies ((\operatorname{depth}\left(\operatorname{source}\left(\operatorname{snapshot}\left(z, n\right)\right), \operatorname{append}\left(p, u\right)\right) = \operatorname{length}\left(p\right) + \operatorname{depth}\left(\operatorname{source}\left(T\right), u\right)) \land \\(\operatorname{length}\left(p\right) + \operatorname{depth}\left(\operatorname{source}\left(T\right), u\right) = \operatorname{length}\left(p\right) + \operatorname{depth}\left(\operatorname{source}\left(T\right), \operatorname{append}\left(u, v\right)\right)))))))) \land \\(\forall A: Source, (\forall L: Nat, ((\operatorname{rank}\left(n, T\right) - 1 \leq L) \implies ((\operatorname{height}\left(A\right) \leq L) \implies ((\forall u: Address, ((\operatorname{length}\left(u\right) = L) \implies (\operatorname{depth}\left(\operatorname{source}\left(\operatorname{snapshot}\left(z, n\right)\right), \operatorname{append}\left(p, u\right)\right) = \operatorname{length}\left(p\right) + \operatorname{depth}\left(A, u\right)))) \implies (\operatorname{shape}\left(\operatorname{source}\left(T\right)\right) = \operatorname{shape}\left(A\right))))))) \land \\(\forall d: Descriptor, (\forall e: Birth, (\forall A: Physical, (\forall B: Physical, ((T = \operatorname{branch}\left(d, e, A, B\right)) \implies ((2 \leq \operatorname{rank}\left(n, T\right)) \land \\(\operatorname{time}\left(e\right) = \operatorname{born}\left(d\right) + \operatorname{select}\left(\operatorname{initial}\left(d\right), 2, 1\right)) \land \\(\operatorname{time}\left(e\right) \leq n) \land \\(0 < \operatorname{index}\left(e\right)) \land \\(\operatorname{bit}\left(e\right) = \operatorname{apply}\left(z, \operatorname{index}\left(e\right)\right)) \land \\(\operatorname{born}\left(\operatorname{descriptor}\left(A\right)\right) = \operatorname{time}\left(e\right)) \land \\(\operatorname{born}\left(\operatorname{descriptor}\left(B\right)\right) = \operatorname{time}\left(e\right)) \land \\(\operatorname{initial}\left(\operatorname{descriptor}\left(A\right)\right) = \operatorname{negate}\left(\operatorname{bit}\left(e\right)\right)) \land \\(\operatorname{initial}\left(\operatorname{descriptor}\left(B\right)\right) = \operatorname{bit}\left(e\right)) \land \\(\operatorname{select}\left(\operatorname{bit}\left(e\right), \operatorname{rank}\left(n, A\right), \operatorname{rank}\left(n, B\right)\right) = \operatorname{rank}\left(n, T\right) - 1) \land \\(\operatorname{select}\left(\operatorname{bit}\left(e\right), \operatorname{rank}\left(n, B\right), \operatorname{rank}\left(n, A\right)\right) = \operatorname{rank}\left(n, T\right) - 2) \land \\(\operatorname{select}\left(\operatorname{bit}\left(e\right), \operatorname{height}\left(\operatorname{source}\left(A\right)\right), \operatorname{height}\left(\operatorname{source}\left(B\right)\right)\right) = \operatorname{rank}\left(n, T\right) - 2) \land \\(\operatorname{select}\left(\operatorname{bit}\left(e\right), \operatorname{height}\left(\operatorname{source}\left(B\right)\right), \operatorname{height}\left(\operatorname{source}\left(A\right)\right)\right) = \operatorname{rank}\left(n, T\right) - 3) \land \\(\forall L: Nat, ((\operatorname{rank}\left(n, T\right) - 2 \leq L) \implies ((\operatorname{DepthMaximum}\left(\operatorname{select}\left(\operatorname{bit}\left(e\right), \operatorname{source}\left(A\right), \operatorname{source}\left(B\right)\right), L, \operatorname{rank}\left(n, T\right) - 2\right)) \land \\(\operatorname{DepthMaximum}\left(\operatorname{select}\left(\operatorname{bit}\left(e\right), \operatorname{source}\left(B\right), \operatorname{source}\left(A\right)\right), L, \operatorname{rank}\left(n, T\right) - 3\right)) \land \\((3 \leq \operatorname{rank}\left(n, T\right)) \implies ((\operatorname{bit}\left(e\right) = true) \iff (\operatorname{Beats}\left(\operatorname{source}\left(A\right), \operatorname{source}\left(B\right), L\right))))))) \land \\((3 \leq \operatorname{rank}\left(n, T\right)) \implies ((\operatorname{rank}\left(n, T\right) - 2 \leq 2 \times n - 1 - \operatorname{length}\left(p\right) - 1) \land \\(\operatorname{length}\left(p\right) + 1 + 2 \times n - 1 - \operatorname{length}\left(p\right) - 1 = 2 \times n - 1) \land \\((\operatorname{bit}\left(e\right) = true) \iff (\operatorname{RootBeats}\left(\operatorname{source}\left(\operatorname{snapshot}\left(z, n\right)\right), p, 2 \times n - 1 - \operatorname{length}\left(p\right) - 1\right))))) \land \\((\operatorname{rank}\left(n, T\right) = 3) \implies ((\operatorname{select}\left(\operatorname{bit}\left(e\right), \operatorname{height}\left(\operatorname{source}\left(A\right)\right), \operatorname{height}\left(\operatorname{source}\left(B\right)\right)\right) = 1) \land \\(\operatorname{select}\left(\operatorname{bit}\left(e\right), \operatorname{height}\left(\operatorname{source}\left(B\right)\right), \operatorname{height}\left(\operatorname{source}\left(A\right)\right)\right) = 0))) \land \\((\operatorname{rank}\left(n, T\right) = 2) \implies ((\operatorname{source}\left(A\right) = \operatorname{of}\left(\operatorname{negate}\left(\operatorname{bit}\left(e\right)\right)\right)) \land \\(\operatorname{source}\left(B\right) = \operatorname{of}\left(\operatorname{bit}\left(e\right)\right)) \land \\(\forall u: Address, ((u \neq \operatorname{nil}\left(\right)) \implies (\operatorname{depth}\left(\operatorname{source}\left(T\right), u\right) = 1))) \land \\(\forall u: Address, (\operatorname{depth}\left(\operatorname{source}\left(T\right), u\right) = \operatorname{depth}\left(\operatorname{mul}\left(\operatorname{source}\left(B\right), \operatorname{source}\left(A\right)\right), u\right))))))))))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.ConeLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed law includes every horizon, padding word, reached prefix and branch. Its q is the displayed descriptor-rank abbreviation. The root-offset clause uses H=2n-1 for every n at least two; a tape u has length H-|p| and v has length |p|, hence both root and padded local tapes have length H. The unrestricted prefix identity also gives the local restriction by subtracting |p|.

At every sufficient local horizon the paid derivation uses the same full root and all operands are absolute literals. Its number of tests is depth+1, including the final absence test with an empty remaining direction list. Run is the existing native serial Run of the source-blind tape controller; its eventTrace consists exactly of these stationary full-root Read events. Using this mathematical presence service requires the original binding, grants, backing, completed serial reads and stationarity premises.

The comparison source U is any finite ordered labelled tree with the same sufficient tape horizon. Equality of complete depths identifies its ordered unlabelled terminal/branch shape. Labels themselves are not recovered. At rank three the ordered high/low maxima are one and zero; at rank two both children are terminal, every nonempty local tape has depth one and exchanging the two terminal labels preserves every depth. This last statement concerns depth observations only and asserts no equivalence of future observations.

**Theorem 1.14 (Observable physical orientations).**

$$\forall n: Nat, (\forall z: Nat \to Bool, ((\operatorname{descriptor}\left(\operatorname{snapshot}\left(z, n\right)\right) = \operatorname{Descriptor}\left(0, true\right)) \land \\(\operatorname{rank}\left(n, \operatorname{snapshot}\left(z, n\right)\right) = n) \land \\(\forall p: Address, (\forall T: Physical, ((\operatorname{at}\left(p, \operatorname{snapshot}\left(z, n\right)\right) = \operatorname{some}\left(T\right)) \implies (\operatorname{ConeLaw}\left(n, z, p, T\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.observable_orientations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A ranked tree is constructed alongside the actual alpha-origin orbit. The construction threads the same global counter in physical a-before-b order; its erasure is proved equal to the original update. Its invariant retains immutable creation times, initial labels and the actual z(index) birth bit. Induction gives ranks n-born+indicator(initial beta), physical child ranks q-1,q-2 and height q-1 with truncated subtraction. Reached-prefix induction pays the remaining-horizon margin at every physical address.

The complete tape geometry theorem supplies paid walks, padding, attained maxima and prefix offsets. Its label-erased frontier argument uses the existing source_foundation rigidity theorem to recover ordered shape. The derived physical child heights then compare attained maxima and recover the actual stored stream bit for every rank at least three. No reconstruction, child margin or chronology appears as an extra hypothesis.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.Beats`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.Birth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.ConeLaw`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.DepthMaximum`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.Descriptor`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.Physical`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.RootBeats`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.at`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.descriptor`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.observable_orientations`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.orbit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.rank`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.source`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalBirthDepth.update`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate](../ActualImageAddressCertificate.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth](PhysicalTapeDepth.md)
