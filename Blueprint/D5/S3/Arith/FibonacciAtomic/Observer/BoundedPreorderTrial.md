# Bounded preorder trials

## Abstract

Certified increasing preorder trials recover bounded original traversals from stationary images.

Sources are all nonempty finite ordered full binary trees with Boolean leaves. True denotes alpha and false denotes beta. Substitution sends alpha to beta and beta to pair(beta,alpha), preserving pairs. An address is a Boolean list, with false for left and true for right. The source sizes and epochs range over arbitrary natural numbers; the bounds are symbolic and impose no fixed enumeration limit.

**Definition 1.1 (One virtual node report).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.Report`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.Report` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A report is a dependent pair of a finite address and its four-valued reply: alpha, beta, branch or absent.

**Definition 1.2 (Ordered virtual reports).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.History`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.History` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A history is a list of reports. Order and repeated entries are retained.

**Definition 1.3 (Branch count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.branches`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.branches` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

branches(s) counts exactly the entries of s whose reply is branch.

**Definition 1.4 (Beta count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.betas`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.betas` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

betas(s) counts exactly the entries of s whose reply is beta.

**Definition 1.5 (Leaf count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.leafVisits`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.leafVisits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

leafVisits(s) counts exactly the alpha and beta replies in s.

**Definition 1.6 (Leaf XOR).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.parity`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.parity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

parity(s) is betas(s) modulo two, with alpha contributing zero and beta contributing one.

**Definition 1.7 (Inclusive branch cutoff).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.cutLength`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.cutLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive threshold h, cutLength(h,s) is the position just after the h-th branch reply, or length(s) if there are fewer than h branches. The empty list gives zero. At a branch with h at most one the recursion returns one; otherwise it consumes the report and decreases h only for a branch. This also defines the function at h=0.

**Definition 1.8 (The bounded preorder).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.trial`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.trial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

trial(h,v) takes cutLength(h,acquisitionTrace([],v)) reports from acquisitionTrace([],v). The order is the existing left-first producer preorder. The cutoff branch itself is included; its descendants are excluded.

**Definition 1.9 (Completion before the cutoff).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.Completes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.Completes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Completes(h,v) means that the complete acquisition trace of v contains fewer than h branches. For the image predecessors in the theorem, this is equivalent to finishing a full tree with h leaves.

**Definition 1.10 (All stationary decoder calls).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.physicalQueries`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.physicalQueries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

physicalQueries(N,s) concatenates originalQueries(N,p) for every report at address p in s. A repeated literal remains a separate physical call, including coincident guard and value addresses.

**Definition 1.11 (The image predecessor).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.virtualSource`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.virtualSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

virtualSource(u,tau,N) is substitution iterated tau-N times on u, with natural subtraction. It is mathematical proof data. The theorem supplies N at most tau before using y as its N-fold image.

**Definition 1.12 (Licensed increments).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.Attempts`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.Attempts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Attempts(start,success,N) is generated by an initial attempt at start, and by passing from an attempted N to N+1 only when success(N) is false.

**Definition 1.13 (The complete per-trial contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.TrialSpec`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.TrialSpec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write v=virtualSource(u,tau,N) and s=trial(h,v). TrialSpec(h,tau,N,u,y) asserts y=substitution iterated N times on v; the epoch-zero tagged reports of s are a prefix of the paid Read projection of productionTrace([],v); and every strict position i in s has fewer than h branch replies in the first i reports of the complete preorder. The length of s is at most 2h-1. Every reached address has depth at most h-1 and a non-absent virtual reply.

The remaining TrialSpec fields state that originalDecode applied to the actual replies on stationary y returns each reached report, and that listController executes that query list from the empty local transcript with fuel length(originalQueries)+1, returning its actual listTrace and the report reply. Every nonroot guard accepts, and at even N the value read is non-absent. Each node uses at most two physical calls, their concatenation at most 4h-2, and every physical literal has length at most h-1+halfCeil(N).

On completion, s equals the complete preorder, v has h leaves, its trace has h leaf visits and h-1 branches and length 2h-1, and its leaf parity equals the beta count of u modulo two if h is even. At N=tau completion and original parity hold for every h. At N=0 the physical list is exactly the virtual address list. On rejection there are exactly h visited branches, the final report is a branch, and N is strictly below tau.

**Theorem 1.14 (First completion and all intervening trials).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.bounded_preorder_trial`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.bounded_preorder_trial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural h,tau,start and all sources u,y, assume length(u)=h, y=substitution iterated tau times on u, and start at most tau. Then every natural N at most tau satisfies TrialSpec(h,tau,N,u,y). Every N satisfying Attempts(start, k mapped to Completes(h,virtualSource(u,tau,k)), N) is at most tau. There exists a natural K with start at most K at most tau and Completes(h,virtualSource(u,tau,K)); every N from start up to but excluding K fails to complete. The number K-start+1 is at most tau-start+1, and for every T at least tau it is at most T+1. Finally, every N from start through K is both an attempted candidate and satisfies the complete TrialSpec. Thus K is the first completion and every decoder invocation has an actual image premise.

A proper preorder prefix of length i has i at most twice its branch count, while the next node's depth is at most the initial address depth plus that branch count. Structural induction splits the next position between the left and right subtrees; a completed left subtree contributes its exact full-tree counts. Applying these two prefix relations immediately before the inclusive cutoff gives both the node bound and the depth bound. Fullness and nondecreasing leaf count force exactly h leaves whenever the traversal completes. Original decoder correctness and its fixed-list execution theorem then give the stationary call and literal bounds.

For positive N and a nonroot p, the ordered decoder list is the parent of p followed by floor(N/2)+1 right edges, then p followed by halfCeil(N) right edges. At the root the guard is omitted. Even N uses the raw value; odd N maps absent to alpha, alpha to beta, and either beta or branch to branch. For N=0 the list is just p. The proved image trials exclude failed guards and even-offset absent values; an odd-offset raw absent is a valid alpha. The list decoder itself is total and returns an absent default on malformed or rejected inputs.

With start=0 and tau at most T, at most T+1 trials suffice. When T=0, tau=K=0 and there is one direct traversal with original parity for every h, including h=1. Earlier completion at positive offset needs the even-h condition for original parity; it does not identify the historical epoch.

trial and Completes are source-indexed mathematical specifications. The theorem proves physical fixed-list execution for each reached node and counts the concatenated lists. Constructing a source-blind reduced trial controller, a nonhalting error state outside the proved image domain, and a one-bit native realization requires separate operational results. Full-source production supplies the virtual Read order; its acquired subtrees and workspace are not assigned to this trial. The call bounds precede word-routing expansion.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.Attempts`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.Completes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.History`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.Report`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.TrialSpec`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.betas`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.bounded_preorder_trial`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.branches`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.cutLength`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.leafVisits`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.parity`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.physicalQueries`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.trial`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial.virtualSource`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout](DelayedOriginalReadout.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer](NativeFullSourceProducer.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap](../SourceCoordinates/NativeRotationDepthGap.md)
