# Native Full Root Feasibility

## Abstract

Complete predecessor-row feasibility on every actual origin equals finite root-experiment feasibility with the same payload capacity and fresh-call budget.

Sources are arbitrary finite ordered Boolean trees. The substitution rho is the original alpha-to-beta and beta-to-pair(beta,alpha) map. P is any finite prefix-free cut. Choose one reference origin u0 solely to specify the fixed nonempty current row C=canonicalRow(P,rho(u0)); every nonempty actual current-row fiber admits such a reference. ImageValues(C), OriginFiber(P,C), appearing class names and Chart(C) are the exact full-fiber objects from NativeClassRootImage and NativeClassRootSimulation. Values and origins are coerced to their underlying values in the formulas. Filled(C,v) abbreviates evaluateRow(extend(C,v),C). A type is some(true), some(false), or none for alpha, beta, or branch. Classes are the occurring-label subtype, without a consecutive-label assumption. EmptyAddress denotes the empty address. FourReplyContinuation(A,B,E,D) sends alpha, beta, branch and absent to A, B, E and D respectively. In the theorem formula, let C binds the displayed fixed row.

**Definition 1.1 (Stationary Actual Traces).**

$$\forall t: Trace, ((\operatorname{Stationary}\left(t\right)) \iff (\forall n: Nat, (\neg (\operatorname{member}\left(\operatorname{update}\left(n\right), t\right)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.Stationary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Stationarity excludes update events on actual terminating traces. The arbitrary control type, interpreter and all unreachable continuations remain unrestricted. Local steps may be arbitrarily numerous but finite on each reached run.

**Definition 1.2 (Visible Alpha Roots).**

$$\forall C: LiteralRow, (\forall theta: (\operatorname{Classes}\left(C\right)) \to (\operatorname{Option}\left(Bool\right)), (\forall a: Address, ((\operatorname{VisibleAlpha}\left(C, theta, a\right)) \iff (\exists e: LiteralRow, ((\operatorname{rowAt}\left(a, C\right) = \operatorname{some}\left(e\right)) \land (\operatorname{lit}\left(\operatorname{typeExtend}\left(C, theta\right), true, e\right)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.VisibleAlpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only a concrete alpha or a class with alpha root is a literal alpha. Ordered pairs are excluded. At a sibling of a reached cut, prefix freedom ensures this visible-root predicate agrees exactly with the actual current subtree being alpha.

**Definition 1.3 (Occurrence-Sensitive Old Support).**

$$\forall C: LiteralRow, (\forall theta: (\operatorname{Classes}\left(C\right)) \to (\operatorname{Option}\left(Bool\right)), (\operatorname{oldMask}\left(C, theta\right) = \{p: Address \Vert (\operatorname{member}\left(p, \operatorname{holeAddresses}\left(emptyAddress, C\right)\right)) \land (\neg (\exists a: Address, (\exists d: Bool, ((p = \operatorname{append}\left(a, \operatorname{singleton}\left(d\right)\right)) \land (\operatorname{VisibleAlpha}\left(C, theta, \operatorname{append}\left(a, \operatorname{singleton}\left(true\right)\right)\right))))))\}))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.oldMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mask retains exactly those reached current occurrences that are not children of a parent with an alpha right child. A root cut has no final edge and is retained. Membership is tested per occurrence, so an old occurrence and a newborn occurrence may share one current equality class without either status being lost.

**Definition 1.4 (Whole Predecessor Target).**

$$\forall C: LiteralRow, (\forall theta: (\operatorname{Classes}\left(C\right)) \to (\operatorname{Option}\left(Bool\right)), (\operatorname{target}\left(C, theta\right) = \operatorname{getD}\left(\operatorname{back}\left(C, \operatorname{oldMask}\left(C, theta\right)\right), \operatorname{of}\left(\operatorname{inl}\left(true\right)\right)\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.target` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Back is the existing occurrence repair and opaque image parser. The target uses its decoded LiteralRow, with an alpha-row fallback. Every admissible type has a successful decoding, so the fallback never contributes on the task domain. The output retains all canonical restricted classes, equalities, disequalities, exterior constructors and predecessor absence guards.

**Definition 1.5 (Full Actual Stationary Reader Feasibility).**

$$\forall P: CutSet, (\forall C: LiteralRow, (\forall r, q: Nat, ((\operatorname{InvFeas}\left(P, C, r, q\right)) \iff (\exists S, K: Type, (\exists sigma: (\operatorname{ImageValues}\left(C\right)) \to (S), (\exists entry: (S) \to (K), (\exists delta: (K) \to (\operatorname{Op}\left(K, LiteralRow\right)), ((\operatorname{Finite}\left(\operatorname{range}\left(sigma\right)\right)) \land (\operatorname{ncard}\left(\operatorname{range}\left(sigma\right)\right) \leq r) \land (\forall v: \operatorname{ImageValues}\left(C\right), (\forall u: \operatorname{OriginFiber}\left(P, C\right), ((\operatorname{rho}\left(u\right) = \operatorname{evaluateRow}\left(\operatorname{extend}\left(C, v\right), C\right)) \implies (\exists t: Trace, ((\operatorname{Run}\left(delta, \operatorname{entry}\left(\operatorname{sigma}\left(v\right)\right), 0, \operatorname{rho}\left(u\right), t, \operatorname{canonicalRow}\left(P, u\right)\right)) \land (\operatorname{Stationary}\left(t\right)) \land (\operatorname{length}\left(\operatorname{answers}\left(t\right)\right) \leq q))))))))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.InvFeas` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ambient complete payload type S and control type K may be infinite. Sigma may depend on all acquired class values. Its actual complete range is explicitly finite and has cardinal at most r; a bare natural cardinal bound would admit infinite ranges and is not this definition. Entry is a function of the complete payload, with fixed common data already installed; it has no extra source-dependent argument. The same actual register rho(u) is used throughout each NativeSerialMachine.Run. Every actual origin and matching image valuation must terminate with the entire canonical predecessor row, with at most q read events. Repeated and absent queries count, local steps do not. Unreachable divergent behavior is permitted. Acquisition, authenticated continuity, complete export, lawful common entry and stationary access are supplied paid premises; this mathematical contract grants none of them.

**Definition 1.6 (Finite Joint Root Experiment Feasibility).**

$$\forall C: LiteralRow, (\forall r, q: Nat, ((\operatorname{RootFeas}\left(C, r, q\right)) \iff (\exists S: Type, ([\operatorname{Fintype}\left(S\right)], \exists c: (\operatorname{Chart}\left(C\right)) \to (S), (\exists E: (S) \to (\operatorname{RootTree}\left(C, LiteralRow\right)), ((1 \leq \operatorname{card}\left(S\right)) \land (\operatorname{card}\left(S\right) \leq r) \land (\forall theta: \operatorname{Chart}\left(C\right), ((\operatorname{fst}\left(\operatorname{rootRun}\left(theta, \operatorname{E}\left(\operatorname{c}\left(theta\right)\right)\right)\right) = \operatorname{target}\left(C, theta\right)) \land (\operatorname{rootDepth}\left(\operatorname{E}\left(\operatorname{c}\left(theta\right)\right)\right) \leq q)))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.RootFeas` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is an inhabited finite alphabet S with at most r installed labels, a coloring of the exact admissible chart, and a finite three-reply experiment tree for each label. Every used tree has installed depth at most q and returns the whole target on all its colored types. Unused labels need no depth condition. Early halts and arbitrary impossible-edge outputs are allowed. At zero classes the tree type permits only stops.

**Definition 1.7 (Actual Representative-Address Installation).**

$$\forall C: LiteralRow, (\forall fallback: LiteralRow, ((\forall o: LiteralRow, (\operatorname{install}\left(C, fallback, \operatorname{stop}\left(o\right)\right) = \operatorname{stop}\left(o\right))) \land (\forall d: \operatorname{Classes}\left(C\right), (\forall A, B, E: \operatorname{RootTree}\left(C, LiteralRow\right), (\operatorname{install}\left(C, fallback, \operatorname{ask}\left(d, A, B, E\right)\right) = \operatorname{read}\left(\operatorname{representative}\left(C, d\right), \operatorname{install}\left(C, fallback, A\right), \operatorname{install}\left(C, fallback, B\right), \operatorname{install}\left(C, fallback, E\right), \operatorname{stop}\left(fallback\right)\right))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.install` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each query asks the original row-determined representative from NativeWholeRowPlan. The existing representative_subtree theorem proves that this address reaches its class value for every valuation, without an image or finite-source restriction. Its native reply is the class root. The absent edge immediately halts with common fallback data and is unreachable on every actual filling. Installation preserves the pair consisting of output and actual invocation count, and its native depth equals the root-tree depth.

**Definition 1.8 (Common Native Dialogue Controller).**

$$(\forall o: LiteralRow, (\operatorname{controller}\left(\operatorname{stop}\left(o\right)\right) = \operatorname{stop}\left(o\right))) \land (\forall a: Address, (\forall A, B, E, D: \operatorname{Dialogue}\left(LiteralRow\right), (\operatorname{controller}\left(\operatorname{read}\left(a, A, B, E, D\right)\right) = \operatorname{read}\left(a, \operatorname{fourReplyContinuation}\left(A, B, E, D\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.controller` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete accessible entry is the installed dialogue selected by the exported code. Stop returns its complete row. Read asks the stored address and continues according to the actual one of four replies. This deterministic controller performs no update.

**Theorem 1.9 (Complete Same-Capacity, Same-Budget Equivalence).**

$$\forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies (\forall u0: Source, (\forall r, q: Nat, ((1 \leq r) \implies (\operatorname{let} C = \operatorname{canonicalRow}\left(P, \operatorname{rho}\left(u0\right)\right), (\forall v: \operatorname{ImageValues}\left(C\right), (\forall u: \operatorname{OriginFiber}\left(P, C\right), ((\operatorname{rho}\left(u\right) = \operatorname{evaluateRow}\left(\operatorname{extend}\left(C, v\right), C\right)) \implies ((\operatorname{oldMask}\left(C, \operatorname{types}\left(C, v\right)\right) = \operatorname{H}\left(P, u\right)) \land (\operatorname{back}\left(C, \operatorname{oldMask}\left(C, \operatorname{types}\left(C, v\right)\right)\right) = \operatorname{some}\left(\operatorname{canonicalRow}\left(P, u\right)\right)) \land (\operatorname{target}\left(C, \operatorname{types}\left(C, v\right)\right) = \operatorname{canonicalRow}\left(P, u\right)))))) \land (\forall theta: \operatorname{Chart}\left(C\right), (\exists row: LiteralRow, (\operatorname{back}\left(C, \operatorname{oldMask}\left(C, theta\right)\right) = \operatorname{some}\left(row\right)))) \land (\forall v: \operatorname{ImageValues}\left(C\right), (\forall d: \operatorname{Classes}\left(C\right), ((\operatorname{subtree}\left(\operatorname{representative}\left(C, d\right), \operatorname{evaluateRow}\left(\operatorname{extend}\left(C, v\right), C\right)\right) = \operatorname{some}\left(\operatorname{v}\left(d\right)\right)) \land (\operatorname{readout}\left(\operatorname{representative}\left(C, d\right), \operatorname{evaluateRow}\left(\operatorname{extend}\left(C, v\right), C\right)\right) = \operatorname{rootReply}\left(\operatorname{types}\left(C, v, d\right)\right))))) \land ((\operatorname{InvFeas}\left(P, C, r, q\right)) \iff (\operatorname{RootFeas}\left(C, r, q\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.native_full_root_feasibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement contains the entire occurrence mask, successful whole-row factorization, successful decoding on every admissible type, actual representative subtree and reply laws, and the full joint-existence equivalence. For necessity, source-free finite replay to the next boundary supplies each reached local segment. Replay uniqueness makes its boundary independent of the witnessing source. A proof-only boundary selector uses an arbitrary common halt where no finite replay exists. Bounded recursive unrolling inspects Stop even at depth zero; induction on the original actual Run preserves its whole output and counted reads. A separate induction bounds every installed reply path by q, including unreachable paths. The actual used payload values form a finite subtype even if S is infinite. The existing truthful_joint_root_simulation takes the maximum query-word length of these finite dialogues, applies simultaneous actual padding, and compiles each constant or single-class reply. Its coloring uses the truthful full-value-dependent supplement of one fixed padded origin throughout that run. Whole-row factorization converts its predecessor output into the common type target. No supplement constancy on a root-type cell is assumed. For sufficiency, locally inspect the already acquired class roots and export the coloring. Exact chart attainment makes the actual export range equal to the used coloring range. Native installation invokes representatives on every actual source and preserves the counted path and installed depth. Whole-row decoding supplies the required predecessor output. Thus both directions use the same r and q. Empty, root and already-blocked cuts, zero classes and zero calls are included. The equivalence can change encoders within joint existence; it does not preserve an arbitrary fixed encoder. It is an existence proof from promised source-total termination, not extraction from program text. It imposes no source-size, finite-address, uniform-local-runtime, global-termination or total-controller-state bound, and establishes no full-trace or physical acquisition/export/isolation correspondence.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.InvFeas`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.RootFeas`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.Stationary`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.VisibleAlpha`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.controller`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.install`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.native_full_root_feasibility`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.oldMask`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullRootFeasibility.target`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootSimulation](NativeClassRootSimulation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber](NativeSharpPredecessorFiber.md)
