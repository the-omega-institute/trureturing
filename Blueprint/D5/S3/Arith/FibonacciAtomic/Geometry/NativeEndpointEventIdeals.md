# Native endpoint event ideals

## Abstract

Membership-defined native event ideals supply actual guarded execution adequacy.

Source is the unchanged Bool free magma, alpha is true and beta is false. Events consist of one split at each target branch and one promotion at each root or right-born position whose target subtree is not alpha. EventLe uses address prefix ancestry and promotion before split at one address. Ideal is supported lower closure. cutTerm is defined solely by membership: without a local split it is the initial or promoted leaf; after splitting it recursively combines the two child cuts. Created records strict ancestor creating splits. The original NativeGuardedLeafRepair.run, Call.shift, ActualLeafHistoryRigidity.subtree and ActualImageAddressCertificate.replace are retained. NativePostClockInverse supplies only its original address/kind/replacement/edited definitions; no clock inverse or serial-clock data is used.

Original Lean suppliers: `D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport` (Source); `D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity` (subtree); `D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate` (replace); `D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition` (D); `D5/S3/Arith/FibonacciAtomic/Geometry/NativeGuardedLeafRepair` (Call.shift, run, D_mul, run_preserves_D); `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativePostClockInverse` (address, kind, replacement, edited only); `D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity` (Enabled, Exec, ExtensionList, result).

Mathematical notation. Bool is {false,true}; Source is the free ordered binary-tree algebra on Bool, with leaf constructor of : Bool → Source and branch constructor mul : Source × Source → Source. Write alpha = of(true), beta = of(false). Address = List(Bool), [] is the empty address, and ++ is list concatenation. Call is the disjoint union of promote(p) and split(p), for p : Address. shift(c,p) prefixes p to the address of c, retaining its constructor. List(X) is the type of finite lists over X; Set(X) is its power set. some and none are the constructors of Option(X); ite(P,x,y) is x if proposition P holds (or Boolean P is true), and y otherwise. All quantifiers in the displays range over the indicated full types.

Native operations. subtree : Address × Source → Option(Source) follows false to the left child and true to the right child; the empty address returns the whole term, and descent across a leaf returns none. replace(t,p,v) replaces the subtree at p by v and leaves a crossed leaf unchanged. The address of promote(p) or split(p) is p; phase(promote(p)) = 0 and phase(split(p)) = 1. The relation c ≤ d means that address(c) is a prefix of address(d) and that equal addresses imply phase(c) ≤ phase(d); c < d means c ≤ d and not d ≤ c. Event(b,t) is the subtype of Calls in events(b,t), with this induced order; val forgets only the membership proof. erase(l) = l.map(val), retaining the order and every Call label.

Endpoint definitions. For b,a : Bool, events(b,of(a)) is {promote([])} exactly when b = true and a = false, and is empty otherwise. For b : Bool and l,r : Source, events(b,mul(l,r)) is the union of {split([])}, the conditional set ({promote([])} when b = true and empty otherwise), the shifts by [false] of events(false,l), and the shifts by [true] of events(true,r). For b,c : Bool and p : Address, birthAt(b,[]) = b and birthAt(b,c::p) = birthAt(c,p). For I : Set(Call) and p : Address, sectionAt(I,p) = {c : Call | shift(c,p) belongs to I}. Created(I,[]) is true, and Created(I,b::p) means split([]) belongs to I and Created(sectionAt(I,[b]),p).

Membership cuts. For b,a : Bool and I : Set(Call), cutTerm(b,of(a),I) is of(a) unless b = true and a = false; in that case it is beta if promote([]) belongs to I, and alpha otherwise. For b : Bool, l,r : Source and I : Set(Call), cutTerm(b,mul(l,r),I) is mul(cutTerm(false,l,sectionAt(I,[false])),cutTerm(true,r,sectionAt(I,[true]))) if split([]) belongs to I; otherwise it is beta when b = false or promote([]) belongs to I, and alpha otherwise. No execution or lower-set hypothesis enters these definitions.

Predicates and execution. D(t) means no left-child address in t is an alpha leaf: for every p : Address, the original readout(p++[false],t) does not return its alpha readout constructor. Born(b,t) means D(t) and (b = false implies t is not alpha). Ideal(b,t,I) means I is a subset of events(b,t) and, for all c in events(b,t) and d in I, c ≤ d implies c belongs to I. Guard(promote(p),u) means subtree(p,u) = some(alpha); Guard(split(p),u) means subtree(p,u) = some(beta). Enabled(b,t,I,e) means e is not in I and every d in events(b,t) with d < e belongs to I. edited(u,promote(p)) = replace(u,p,beta), and edited(u,split(p)) = replace(u,p,mul(beta,alpha)). run(u,[]) = some(u); run(u,e::w) = run(edited(u,e),w) if Guard(e,u), and none otherwise. insert(e,I) = I union {e}.

Finite-order notation. For b : Bool, t : Source and K : Set(Event(b,t)), raw(b,t,K) = {val(e) | e belongs to K}. IsLowerSet(K) means every event below a member of K also belongs to K. Exec(K,[],J) means K = J; Exec(K,e::l,J) means e is fresh, every strict predecessor of e is in K, and Exec(insert(e,K),l,J). ExtensionList(K,J,l) means l has no repetitions, its members are exactly J minus K, and for every earlier a and later b in l, not b ≤ a. These are the original EnabledPathSwapConnectivity predicates on Event(b,t). The symbol univ denotes the whole indicated Event type, including when it is empty. All occurrences of events as sets use the underlying set of the finite inventory.

**Theorem 1.1 (Creating root split precedence).**

$$\forall b: \operatorname{Bool}, (\forall c: \operatorname{Call}, (\operatorname{split}\left([]\right) < \operatorname{shift}\left(c, [b]\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.root_before` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The root split strictly precedes every call shifted into either child. This consumed order helper is used by lower-set enabling and the exact AA17.2 edge proof.

**Theorem 1.2 (Strict order under one child shift).**

$$\forall b: \operatorname{Bool}, (\forall c: \operatorname{Call}, (\forall d: \operatorname{Call}, ((\operatorname{shift}\left(c, [b]\right) < \operatorname{shift}\left(d, [b]\right)) \iff (c < d))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.shift_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Shifting two original calls into the same child preserves and reflects their strict prefix/phase comparison. This consumed normalization helper transports the causal edge proof and native enabling.

**Theorem 1.3 (No predecessor of the root promotion).**

$$\forall c: \operatorname{Call}, (\neg (c < \operatorname{promote}\left([]\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.lt_promote_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No original call strictly precedes the root promotion in the prefix/phase order. The helper supplies the root promotion case of enabling and exact causal closure.

**Theorem 1.4 (Only predecessor of the root split).**

$$\forall c: \operatorname{Call}, ((c < \operatorname{split}\left([]\right)) \iff (c = \operatorname{promote}\left([]\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.lt_split_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An original call strictly precedes the root split if and only if it is the root promotion. Endpoint support separately decides whether that promotion actually belongs to the finite event set.

**Theorem 1.5 (Predecessors of a shifted event).**

$$\forall b: \operatorname{Bool}, (\forall c: \operatorname{Call}, (\forall d: \operatorname{Call}, ((d < \operatorname{shift}\left(c, [b]\right)) \iff ((d = \operatorname{promote}\left([]\right)) \lor ((d = \operatorname{split}\left([]\right)) \lor (\exists f: \operatorname{Call}, ((d = \operatorname{shift}\left(f, [b]\right)) \land (f < c))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.lt_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every strict predecessor of a call shifted into child b is a root promotion, a root split, or the same child shift of a strict predecessor. Conversely each listed case strictly precedes that shifted event. Endpoint support and lower closure remove any absent root promotion in the native application.

**Theorem 1.6 (Event support under a child shift).**

$$\forall b: \operatorname{Bool}, (\forall c: \operatorname{Bool}, (\forall l: \operatorname{Source}, (\forall r: \operatorname{Source}, (\forall e: \operatorname{Call}, ((\operatorname{shift}\left(e, [c]\right) \in \operatorname{events}\left(b, \operatorname{mul}\left(l, r\right)\right)) \iff (e \in \operatorname{events}\left(c, \operatorname{ite}\left(c, r, l\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.shift_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A shifted call belongs to the endpoint event set of a branch exactly when its unshifted call belongs to the corresponding child event set with that child birth type. This consumed helper connects the recursive local edge proof to the same original event inventory.

**Theorem 1.7 (Actual addressed subtrees of membership cuts).**

$$\forall t: \operatorname{Source}, (\forall p: \operatorname{Address}, (\forall v: \operatorname{Source}, ((\operatorname{subtree}\left(p, t\right) = \operatorname{some}\left(v\right)) \Rightarrow (\forall b: \operatorname{Bool}, (\forall I: \operatorname{Set}\left(\operatorname{Call}\right), (\operatorname{subtree}\left(p, \operatorname{cutTerm}\left(b, t, I\right)\right) = \operatorname{ite}\left(\operatorname{Created}\left(I, p\right), \operatorname{some}\left(\operatorname{cutTerm}\left(\operatorname{birthAt}\left(b, p\right), v, \operatorname{sectionAt}\left(I, p\right)\right)\right), \operatorname{none}\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.subtree_partial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every target subtree at address p, the actual subtree of the membership-defined cut is absent exactly when some strict ancestor creating split is absent. Otherwise it is the local membership cut of that target subtree, with birth type determined by the final address bit. This statement requires no execution or ideal hypothesis.

**Theorem 1.8 (Native guard and creating ancestors).**

$$\begin{aligned}&\forall t: \operatorname{Source}, \forall p: \operatorname{Address}, \forall v: \operatorname{Source}, (\operatorname{subtree}\left(p, t\right) = \operatorname{some}\left(v\right)) \Rightarrow (\\&(v \neq \operatorname{of}\left(\operatorname{true}\right)) \Rightarrow (\forall b: \operatorname{Bool}, \forall I: \operatorname{Set}\left(\operatorname{Call}\right), (\\&((\operatorname{Guard}\left(\operatorname{promote}\left(p\right), \operatorname{cutTerm}\left(b, t, I\right)\right)) \iff ((\operatorname{Created}\left(I, p\right)) \land ((\operatorname{birthAt}\left(b, p\right) = \operatorname{true}) \land ((\neg (\operatorname{promote}\left(p\right) \in I)) \land (\forall l: \operatorname{Source}, (\forall r: \operatorname{Source}, ((v = \operatorname{mul}\left(l, r\right)) \Rightarrow (\neg (\operatorname{split}\left(p\right) \in I)))))))))\\&\land ((\operatorname{Guard}\left(\operatorname{split}\left(p\right), \operatorname{cutTerm}\left(b, t, I\right)\right)) \iff ((\operatorname{Created}\left(I, p\right)) \land (((\operatorname{birthAt}\left(b, p\right) = \operatorname{false}) \lor (\operatorname{promote}\left(p\right) \in I)) \land (\forall l: \operatorname{Source}, (\forall r: \operatorname{Source}, ((v = \operatorname{mul}\left(l, r\right)) \Rightarrow (\neg (\operatorname{split}\left(p\right) \in I)))))))))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.guard_ancestor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every non-alpha target subtree, promotion is guarded exactly when all strict ancestor splits have occurred, its position was born alpha, its promotion is absent and its local split is absent when the target is a branch. Splitting is guarded exactly when all creating ancestors have occurred, the position was born beta or its promotion has occurred, and its branch split is absent. These equivalences use the unchanged subtree operation and actual alpha/beta constructors. They are the structural witness used in the subsequent guard and transition proofs.

**Theorem 1.9 (Initial birth leaf).**

$$\forall b: \operatorname{Bool}, (\forall t: \operatorname{Source}, ((\operatorname{Born}\left(b, t\right)) \Rightarrow (\operatorname{cutTerm}\left(b, t, \emptyset\right) = \operatorname{of}\left(b\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.partial_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a target in the original no-left-alpha domain compatible with its specified birth type, the empty membership cut is precisely that birth leaf. Born beta cannot have alpha as target.

**Theorem 1.10 (Actual native transition).**

$$\forall b: \operatorname{Bool}, (\forall t: \operatorname{Source}, (\forall I: \operatorname{Set}\left(\operatorname{Call}\right), ((\operatorname{Born}\left(b, t\right)) \Rightarrow ((\operatorname{Ideal}\left(b, t, I\right)) \Rightarrow (\forall e: \operatorname{Call}, ((e \in \operatorname{events}\left(b, t\right)) \Rightarrow ((\operatorname{Guard}\left(e, \operatorname{cutTerm}\left(b, t, I\right)\right)) \Rightarrow (\operatorname{edited}\left(\operatorname{cutTerm}\left(b, t, I\right), e\right) = \operatorname{cutTerm}\left(b, t, \operatorname{insert}\left(e, I\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.partial_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every supported lower set, every endpoint event whose actual leaf guard holds changes the cut by the original edited replacement, giving exactly the membership cut with that event inserted. The split case proves both child cuts are still their birth leaves; the descendant case descends through an already present creating split.

**Theorem 1.11 (Actual guards are finite-order enabling).**

$$\forall b: \operatorname{Bool}, (\forall t: \operatorname{Source}, (\forall I: \operatorname{Set}\left(\operatorname{Call}\right), ((\operatorname{Born}\left(b, t\right)) \Rightarrow ((\operatorname{Ideal}\left(b, t, I\right)) \Rightarrow (\forall e: \operatorname{Call}, ((e \in \operatorname{events}\left(b, t\right)) \Rightarrow ((\operatorname{Guard}\left(e, \operatorname{cutTerm}\left(b, t, I\right)\right)) \iff (\operatorname{Enabled}\left(b, t, I, e\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.guard_enabled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every compatible target, supported lower set and endpoint event, the actual native leaf guard is equivalent to freshness and membership of every strict causal predecessor. The proof locates the actual non-alpha target subtree of each event, characterizes enabling by creating-ancestor and local membership conditions, and applies guard_ancestor at that event address. This consumes the full addressed-subtree correspondence, with no simulation or reachability premise.

**Theorem 1.12 (History-independent inventory).**

$$\forall b: \operatorname{Bool}, (\forall t: \operatorname{Source}, (\forall I: \operatorname{Set}\left(\operatorname{Call}\right), ((\operatorname{Born}\left(b, t\right)) \Rightarrow ((\operatorname{Ideal}\left(b, t, I\right)) \Rightarrow (\operatorname{events}\left(b, \operatorname{cutTerm}\left(b, t, I\right)\right) = I)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.cut_events` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reading the endpoint-defined event inventory of a membership cut returns exactly its supported lower set. Root events and shifted child events are separated by their actual addresses. This invariant makes distinct lower sets have distinct partial endpoints.

**Theorem 1.13 (Full endpoint reconstruction).**

$$\forall b: \operatorname{Bool}, (\forall t: \operatorname{Source}, ((\operatorname{Born}\left(b, t\right)) \Rightarrow (\operatorname{cutTerm}\left(b, t, \operatorname{events}\left(b, t\right)\right) = t)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.cut_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cut containing every endpoint label reconstructs the original target term. The proof recursively reconstructs both children after the root split; it does not select a serial history.

**Theorem 1.14 (Native executions between arbitrary ideals).**

$$\begin{aligned}&\forall b: \operatorname{Bool}, \forall t: \operatorname{Source}, (\operatorname{Born}\left(b, t\right)) \Rightarrow (\\&\forall K: \operatorname{Set}\left(\operatorname{Event}\left(b, t\right)\right), \forall J: \operatorname{Set}\left(\operatorname{Event}\left(b, t\right)\right), (\operatorname{IsLowerSet}\left(K\right)) \Rightarrow ((\operatorname{IsLowerSet}\left(J\right)) \Rightarrow (\\&\forall l: \operatorname{List}\left(\operatorname{Event}\left(b, t\right)\right), ((\operatorname{Exec}\left(K, l, J\right)) \iff (\operatorname{run}\left(\operatorname{cutTerm}\left(b, t, \operatorname{raw}\left(b, t, K\right)\right), \operatorname{erase}\left(l\right)\right) = \operatorname{some}\left(\operatorname{cutTerm}\left(b, t, \operatorname{raw}\left(b, t, J\right)\right)\right))))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.execution_adequacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all two lower sets and every list of endpoint labels, abstract enabled execution between those sets is equivalent to successful original run between their membership cuts. The reverse induction maintains the reached ideal at every prefix. Each step obtains its guard from the preceding equivalence and uses the actual replacement theorem; equality of terminal cuts is reflected by the event inventory invariant.

**Theorem 1.15 (Exact labelled extension histories).**

$$\forall t: \operatorname{Source}, ((\operatorname{D}\left(t\right)) \Rightarrow (\forall l: \operatorname{List}\left(\operatorname{Event}\left(\operatorname{true}, t\right)\right), ((\operatorname{run}\left(\operatorname{of}\left(\operatorname{true}\right), \operatorname{erase}\left(l\right)\right) = \operatorname{some}\left(t\right)) \iff (\operatorname{ExtensionList}\left(\emptyset, \operatorname{univ}, l\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.linear_extension_histories` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original D target and every list of its labelled endpoint events, successful original run from alpha to that target is equivalent to being an extension list from the empty ideal to the full ideal. Only after native adequacy is established does the proof invoke EnabledPathSwapConnectivity.result for the generic finite-poset correspondence.

**Theorem 1.16 (No hidden membership premise on histories).**

$$\forall t: \operatorname{Source}, ((\operatorname{D}\left(t\right)) \Rightarrow (\forall w: \operatorname{List}\left(\operatorname{Call}\right), ((\operatorname{run}\left(\operatorname{of}\left(\operatorname{true}\right), w\right) = \operatorname{some}\left(t\right)) \iff (\exists l: \operatorname{List}\left(\operatorname{Event}\left(\operatorname{true}, t\right)\right), ((\operatorname{erase}\left(l\right) = w) \land (\operatorname{ExtensionList}\left(\emptyset, \operatorname{univ}, l\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.all_histories` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every raw successful Call word from alpha to a D target has a lift to exactly its endpoint-labelled linear extension, and conversely every such lift is an actual successful word. A separate source-operation induction proves that every actual successful call adds its own fresh event to the native inventory. Thus membership in the endpoint label set is proved from the raw run, never assumed as a history premise.

The owning source clauses are Unified Joint Law Bridge Proposition 5.3 legal generation and causal inverse, Proposition 5.6 causal versus serial history, and Atomic Generation Acquisition AA17.2 enabled-event adequacy. These theorems do not establish the actual seven-coordinate group laws, mixed selected partitions, controller measurability, eight-event signed probability law or common full-tree submass. The complete seven/eight target remains open. The all-assignment promised-comb application is NativePromiseCausalBoundary.result.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.all_histories`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.cut_events`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.cut_full`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.execution_adequacy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.guard_ancestor`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.guard_enabled`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.linear_extension_histories`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.lt_promote_root`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.lt_shift`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.lt_split_root`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.partial_empty`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.partial_insert`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.root_before`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.shift_lt`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.shift_mem`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.subtree_partial`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativePostClockInverse](../Observer/OriginalVector/NativePostClockInverse.md)
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity](../../../ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.md)
- Narrative reference: [D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate](../ActualImageAddressCertificate.md)
- Narrative reference: [D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity](../ActualLeafHistoryRigidity.md)
- Narrative reference: [D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport](../GenealogicalFiberTransport.md)
- Narrative reference: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeGuardedLeafRepair](NativeGuardedLeafRepair.md)
- Narrative reference: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition](NativeMaterialRootRecognition.md)
- Narrative reference: [D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativePostClockInverse](../Observer/OriginalVector/NativePostClockInverse.md)
- Narrative reference: [D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity](../../../ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.md)
