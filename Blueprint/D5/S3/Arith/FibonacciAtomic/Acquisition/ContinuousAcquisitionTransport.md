# Preserving a continuous competitor's acquired information

## Abstract

Continuous source-blind acquisition has an exact operational transport to terminal reset histories.

**Theorem 1.1 (One public selector preserves every terminating run).**

$$\forall (S : \operatorname{Type}\left(\right)) (L : \operatorname{Type}\left(\right)) (P : \operatorname{Controller}\left(S, L\right)) (H : \mathbb{N}) (E : \operatorname{List}\left(\operatorname{Event}\left(\right)\right)) (v : \mathbb{N} \times \mathbb{N}) (t : S) (y : \mathbb{N} \times \mathbb{N}) (l : L), \operatorname{Run}\left(P, H, \operatorname{initial}\left(P\right), v, E, t, y, l\right) \implies \operatorname{execute}\left(\operatorname{terminalGcd}\left(H\right), \operatorname{selector}\left(P\right), \operatorname{paidReads}\left(E\right)+1, [], v\right) = \operatorname{some}\left((\operatorname{records}\left([], E\right), l)\right) \land \operatorname{normalize}\left(P, \operatorname{replay}\left(P, \operatorname{records}\left([], E\right)\right)\right) = (t, \operatorname{finalWord}\left([], E\right)) \land y = \operatorname{runWord}\left(\operatorname{finalWord}\left([], E\right), v\right) \land \operatorname{length}\left(\operatorname{records}\left([], E\right)\right) = \operatorname{paidReads}\left(E\right) \land \operatorname{PublicRun}\left(P, (\operatorname{initial}\left(P\right), []), E, (t, \operatorname{finalWord}\left([], E\right)), l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Acquisition/ContinuousAcquisitionTransport.continuous_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A controller has an arbitrary configuration space S, an initial configuration, a default output and one source-independent instruction function. The type binders S and L range over arbitrary, independently chosen universes. An instruction takes a local step, completes one original action with its fixed acknowledgement, requests a paid gcd reply, or halts with an output. A read continuation receives the complete natural-number reply. Source coordinates never enter the instruction function. True denotes R(a,b)=(b,a+b), and false denotes G(a,b)=(a+1,b). Only a paid read returns gcd(2a+3b,H).

S need not be finite or bounded. A configuration can contain a finite program's instruction pointer, arbitrary finite binary working memory, retained records, public parameters and opaque handles. The semantic theorem even allows arbitrary transition functions, a larger class than effective finite programs. Every finite source-blind program with the stated operations has this transition form: ordinary computation changes local configuration, an original call changes the one actual pair and returns its fixed acknowledgement, and a read changes only local memory. There is no finite-state, fixed-horizon or uniform local-work premise.

Run is the actual operational relation on natural pairs, including zero. Its event tape records local steps, completed actions and paid replies in chronological order. The terminal local configuration and actual endpoint are separate indices. A run may have no reads, may repeat the same read, and may perform arbitrary finite local computations and actions after its last read. All those actions remain in the terminal cumulative word.

For an event tape E, records(A,E) pairs each reply with the complete chronological action word accumulated from A before that reply. Local steps produce no record; actions append a letter; each reply produces exactly one record. Empty words and repeated words are retained and charged. finalWord(A,E) includes all actions, including the final interval after the last reply. paidReads(E) counts reply events.

The selector replays public code from its initial configuration using only acquired history. Between reads it runs local instructions and appends each action to a local cumulative-word buffer. At a requested read it selects that whole word as one reset query. It feeds the acquired answer into the same continuation and repeats. After the final answer it completes the remaining public interval before returning the original output. No unknown pair is simulated or consulted.

Public interval evaluation uses StateTransition.eval, the usual partial execution of a deterministic transition function. normalize gives this partial operation an arbitrary total value on divergent histories. This totalization is noncomputable. On every actual prefix of a terminating run its value agrees with the finite public interpreter. The selector has no fuel, entry, stopping-time, tariff or backing-capacity input. No decision procedure for divergent histories or uniform bound on finite intervals is asserted.

The proof follows each original local, action and read step. Deterministic public evaluation has the same endpoint before and after a silent step. The action-word invariant is x=runWord(A,v); appending an action updates both sides by that same original action. At a read, terminalGcd(H,A,v) is consequently the complete actual current gcd. The replayed instruction and its next local configuration coincide. Induction preserves all subsequent adaptive choices. At halt it preserves the output, final local state and entire action word, not only the acquired replies.

For every run from initial state and entry v with tape E, terminal state t, endpoint y and output l, reset execution with the single selector and paidReads(E)+1 proof fuel returns exactly (records([],E),l). Normalized replay of that trace is (t,finalWord([],E)); y equals runWord(finalWord([],E),v); and the reset trace length equals paidReads(E). PublicRun proves that the public interpreter reproduces the entire same event tape, including each local step and action. The proof fuel certifies execution in the reset interface and is never passed to the selector. The same selector works for every entry.

**Theorem 1.2 (The exact reset optimum bounds the full continuous class).**

$$\forall (S : \operatorname{Type}\left(\right)) (H : \mathbb{N}) (P : \operatorname{Controller}\left(S, \operatorname{ZMod}\left(H\right) \times \operatorname{ZMod}\left(H\right)\right)) (J : \mathbb{N}), (1 \le H \land (\forall (v : \mathbb{N} \times \mathbb{N}), \exists (E : \operatorname{List}\left(\operatorname{Event}\left(\right)\right)) (t : S) (y : \mathbb{N} \times \mathbb{N}), \operatorname{Run}\left(P, H, \operatorname{initial}\left(P\right), v, E, t, y, \operatorname{residueSource}\left(H, v\right)\right) \land \operatorname{paidReads}\left(E\right) \le J)) \implies \operatorname{ite}\left(H=1, 0, 2\operatorname{costBound}\left(H\right)\right) \le J$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Acquisition/ContinuousAcquisitionTransport.continuous_acquisition_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix H at least one and one controller whose output type is ZMod(H) squared. Suppose that for every natural pair v there exists a terminating actual run outputting residueSource(H,v), with at most J paid replies. These run witnesses are per entry; their local step counts, action counts, tapes and termination times need not share a bound. Apply the transport to each run using the same public selector. Its exact traces and per-entry proof fuels witness that J belongs to TerminalGcdAcquisitionCost.acquisitionBudgets(H).

The least-budget clause of terminal_gcd_acquisition_cost then gives (if H=1 then 0 else 2 costBound(H)) at most J. For H greater than one, costBound(H) is the maximum of h(p-1) over prime powers p^h exactly dividing H. The prime-axis arithmetic lower bound is reused without alteration. Identification alone suffices, so the inequality also applies to every successful identification and behavior-return competitor with retained callable service.

This transport is a comparison of information interfaces, not a reset primitive for the actual continuous source. It proves no attaining return policy, positive closing construction, synchronized installed updater, source-service realization or upper resource bound. The original fixed acknowledgements, exclusive serial control, finite per-run service and backing, and exclusion of timing, failure, size or tariff observations are the interface conditions represented by Run. The simulated local computation is charged separately; only paid-read count is asserted to be preserved as an optimized resource.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/ContinuousAcquisitionTransport.continuous_acquisition_lower_bound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Acquisition/ContinuousAcquisitionTransport.continuous_transport`
- Dependency: [D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost](../TerminalGcdAcquisitionCost.md)
