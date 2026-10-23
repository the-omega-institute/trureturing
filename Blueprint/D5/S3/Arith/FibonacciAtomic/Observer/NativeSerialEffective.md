# NativeSerialEffective

## Abstract

NativeSerialEffective

**Definition 1.1 (Acquired external event).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalEvent`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalEvent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite event records the actual update epoch or the actual epoch, finite physical address and four-valued reply of a Read. Repetition and chronological order are retained.

**Definition 1.2 (Complete finite accessible selector state).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalState`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four components encode common finite input, deterministic accessible workspace, certified epoch and the complete acquired chronological record. Natural encodings permit arbitrary finite strings and finite records; there is no bound on their lengths. The state is common at the fixed entrance, rather than chosen separately for each source.

**Definition 1.3 (Effective four-valued encoding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalReplyCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalReplyCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Alpha, beta, branch and absent have codes zero, one, two and three.

**Definition 1.4 (Actual Read state transition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.afterOriginalRead`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.afterOriginalRead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Append the actual epoch, submitted address and actual reply without changing the register or epoch; select the designated accessible workspace.

**Definition 1.5 (Actual update state transition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.afterOriginalUpdate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.afterOriginalUpdate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Append the update and increment the epoch while physical execution applies substitution to the same register.

**Definition 1.6 (Independent source selector actions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalAction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A source action is a finite Read address with four workspace continuations, an update continuation, or a finite output. These sum/product carriers have the standard Primcodable representation. All four Read continuations may be the same saved workspace; the next selector evaluation can perform arbitrary reply-dependent computation from the appended record.

**Definition 1.7 (Read action constructor).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalRead`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalRead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite address is computed by the partial selector; no fixed address bound is supplied.

**Definition 1.8 (Update action constructor).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalUpdate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalUpdate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real same-register substitution with a finite workspace continuation.

**Definition 1.9 (Absorbing output action).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalStop`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalStop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Halt returns the entire finite output and ends this invocation.

**Definition 1.10 (Reply-directed workspace).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalContinuation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalContinuation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual four-valued reply selects the continuation, and is also appended to the full record.

**Definition 1.11 (Partial-recursive original selector semantics).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalEffectiveService`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalEffectiveService` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Effectiveness means the standard mathlib Partrec predicate on the independently specified finite input, workspace, epoch and full history carrier. This is the ordinary partial-recursive interpretation of a deterministic effective selector on finite data, not a field asserting representation in a packet machine. Divergence is permitted on unreachable histories. A sourcewise terminating service supplies finite OriginalRun witnesses only for its actual source fiber.

**Definition 1.12 (Independent original boundary execution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalRun`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Selection is membership in a partial computation. The source rules append every physical event, perform actual substitution, query the actual current register, and stop with the full output. Local selector computation is not an extra physical event.

**Definition 1.13 (Exact partial-recursive realization).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalSelectorCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalSelectorCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pinned Nat.Partrec.Code.exists_code realizes the selector on encoded finite states and outputs. Choosing one fixed code is an existential program choice, not runtime totalization of its partial evaluation.

**Definition 1.14 (Explicit code realization).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalCodeRealization`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalCodeRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A caller supplies a concrete Nat.Partrec.Code and an equality at every genuine encoded OriginalState: eval code (encode s) equals the encoded partial action selected at s. No equality is required on invalid natural representations. Every original partial-recursive selector has such a code by originalSelectorCode_spec specialized at encode s and encodek; the choice may be noncomputable. This is existence of one program for each service, with no uniform executable extraction from a proposition. The proof is not consulted by the executable evaluator.

**Definition 1.15 (Executable finite-code evaluator).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.evalOriginalActionFromCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.evalOriginalActionFromCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At finite stage j evaluate an explicitly supplied partial-recursive code with evaln fuel 2^j and decode one original action. A miss advances only the stage. Cofinality follows from evaln_mono and j < 2^j, so every finite sufficient raw fuel is eventually exceeded. The raw evaluator requires its encoded input to be below its fuel; the schedule permits execution on arbitrary finite histories without a global bound. This definition contains no classical choice and can be run directly; no runtime complexity estimate is asserted.

**Definition 1.16 (Realized finite-code evaluator).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.evalOriginalActionCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.evalOriginalActionCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The executable evaluator selected by an OriginalCodeRealization is the supplied code evaluator, with the realization equation available only for the soundness and completeness bridge.

**Theorem 1.17 (Realized action soundness).**

$$\forall O: Type [\operatorname{Primcodable}\left(O\right)], (\forall S: \operatorname{OriginalEffectiveService}\left(O\right), (\forall R: \operatorname{OriginalCodeRealization}\left(S\right), (\forall s: OriginalState, (\forall j: Nat, (\forall a: \operatorname{OriginalAction}\left(O\right), ((\operatorname{evalOriginalActionCode}\left(R, j, \operatorname{encode}\left(s\right)\right) = \operatorname{some}\left(a\right)) \implies (\operatorname{mem}\left(a, \operatorname{select}\left(S, s\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.evalOriginalActionCode_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every stage, a decoded action returned on a genuine source state belongs to that state's independently specified partial selector. The proof directly reuses evaln_sound and the genuine-state realization equation; the boundary-prefix simulation consumes it to rule out any earlier different action.

**Theorem 1.18 (Cofinal action completeness).**

$$\forall O: Type [\operatorname{Primcodable}\left(O\right)], (\forall S: \operatorname{OriginalEffectiveService}\left(O\right), (\forall R: \operatorname{OriginalCodeRealization}\left(S\right), (\forall s: OriginalState, (\forall a: \operatorname{OriginalAction}\left(O\right), ((\operatorname{mem}\left(a, \operatorname{select}\left(S, s\right)\right)) \implies (\exists j: Nat, (\operatorname{evalOriginalActionCode}\left(R, j, \operatorname{encode}\left(s\right)\right) = \operatorname{some}\left(a\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.evalOriginalActionCode_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual selected action is returned at some finite stage. evaln_complete supplies raw fuel, evaln_mono lifts it to 2^stage, and encodek recovers the action. The native boundary induction consumes this witness separately for Stop, ApplyRho and Read, without a common runtime bound.

**Definition 1.19 (Bounded evaluator).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.evalOriginalAction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.evalOriginalAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only total finite-fuel evaln is executed. Its soundness and completeness are reused directly from pinned mathlib; a reached action has some finite sufficient fuel, while an unreachable diverging state need never yield an action.

**Definition 1.20 (Encoded evaluator configuration).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalControl`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pair the source state code with a finite controller counter. The original chosen-code controller uses it as raw fuel; the explicit executable backend uses it as stage j and queries raw fuel 2^j. Both reset the counter to zero after each physical action.

**Definition 1.21 (Total source-blind microsteps).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalNativeControl`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalNativeControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decode the finite state and run one bounded evaluator attempt. Failure inserts a Local step with increased fuel; success submits exactly the selected physical action. No tree, timing, identity, equality, reset or clone port enters control.

**Definition 1.22 (Executable finite-code controller).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalNativeControlFromCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalNativeControlFromCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Run one source-blind native microstep from an explicit code. Failed finite evaluation emits only a local evaluator step; successful Read, ApplyRho and Stop actions use the same source-state transitions as the original controller.

**Definition 1.23 (Realized finite-code controller).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalNativeControlCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalNativeControlCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The controller attached to a proved explicit code realization. Its runtime behavior is entirely determined by the code, while the realization proof establishes correspondence with the original partial selector.

**Definition 1.24 (External trace erasure).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.eraseEvaluatorSteps`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.eraseEvaluatorSteps` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Remove only Local evaluator steps, retaining all actual substitutions and every repeated physical Read and reply.

**Definition 1.25 (Typed external observation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.ExternalObservation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.ExternalObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observation type explicitly distinguishes update, Read and Halt carrying the complete output.

**Definition 1.26 (External event projection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.externalEvents`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.externalEvents` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Project native traces to external observations by removing local work only.

**Definition 1.27 (Terminal whole-output observation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.terminalObservation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.terminalObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Append exactly one Halt with the full output to the chronological external events.

**Theorem 1.28 (General original-selector simulation).**

$$\forall O: Type [\operatorname{Primcodable}\left(O\right)], (\forall S: \operatorname{OriginalEffectiveService}\left(O\right), (\forall s: OriginalState, (\forall r: Source, (\forall t: Trace, (\forall o: O, ((\operatorname{OriginalRun}\left(S, s, r, t, o\right)) \implies ((\operatorname{Computable}\left(\operatorname{uncurry}\left(\operatorname{evalOriginalAction}\left(S\right)\right)\right)) \land (\exists n: Trace, ((\operatorname{Run}\left(\operatorname{originalNativeControl}\left(S\right), \operatorname{originalControl}\left(s, 0\right), \operatorname{epoch}\left(s\right), r, n, o\right)) \land (\operatorname{eraseEvaluatorSteps}\left(n\right) = t) \land (\operatorname{reads}\left(n\right) = \operatorname{reads}\left(t\right)) \land (\operatorname{terminalObservation}\left(n, o\right) = \operatorname{terminalObservation}\left(t, o\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.original_service_simulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bounded evaluator is certified Computable by exact composition of primrec_evaln and decoding. For every terminating execution of any partial-recursive original selector, one fixed total source-blind evaluator control has a finite native run on the identical current register and certified epoch. Increasing-fuel search terminates separately at each reached boundary. Erasure preserves the exact external trace, repeated Read list and terminal observation including Halt and the entire output. No uniform local, workspace, update or runtime bound is used.

**Theorem 1.29 (Direct executable original-selector simulation).**

$$\forall O: Type [\operatorname{Primcodable}\left(O\right)], (\forall S: \operatorname{OriginalEffectiveService}\left(O\right), (\forall R: \operatorname{OriginalCodeRealization}\left(S\right), (\forall s: OriginalState, (\forall r: Source, (\forall t: Trace, (\forall o: O, ((\operatorname{OriginalRun}\left(S, s, r, t, o\right)) \implies ((\operatorname{Computable}\left(\operatorname{uncurry}\left(\operatorname{evalOriginalActionCode}\left(R\right)\right)\right)) \land (\exists n: Trace, ((\operatorname{Run}\left(\operatorname{originalNativeControlCode}\left(R\right), \operatorname{originalControl}\left(s, 0\right), \operatorname{epoch}\left(s\right), r, n, o\right)) \land (\operatorname{eraseEvaluatorSteps}\left(n\right) = t) \land (\operatorname{reads}\left(n\right) = \operatorname{reads}\left(t\right)) \land (\operatorname{terminalObservation}\left(n, o\right) = \operatorname{terminalObservation}\left(t, o\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.original_code_service_simulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a supplied finite code and its genuine-state realization equation, the exponential-stage evaluator is Computable by Nat.Primrec.pow, Primrec2.unpaired', primrec_evaln and decoding. For every OriginalRun, cofinal completeness and the boundary induction give a finite native trace on the identical register and certified epoch. Erasure retains the exact suffix, every repeated paid Read, real ApplyRho, terminal Halt and entire output. Common input, workspace, epoch and retained history are unrestricted finite data. Partial divergence away from reached states remains allowed, and no uniform runtime, address, workspace or totality bound is added.

**Definition 1.30 (Encoded machine instruction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.Packet`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.Packet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An unrestricted natural number encodes local machine state. A finite packet supplies an opcode, successor or output code, a finite physical address and four continuation states. Neither the state set nor address domain is bounded.

**Definition 1.31 (Encoded source-free service).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.EffectiveService`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.EffectiveService` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The one-step interpreter is computable. Local divergence remains an unbounded sequence of local steps. The output map interprets terminal output codes in the semantic output type; the lower-bound class also permits arbitrary such interpretations. An effective finite-output decoder is one allowed interpretation; arbitrary output maps need not themselves be effective. Common input is part of the fixed initial control, never a hidden source argument.

**Definition 1.32 (Literal reply continuation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.continuation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.continuation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four continuation entries are selected by alpha, beta, branch and absent respectively. Selecting a continuation consumes exactly the reply returned by the submitted physical Read.

**Definition 1.33 (Exact four-operation bridge).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.compile`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.compile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compilation only maps one encoded machine instruction to its native Local, Read, ApplyRho or Stop case. It performs no next-boundary search and constructs no observation tree.

**Definition 1.34 (Direct encoded-service execution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.ServiceRun`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.ServiceRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The direct rules operate on the actual original physical register. Read invokes the literal port once; ApplyRho performs real substitution. Every action, epoch, address, reply and entire terminal output is retained.

**Theorem 1.35 (Trace-preserving effective-service inclusion).**

$$\forall O: Type, (\forall S: \operatorname{EffectiveService}\left(O\right), (\forall c, e: Nat, (\forall r: Source, (\forall t: Trace, (\forall o: O, ((\operatorname{ServiceRun}\left(S, c, e, r, t, o\right)) \implies (\operatorname{Run}\left(\operatorname{compile}\left(S\right), c, e, r, t, o\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.effective_service_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every direct encoded-service run is a native serial run on exactly the same register with exactly the same full action trace and output. Thus every chronological call and update is preserved one for one. The native lower-bound class is broader: its control types and transition functions need not be computable.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.EffectiveService`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.ExternalObservation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalAction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalCodeRealization`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalEffectiveService`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalEvent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalRun`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.OriginalState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.Packet`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.ServiceRun`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.afterOriginalRead`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.afterOriginalUpdate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.compile`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.continuation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.effective_service_inclusion`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.eraseEvaluatorSteps`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.evalOriginalAction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.evalOriginalActionCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.evalOriginalActionCode_complete`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.evalOriginalActionCode_sound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.evalOriginalActionFromCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.externalEvents`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalContinuation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalControl`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalNativeControl`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalNativeControlCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalNativeControlFromCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalRead`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalReplyCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalSelectorCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalStop`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.originalUpdate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.original_code_service_simulation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.original_service_simulation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.terminalObservation`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine](NativeSerialMachine.md)
