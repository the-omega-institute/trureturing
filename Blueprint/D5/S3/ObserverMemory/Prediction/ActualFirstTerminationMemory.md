# Actual First-Termination Memory

## Abstract

A fixed universal code has exact first-termination pulses, attained per-program memory minima, and no computable uniform bound.

## The fixed program and its operational clock

The source uses one fixed code u and places the program index e in the literal input [e]. The code is the standard Nat.Partrec numbering transported through decodeCode and encodeCode; no family of codes is selected as e varies. The finite-data machine has Data = List Nat, a typed continuation Stack, and Cfg = Data + (Stack x Data). The normal and returning interpreters implement the pinned ToPartrec operational clauses.

step is exactly one effective ToPartrec.step: a terminal Data configuration maps to none, while a live continuation performs one returning transition. The initial clock is 0 -> halt [] and encode(c)+1 -> normal u [] [c]; run u e n is the n-fold Option transition from that initial state. pulse u e n is true exactly when run u e n is live and the next native step is terminal. Thus the clock counts native transitions, and t=0 is an actual first-termination case.

step_decode and run_decode identify this clock pointwise and at every index with the effective ToPartrec.step. first_terminal adds the exact first-terminal equivalence: the terminal state occurs at t and every earlier pulse is false.

## Single-pulse minima and the two uniform obstructions

For a Boolean stream b, unarySizes b is the set of finite state-carrier cardinalities realized by one start state, one update, and one Boolean readout. A unique hit at t is therefore the delayed pulse decide(n = t). The imported delayed-pulse minimum, transported by single_start_dp_sizes, gives IsLeast(unarySizes b, t+2) at a hit; the all-false stream has the attained one-state minimum. Consequently every operational program has an attained finite minimum, including the t=0 case.

MinimumStateBound b s means that s e bounds every attained minimum for b e. ExhaustiveZeroPrefix b N is the inclusive cutoff property: if all n <= N e are false, then every n is false. prefixHit computes the finite prefix witness using length N(e)+1, so an effective bound or inclusive cutoff would decide the undecidable existential hit predicate.

The universal_exists construction supplies one fixed u with output equal to the singleton image of the standard program e on input zero. The final theorem combines that universal property, total computability of pulse, the operational clock equations, the sharp one-state and t+2 minima, and both nonexistence claims. No finite proxy, bounded prefix assumption, or computable selector is introduced.

## Four-slot audit boundary

The public D5 audit targets are single_start_dp_sizes, uniform_single_pulse_obstruction, step_decode, first_terminal, and original_section_6_4, with the public supporting definitions unarySizes, prefixHit, ExhaustiveZeroPrefix, MinimumStateBound, decodeCode, encodeCode, decodeStack, decodeCfg, normal, returning, step, initial, run, pulse, view, normalDispatch, normalBody, returnFrame, and returnBody.

A same-delivery faithful four-slot Contract.Registration was attempted against the enrolled dependent-family interfaces. The complete source telescope mixes an existential fixed universal code, an unbounded program/input clock, and the minimum-state and inclusive-cutoff predicates; the current enrolled templates do not provide a lawful realization/readout reconstruction with compiled variation, sensitivity, dependence, and source-occurrence binding for this family. The unfinished interface gap is recorded under https://github.com/the-omega-institute/trureturing/issues/5214. No declared_validated audit status is asserted; this issue is not a proof or a registration result.

**Theorem 1.1 (A fixed universal program has exact first-termination memory behavior).**

$$\exists u \in Code,\; \left(\left(\left(\left(\left(\left(\left(\left(\left(\forall e \in \mathbb{N},\; \operatorname{eval}(\operatorname{decodeCode}(u), [e]) = \operatorname{map}(\operatorname{singleton}, \operatorname{eval}(\operatorname{ofNatCode}(e), 0))\right) \land \operatorname{Computable}_2(\operatorname{pulse}(u))\right) \land \left(\forall e \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{run}(u, e, n).map \operatorname{decodeCfg} = \operatorname{iterate}((fun q: \operatorname{Option}(Turing.ToPartrec.Cfg) \mapsto \operatorname{bind}(q, Turing.ToPartrec.step)), n, \operatorname{some}(\operatorname{decodeCfg}(\operatorname{initial}(u, e))))\right)\right) \land \left(\forall e \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{pulse}(u, e, t) = true \Leftrightarrow \left(\left(\exists q \in \operatorname{Cfg},\; \operatorname{run}(u, e, t) = \operatorname{some}(q) \land \operatorname{step}(q) = none\right) \land \left(\forall n \in \mathbb{N},\; n < t \Rightarrow \operatorname{pulse}(u, e, n) = false\right)\right)\right)\right) \land \operatorname{pulse}(u, 0, 0) = true\right) \land \left(\forall e \in \mathbb{N},\; \left(\forall n \in \mathbb{N},\; \operatorname{pulse}(u, e, n) = false\right) \Rightarrow \operatorname{IsLeast}(\operatorname{unarySizes}(\operatorname{pulse}(u, e)), 1)\right)\right) \land \left(\forall e \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{pulse}(u, e, t) = true \Rightarrow \operatorname{IsLeast}(\operatorname{unarySizes}(\operatorname{pulse}(u, e)), t+2)\right)\right) \land \left(\forall e \in \mathbb{N},\; \exists k \in \mathbb{N},\; \operatorname{IsLeast}(\operatorname{unarySizes}(\operatorname{pulse}(u, e)), k)\right)\right) \land \left(\neg \left(\exists s \in \mathbb{N} \to \mathbb{N},\; \operatorname{Computable}(s) \land \operatorname{MinimumStateBound}(\operatorname{pulse}(u), s)\right)\right)\right) \land \left(\neg \left(\exists N \in \mathbb{N} \to \mathbb{N},\; \operatorname{Computable}(N) \land \operatorname{ExhaustiveZeroPrefix}(\operatorname{pulse}(u), N)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/ActualFirstTerminationMemory.original_section_6_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one fixed universal code u. For every natural program index e, decodeCode u on the one-element input [e] is the singleton image of the standard Nat.Partrec code of e on input zero.

The pulse is total computable. The displayed run_decode clause preserves the actual ToPartrec.step at every e and n, including the Option terminal case. The first-terminal clause records both the terminal witness at t and the falsity of every earlier pulse; pulse u 0 0 is true.

For every e, an all-false stream has minimum one, a unique hit at t has minimum t+2, and a minimum is attained. The last two clauses exclude both a total computable bound on all attained minima and a total computable inclusive zero-prefix cutoff. These are the exact operational-clock conclusions of the source theorem.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/ActualFirstTerminationMemory.original_section_6_4`
- Dependency: [D5/S3/ObserverMemory/Prediction/DelayedPulseMemoryGap](DelayedPulseMemoryGap.md)
