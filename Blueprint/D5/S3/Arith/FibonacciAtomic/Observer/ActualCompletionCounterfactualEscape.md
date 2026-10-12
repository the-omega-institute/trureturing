# Native Counterfactual Completion Obstruction

## Abstract

Every original normalized completion has one matching prefix whose fresh acquisition branch ladder escapes each finite atomic-action Observer on raw counterfactual histories.

Address is the original list of Boolean directions; RawHistory retains literal addresses and raw Reply values, including branch, absent, contradictory repetitions and reports that no source realizes. Source is the original nonempty ordered FreeMagma Bool tree. The arbitrary finite family F may be empty or contain duplicates. The finite PassiveProtocol route and decoder are unrestricted.

**Definition 1.1 (Literal all-left address).**

$$\forall n: Nat, (\operatorname{leftAddress}\left(n\right) = \operatorname{replicate}\left(n, false\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionCounterfactualEscape.leftAddress` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

leftAddress(n) is the literal Boolean word of n false directions, with empty root at zero. No quotient identifies words of different lengths.

**Definition 1.2 (Chronological branch ladder).**

$$(\operatorname{branchHistory}\left(0\right) = \operatorname{nil}\left(\right)) \land (\forall n: Nat, (\operatorname{branchHistory}\left(n+1\right) = \operatorname{append}\left(\operatorname{branchHistory}\left(n\right), \operatorname{singleton}\left(\operatorname{pair}\left(\operatorname{leftAddress}\left(n\right), branch\right)\right)\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionCounterfactualEscape.branchHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

branchHistory(n) reports branch at depths zero through n minus one. These reports are formal raw inputs, with no bounded-source realization premise. The chosen ladder is fixed by encodeHistory after kappa_hist; arbitrary raw histories are not fixed. In particular a root absent report empties the raw frontier, whereas its coarse-none representative is branch and inserts both children.

**Definition 1.3 (Length of every nominal atomic action).**

$$(\forall q: Address, (\operatorname{queryAddressLength}\left(\operatorname{inl}\left(q\right)\right) = \operatorname{length}\left(q\right))) \land (\forall b: Bool, (\operatorname{queryAddressLength}\left(\operatorname{inr}\left(b\right)\right) = 0))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionCounterfactualEscape.queryAddressLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An atomic query action contributes its literal address length; either Boolean halt contributes zero. The finite maximum in the proof ranges over the complete nominal Observer carrier, including dormant query rows and absorbing halt rows.

**Theorem 1.4 (One fresh prefix and an unbounded native ladder).**

$$\forall u: Universe, (\forall m: Nat, (\forall F: \operatorname{Fin}\left(m\right) \to Source, (\forall decode: CoarseHistory \to \operatorname{Option}\left(\operatorname{Fin}\left(m\right)\right), (\forall p: \operatorname{PassiveProtocol}\left(Address, \operatorname{constant}\left(\operatorname{Option}\left(Bool\right)\right)\right), (\forall pi: Strategy, ((\operatorname{policy}\left(pi\right) = \lambda h: RawHistory \mapsto \operatorname{controllerPolicy}\left(\operatorname{compileRaw}\left(F, decode, p, \operatorname{nil}\left(\right)\right), \operatorname{encodeHistory}\left(\operatorname{kappaHist}\left(h\right)\right)\right)) \implies \exists pre: RawHistory, ((\forall k: \operatorname{Fin}\left(\operatorname{length}\left(pre\right)\right), (\operatorname{policy}\left(pi, \operatorname{take}\left(pre, \operatorname{val}\left(k\right)\right)\right) = \operatorname{inl}\left(\operatorname{fst}\left(\operatorname{get}\left(pre, k\right)\right)\right))) \land (\forall s: RawHistory, (\operatorname{routePhase}\left(F, decode, p, \operatorname{nil}\left(\right), \operatorname{kappaHist}\left(\operatorname{append}\left(pre, s\right)\right)\right) = \operatorname{pair}\left(\operatorname{acquisition}\left(\operatorname{kappaHist}\left(s\right)\right), \operatorname{acquisitionPolicy}\left(\operatorname{encodeHistory}\left(\operatorname{kappaHist}\left(s\right)\right)\right)\right))) \land (\forall n: Nat, (\operatorname{policy}\left(pi, \operatorname{append}\left(pre, \operatorname{branchHistory}\left(n\right)\right)\right) = \operatorname{inl}\left(\operatorname{leftAddress}\left(n\right)\right))) \land (\forall E: \operatorname{Type}\left(u\right), ([\operatorname{Fintype}\left(E\right)], \forall M: \operatorname{Observer}\left(E\right), (\exists n: Nat, (\operatorname{historyAction}\left(M, \operatorname{append}\left(pre, \operatorname{branchHistory}\left(n\right)\right)\right) \neq \operatorname{policy}\left(pi, \operatorname{append}\left(pre, \operatorname{branchHistory}\left(n\right)\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionCounterfactualEscape.counterfactual_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m, F : Fin m to Source, decoder, finite route p and original Strategy pi with the displayed exact policy identity, the theorem constructs one finite raw prefix pre before quantifying either depth or Observer. Every prefix step has the literal matching-address certificate pi.policy(pre.take(k)) = inl((pre.get(k)).address). For every raw suffix s, the full original phase parser returns acquisition(kappa_hist(s)) and acquisitionPolicy(encodeHistory(kappa_hist(s))). In particular the local suffix at s empty is genuinely empty. Its action is pi.policy(pre ++ s) by the first conjunct of phase_replay_contract, applied to the original policy identity.

A singleton source of false is used solely to choose answers along the arbitrary finite route. encode_projection identifies the resulting coarse route with its raw representative. Induction on the native PassiveProtocol proves matching at each chronological request, preserving the seen history and repeated addresses. If decode selects no prototype, the route itself is pre. If it selects i, the existing leaf-cardinality and labelled-leaf facts give a first leaf q with Boolean expectation. Append the matching-address branch report at q; its coarse none differs from that expectation. The existing first-verifier-mismatch reset yields fresh acquisition for every suffix, even if q was reported in the route. This construction adds no prototype and asserts no realization of the entire counterfactual history.

The substantive new invariant is: for every n there exists rest with frontier(branchHistory(n)) = leftAddress(n) :: rest. Symbolic induction uses the original acquisitionStep: a matching head branch replaces the head with its left child followed by its right child and retains all pending addresses. Normalization fixes precisely this ladder, so the phase action identity yields pi.policy(pre ++ branchHistory(n)) = inl(leftAddress(n)). This invariant is used on the live path to the final disagreement.

For every universe-polymorphic finite E and original Observer M, let B be the finite supremum of queryAddressLength(M.action(e)) over all e in E. Finset.le_sup bounds the actual history row by B. On the same prefix and ladder at n = B + 1, the strategy requests a word of length B + 1, so historyAction(M,pre ++ branchHistory(n)) differs. No assumption of existing disagreement, fallback reachability or infinite action range occurs in the telescope.

This is the source-level implication of proposition 38.71. An original positive-family completion supplies pi and the exact policy identity through completion_contract; the structural proof uses neither prototype positivity nor a source budget. Thus for any positive allowed budget, including one or two, all-history equality with a finite Observer contradicts the displayed disagreement. These are direct applications, rather than additional retained mathematical declarations. The theorem retains impossible histories and arbitrary literal addresses; it does not replace all-history equality by actual-source equality or by coarse factorization.

The actual bounded-source compiler of proposition 38.70 still reproduces actual traces, raw caches and stopping behavior on its promised sources. Its counterfactual behavior may differ from the original completion. A generic finite-state stream emitter with an external output accumulator can assemble words over several outputs; that accumulator and interface are outside this Observer model, in which each row emits one complete literal address or one Boolean halt. No physical memory, runtime or stream-transducer bound is asserted. The result is a native formalization and application of the source argument, without a literature originality claim.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionCounterfactualEscape.branchHistory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionCounterfactualEscape.counterfactual_escape`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionCounterfactualEscape.leftAddress`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionCounterfactualEscape.queryAddressLength`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay](ActualCompletionPhaseReplay.md)
