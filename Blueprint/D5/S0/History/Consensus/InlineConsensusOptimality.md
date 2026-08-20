# Inline Consensus Optimality

## Abstract

A finite fail-closed consensus router is the unique greatest sound rule, and every maximal protocol run consumes a finite shared resource potential.

**Theorem 1.1 (The termination router is sound, maximal, and unique).**

$$\operatorname{Sound}(r*) \land \forall p, \operatorname{Sound}(p) \Rightarrow p \le r* \land \operatorname{unique}(r*)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusOptimality.termination_router_sound_maximal_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observation alphabet contains exactly three named termination seats, five possible seat results, and a three-slot roster. The result function cannot contain a meta-judge verdict. Hazard is stated independently as a fake roster or a named seat that is not satisfied; it is not defined as the Boolean complement of the router.

The proof exhausts the finite router rows to identify hazard-free observations with exact-roster all-satisfied observations. Soundness and pointwise maximality follow from that equivalence. Uniqueness applies Mathlib's IsGreatest.unique rather than reproving greatest-element antisymmetry.

Two concrete competitors show that both halves do work. Always-abstain is sound but strictly below the router at the exact all-satisfied fixture. Majority-admit is strictly more permissive, but the two-satisfied and one-unsatisfied fixture proves that it is not sound. The review table also has the hazard-complement form and its soundness and maximality are checked in Lean. The design table does not: it has convergence and bounded-stall exits and supplies no independent binary hazard predicate, so no design maximality claim is forced.

Snapshot note: the abstract model was compared with the beta.32 sshx SKILL.md whose SHA-256 is ab688e34f2b183291958f78b2d9ff6905d7330f3844668c5103026790d8b4cbf and CODEX_WORKER_SPEC.md whose SHA-256 is 700237b1a1389002215272874e8c9cd7b17a130f0d0eaf7bb20cf9b39f49829d. This is prose snapshot correspondence only. A later plugin version may falsify it without falsifying the Lean theorems; no current or future plugin version is claimed.

**Theorem 1.2 (Every maximal protocol run is explicitly bounded).**

$$\forall run, length(run) \le \operatorname{explicitRunBound}(config)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/Consensus/InlineConsensusOptimality.every_reachable_run_is_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ClauseId and clauseTrace name the formal object for every load-bearing clause S1 through S10: seven stages and unique successors; carrier priority and eligible-untried fallback; immutable retry budgets; the five completion conjuncts and forbidden proxies; terminal abstention; peer-output-free seat views; disclosed prior exposure and a perfectly correlated heterogeneous countermodel; all three routing tables; a termination roster without meta-judge results; and one shared pass counter.

A protocol step either erases one previously available stage-role-carrier key, follows the unique stage successor, consumes one shared bounded-pass unit, or enters terminal or abstained. The potential is the sum of remaining flight keys, remaining stage edges, remaining shared passes, and one live-state credit. Mathlib's card_erase_lt_of_mem proves that a flight failure strictly decreases the first component; the other constructors decrease their named component.

Induction over the operational execution proves stage order, retry-budget compliance, non-reopening of carrier keys, and the shared-pass bound. A maximal live state is impossible because abstain is always an available transition. The concrete fallback fixture selects codex first, then nyxid after codex is erased, and lies below the same explicit bound; the thinking-abstain fixture contains no dependent-stage event.

## References

- Truth anchor: `D5/S0/History/Consensus/InlineConsensusOptimality.every_reachable_run_is_bounded`
- Truth anchor: `D5/S0/History/Consensus/InlineConsensusOptimality.termination_router_sound_maximal_unique`
