# Raw Endpoint Leaf Peeling

## Abstract

Raw leaf peeling follows one target while separating branch and absent reply groups, and completes each selected source with its entire labelled leaf frontier.

The sources and four replies are the actual ordered binary trees and their original readout. A strategy uses a single deterministic policy, starts with an empty history on every source, and terminates correctly on every finite source. Fees count the distinct addresses actually requested. L(U) is the existing leafAddresses(U).

**Definition 1.1 (Safe target-leaf lists).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/RawEndpointPeeling.Peels`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/RawEndpointPeeling.Peels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite family F, target z, survivor set S and finite address list qs, Peels recursively requires each address to be a leaf of F(z). The branch and absent response groups in S each have at most one member. The next survivor set is the group reporting the target's actual reply. At the end every survivor is z. When S initially contains z, it retains z throughout. For a nonconflicting family, every leaf reply matches the target label, so the recursion deletes exactly the two nonleaf groups and leaves no competitor at the end.

**Definition 1.2 (Actual raw peeling controller).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/RawEndpointPeeling.peelController`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/RawEndpointPeeling.peelController` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The controller actually requests the next address. A target reply continues with its response group. A different reply whose group is a singleton starts that source's complete leaf verifier with a fresh logical history; any other reply starts the existing acquisition fallback. Exhausting the list starts the target's complete verifier. The verifier accepts only the complete matching labelled frontier, and mismatches enter acquisition. The paid set comes from the resulting execution history.

**Theorem 1.3 (Endpoint criterion and exact execution bills).**

$$\forall k: Nat, ((1 \leq k) \implies (\forall z: \operatorname{Fin}\left(m\right), (((\exists pi: \operatorname{Strategy}\left(\right), (\forall i: \operatorname{Fin}\left(m\right), (\operatorname{C}\left(pi, \operatorname{Fk}\left(i\right)\right) = n + 1 - \operatorname{indicator}\left(i = z\right)))) \iff (\exists qs: \operatorname{List}\left(\operatorname{Address}\left(\right)\right), (\operatorname{Peels}\left(Fk, z, univ, qs\right)))) \land (\forall qs: \operatorname{List}\left(\operatorname{Address}\left(\right)\right), ((\operatorname{Peels}\left(Fk, z, univ, qs\right)) \implies (\exists pi: \operatorname{Strategy}\left(\right), ((\operatorname{policy}\left(pi\right) = \operatorname{P}\left(\operatorname{c}\left(Fk, z, qs\right)\right)) \land (\forall U: \operatorname{Source}\left(\right), (\operatorname{T}\left(pi, U\right) = \operatorname{O}\left(\operatorname{c}\left(Fk, z, qs\right), U\right))) \land (\forall i: \operatorname{Fin}\left(m\right), (\operatorname{C}\left(pi, \operatorname{Fk}\left(i\right)\right) = n + 1 - \operatorname{indicator}\left(i = z\right))) \land (\operatorname{J}\left(pi, \operatorname{Fk}\left(z\right)\right) = \operatorname{L}\left(\operatorname{Fk}\left(z\right)\right)) \land (\forall i: \operatorname{Fin}\left(m\right), ((i \neq z) \implies (\exists q: \operatorname{Address}\left(\right), ((\operatorname{First}\left(qs, Fk, i\right) = \operatorname{some}\left(q\right)) \land (\neg (q \in \operatorname{L}\left(\operatorname{Fk}\left(i\right)\right))) \land (\operatorname{J}\left(pi, \operatorname{Fk}\left(i\right)\right) = \operatorname{L}\left(\operatorname{Fk}\left(i\right)\right) \cup \operatorname{singleton}\left(q\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/RawEndpointPeeling.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least one, m=2k+1 and n=3k+13. Fk is the existing nested-compensation family transported from Unit plus Fin(k) plus Fin(k) to Fin(m) by Fintype.equivFin. This bijection changes only the member indices. All members are positive, distinct, nonconflicting and have n leaves. The target z ranges over every member. The indicator is one when its equality holds and zero otherwise; subtraction is natural subtraction.

C(pi,U), J(pi,U) and T(pi,U) denote the existing cost, paid terminal-history set and terminal outcome. c(Fk,z,qs) is peelController(Fk,z,univ,qs), O(c,U) is controllerOutcome(c,U), and P(c) is controllerPolicy(c). First(qs,Fk,i) is List.find? with the actual nonleaf predicate chi(readout(a,Fk(i)))=1. Thus some(q) identifies the first exit address, including in lists with repeated requests.

Necessity uses a recursive actual-response route whose costs are no greater than those of the given strategy. Zero target excess makes every query on its path a target leaf. Each branch or absent child has zero remaining excess on all its members; nonconflict forces such a child to be a singleton. Following the target child therefore yields a safe finite list. Conversely the listed controller follows matching leaves until the first nonleaf response, selects that unique member, and verifies its complete frontier. Earlier queries are that member's leaves; its exit is its sole nonleaf. On the target all route queries are leaves. Complete verification yields exactly the asserted paid sets and endpoint costs on every family member. The existing execution contract connects every controller outcome to the policy's actual finite run on every source.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/RawEndpointPeeling.Peels`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/RawEndpointPeeling.peelController`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/RawEndpointPeeling.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation](Scale38NestedCompensation.md)
