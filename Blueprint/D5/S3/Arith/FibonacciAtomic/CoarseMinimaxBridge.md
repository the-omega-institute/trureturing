# Coarse Controllers and the Minimax Lower Bound

## Abstract

A uniformly one-excess coarse controller supplies a safe endpoint route, forcing two excess queries when the endpoint spectrum is empty.

**Theorem 1.1 (Universal endpoint bridge and lower bound).**

$$\forall k: Nat, ((1 \le k) \implies ((\forall pi: Strategy, ((\operatorname{CoarseObservable}\left(\operatorname{policy}\left(pi\right)\right)) \implies ((\forall i: \operatorname{Fin}\left(2k+1\right), (\operatorname{C}\left(pi, \operatorname{F}\left(k, i\right)\right) \le 3k+14)) \implies (\exists z: \operatorname{Fin}\left(2k+1\right), (\exists qs: \operatorname{List}\left(Address\right), (\operatorname{Safe}\left(k, z, qs\right))))))) \land ((3 \le k) \implies (\forall pi: Strategy, ((\operatorname{CoarseObservable}\left(\operatorname{policy}\left(pi\right)\right)) \implies (\exists i: \operatorname{Fin}\left(2k+1\right), (3k+15 \le \operatorname{C}\left(pi, \operatorname{F}\left(k, i\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/CoarseMinimaxBridge.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k at least one, I(k)=Fin(2k+1). Let e be Fintype.equivFin from Unit plus Fin(k) plus Fin(k), and let F(k,i) be the existing Scale38NestedCompensation.family(k,e.symm(i)). Every member has n=3k+13 leaves. Strategy means one deterministic policy that terminates and correctly decides positivity on every nonempty finite ordered labelled full binary tree. CoarseObservable means that the policy depends only on its chronological history with branch and absent merged into none, retaining both distinct leaf labels. C(pi,U) is the number of different addresses actually requested.

Safe(k,z,qs) denotes CoarseEndpointPeeling.Peels(F(k),z,univ,qs). Each address is a leaf of the eventual target, its merged nonleaf group has at most one surviving member, and the final survivor set is contained in the target singleton. The first conjunct quantifies over every coarse Strategy with a uniform cost bound n+1. It produces an actual finite address list and a target with this safety property. The existing peeling theorem realizes the list as a globally correct coarse endpoint strategy with exact paid sets.

Take the finite accepting runs of the controller on all members. At each common coarse history, retain each member's actual raw prefix and residual execution. A stopping node has at most one member: two different nonconflicting positive trees must have a fresh coarse divergence. At a query node, two members giving none would both have paid a nonleaf on the same coarse prefix. The common-history obstruction would force one terminal nonleaf count to be at least two, contradicting the uniform one-excess bound.

A node with at least two members therefore has a nonempty matching leaf child. Skip a query when that child is the whole survivor set, and otherwise retain its actual address and continue through that child. Finite residual execution budgets decrease, so the construction reaches a singleton. The retained list is a subsequence of the chosen member's actual residual query list. It is executed as a new route; deleted reports are never installed as observations. In particular, the original controller may pay extra nonleaves after reaching a singleton, and no original coordinate is assumed to have cost n.

For k at least three the exact coarse endpoint spectrum is empty. If a coarse Strategy had no input of cost at least n+2, integrality would give the uniform bound n+1. The first conjunct would then supply a safe endpoint route, contradicting that spectrum. Thus every such Strategy has a family member of cost at least 3k+15.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CoarseMinimaxBridge.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/CoarseEndpointSpectrum](CoarseEndpointSpectrum.md)
