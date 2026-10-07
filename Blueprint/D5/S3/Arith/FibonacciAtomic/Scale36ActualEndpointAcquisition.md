# Scale36 Actual Endpoint Acquisition

## Abstract

The Scale36 family has distinct compatible positive trees and all literal actual endpoints.

For k at least one, I(k) is Unit plus Fin(k) times Fin(2). The Unit row is P0, and the two exceptional rows in slot j are Uj and Vj. There are k active slots and one compensation slot in the ordered right comb. E is the beta/alpha pair, A is (E,beta), C is (A,E), B is (C,A), T is (A,C), W1 is (B,C), and KT is (T,A). P0 has C in every active slot and KT at the tail. Uj replaces these by T and B; Vj by W1 and A. Q(k,i) is the complete bracket-preserving preimage and n(k)=5k+11. The map kappahist retains the chronological addresses and merges branch and absent responses. A policy factors through this map precisely when it depends only on that coarse history.

**Theorem 1.1 (Positive, Distinct and Nonconflicting Prototypes).**

$$\forall k: Nat, ((1 \leq k) \implies ((\operatorname{Injective}\left(\operatorname{F}\left(k\right)\right)) \land (\forall i: \operatorname{I}\left(k\right), ((\operatorname{rho3}\left(\operatorname{Q}\left(k, i\right)\right) = \operatorname{F}\left(k, i\right)) \land (\operatorname{Positive}\left(\operatorname{F}\left(k, i\right)\right)) \land (\operatorname{length}\left(\operatorname{F}\left(k, i\right)\right) = \operatorname{n}\left(k\right)) \land (\operatorname{card}\left(\operatorname{L}\left(\operatorname{F}\left(k, i\right)\right)\right) = \operatorname{n}\left(k\right)))) \land (\forall i: \operatorname{I}\left(k\right), (\forall j: \operatorname{I}\left(k\right), (\operatorname{NC}\left(\operatorname{F}\left(k, i\right), \operatorname{F}\left(k, j\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Scale36ActualEndpointAcquisition.family_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The third substitution image respects every pair in the right comb. Its complete preimages give positivity. The ordinary C block has five leaves; each exceptional block together with its compensation has sixteen. Reading a full activity slot recovers its tree, so the exceptional position and type determine the index. The activity blocks C,T,W1 and compensation blocks KT,B,A separately agree at every shared leaf. This agreement extends through the common ordered comb.

The four addresses in slot j are a=R^j LLLR, b=R^j LRR, q=R^j LRLLR, r=R^j LLLLLR, with zero-based j. Ordinary scans ask a, then b only after an alpha leaf. A coarse nonleaf report selects Vj at a and Uj at b. Two alpha reports continue. A Uj target scans all other slots, then uses a,q in its retained slot; a Vj target uses q,r. Unexpected beta reports invoke acquisition.

**Theorem 1.2 (All Actual Endpoints and Exact Paid Sets).**

$$\forall k: Nat, ((1 \leq k) \implies (((\operatorname{Injective}\left(\operatorname{F}\left(k\right)\right)) \land (\forall i: \operatorname{I}\left(k\right), ((\operatorname{rho3}\left(\operatorname{Q}\left(k, i\right)\right) = \operatorname{F}\left(k, i\right)) \land (\operatorname{Positive}\left(\operatorname{F}\left(k, i\right)\right)) \land (\operatorname{length}\left(\operatorname{F}\left(k, i\right)\right) = \operatorname{n}\left(k\right)) \land (\operatorname{card}\left(\operatorname{L}\left(\operatorname{F}\left(k, i\right)\right)\right) = \operatorname{n}\left(k\right)))) \land (\forall i: \operatorname{I}\left(k\right), (\forall j: \operatorname{I}\left(k\right), (\operatorname{NC}\left(\operatorname{F}\left(k, i\right), \operatorname{F}\left(k, j\right)\right))))) \land (\operatorname{card}\left(\operatorname{I}\left(k\right)\right) = 2 \cdot k + 1) \land (\forall i: \operatorname{I}\left(k\right), (\exists pi: Strategy, ((\operatorname{FactorsThrough}\left(\operatorname{policy}\left(pi\right), kappahist\right)) \land (\forall j: \operatorname{I}\left(k\right), ((\operatorname{J}\left(pi, \operatorname{F}\left(k, j\right)\right) = \operatorname{L}\left(\operatorname{F}\left(k, j\right)\right) \cup \operatorname{X}\left(k, i, j\right)) \land (\operatorname{cost}\left(pi, \operatorname{F}\left(k, j\right)\right) = \operatorname{n}\left(k\right) + 1 - \operatorname{indicator}\left(i = j\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Scale36ActualEndpointAcquisition.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each route selects its actual evaluation prototype. Ordinary continuation requests are alpha leaves of that input. At the retained slot, the a/q and q/r rules distinguish P0,Uj,Vj with the displayed extra address. The paid set J equals the full leaf set L together with the empty or singleton set X. X is empty at the target itself. For a different input Uj it is b_j, except that target Vj uses r_j. For a different input Vj it is a_j. For input P0 and an exceptional target it is q at the target slot.

The coarse completion contract compiles each finite route into an original Strategy whose policy depends only on the coarse chronological history. This one strategy is usable through both readout interfaces. A tentative selection starts full leaf verification; a mismatch or failed selection starts global acquisition. Strategy correctness and finite termination quantify over every finite source tree, from the same empty initial history. True cache hits preserve actual responses and the union of requests. The extra address is a nonleaf, so the bill is n at the target and n+1 at every other evaluation row.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale36ActualEndpointAcquisition.family_structure`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale36ActualEndpointAcquisition.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion](ActualCoarseReadoutCompletion.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum](FourExitRawEndpointSpectrum.md)
