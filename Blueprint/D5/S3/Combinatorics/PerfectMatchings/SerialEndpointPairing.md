# Serial Composition of Actual Endpoint Pairings

## Abstract

Actual first-return pairings of arbitrary finite modules compose in series on the full original carrier.

**Theorem 1.1 (The two permutations of two points).**

$$\forall c \in \operatorname{Perm}\left(\operatorname{Fin}\left(2\right)\right),\; c = 1 \lor c = \operatorname{swap}\left(0, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/SerialEndpointPairing.two_forms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every permutation of Fin(2) is either the identity or the swap of 0 and 1.

A cut module consists of a finite carrier X, an involutive corner permutation s with no fixed point, an involutive band permutation r, and an equivalence e from Fin(4) onto the entire fixed set of r. The labels 0 and 1 are the left pair, and 2 and 3 the right pair. The local pairing is e inverse composed with endpointPairing(s,r) composed with e. Here endpointPairing is the actual first positive return of s*r to Fix(r), not an additional input. Its involutivity and absence of fixed points imply the three forms D=(01)(23), T=(02)(13), and U=(03)(12). A pairing is through when it differs from D.

Let n be any natural number. The family M has n+1 cut modules indexed by Fin(n+1), and c assigns an arbitrary permutation of Fin(2) to each of the n adjacent connectors. Put L(i,a)=e_i(a) and R(i,a)=e_i(2+a), for a in Fin(2). The chain carrier is the full disjoint union of the original X_i, with flags written (i,x). Its corner action is the original s_i on each summand. Its band action preserves r_i away from the local ports, joins (i,R(i,a)) with (i+1,L(i+1,c_i(a))), and fixes the two flags at the first left port and the two at the last right port. These prescriptions define an involution: the connector pairs are disjoint, every local nonport pair is retained, and the four outer flags are exactly the fixed points. In serialOn(n,M,c), the outer equivalence lists these flags in the order first-left 0, first-left 1, last-right 0, last-right 1. The global corner has no fixed point.

**Theorem 1.2 (The Original-Carrier Serial Criterion and its Action Laws).**

$$\forall n \in Nat,\; \forall M \in \operatorname{Function}\left(\operatorname{Fin}\left(n + 1\right), CutModule\right),\; \forall c \in \operatorname{Function}\left(\operatorname{Fin}\left(n\right), \operatorname{Perm}\left(\operatorname{Fin}\left(2\right)\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(n + 1\right),\; \forall x \in \operatorname{Carrier}\left(\operatorname{apply}\left(M, i\right)\right),\; \operatorname{corner}\left(\operatorname{serialOn}\left(n, M, c\right), \operatorname{pair}\left(i, x\right)\right) = \operatorname{pair}\left(i, \operatorname{corner}\left(\operatorname{apply}\left(M, i\right), x\right)\right)\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(n + 1\right),\; \forall x \in \operatorname{Carrier}\left(\operatorname{apply}\left(M, i\right)\right),\; \operatorname{band}\left(\operatorname{apply}\left(M, i\right), x\right) \ne x \Rightarrow \operatorname{band}\left(\operatorname{serialOn}\left(n, M, c\right), \operatorname{pair}\left(i, x\right)\right) = \operatorname{pair}\left(i, \operatorname{band}\left(\operatorname{apply}\left(M, i\right), x\right)\right)\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall a \in \operatorname{Fin}\left(2\right),\; \operatorname{band}\left(\operatorname{serialOn}\left(n, M, c\right), \operatorname{pair}\left(\operatorname{castSucc}\left(i\right), \operatorname{ports}\left(\operatorname{apply}\left(M, \operatorname{castSucc}\left(i\right)\right), \operatorname{natAdd}\left(a, 2\right)\right)\right)\right) = \operatorname{pair}\left(\operatorname{succ}\left(i\right), \operatorname{ports}\left(\operatorname{apply}\left(M, \operatorname{succ}\left(i\right)\right), \operatorname{castAdd}\left(\operatorname{apply}\left(\operatorname{apply}\left(c, i\right), a\right), 2\right)\right)\right)\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(2\right),\; \operatorname{ports}\left(\operatorname{serialOn}\left(n, M, c\right), \operatorname{castAdd}\left(a, 2\right)\right) = \operatorname{pair}\left(0, \operatorname{ports}\left(\operatorname{apply}\left(M, 0\right), \operatorname{castAdd}\left(a, 2\right)\right)\right)\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(2\right),\; \operatorname{ports}\left(\operatorname{serialOn}\left(n, M, c\right), \operatorname{natAdd}\left(a, 2\right)\right) = \operatorname{pair}\left(\operatorname{last}\left(n\right), \operatorname{ports}\left(\operatorname{apply}\left(M, \operatorname{last}\left(n\right)\right), \operatorname{natAdd}\left(a, 2\right)\right)\right)\right) \land \left(\operatorname{pairing}\left(\operatorname{serialOn}\left(n, M, c\right)\right) \ne \operatorname{Dead}\left(\right) \Leftrightarrow \left(\forall i \in \operatorname{Fin}\left(n + 1\right),\; \operatorname{pairing}\left(\operatorname{apply}\left(M, i\right)\right) \ne \operatorname{Dead}\left(\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/SerialEndpointPairing.serial_endpoint_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the displayed formula K(n,M,c) denotes serialOn(n,M,c), P denotes the actual labelled endpoint pairing, and Dead denotes D. The six conjuncts give the corner action, the nonport band action, every forward connector pair, the two left outer labels, the two right outer labels, and the through criterion. The reverse connector action follows from band involutivity. The type of K also includes the finite carrier, involutivity of both actions, the free-corner law, and the exact outer-port equivalence. The case n=0 is one original module with no connector.

First consider two modules. Their disjoint-union corner and cut-band actions have eight exposed flags. An iterate starting in either summand remains there until reattachment, so its first-return time and endpoint are precisely those of that original module. Thus the actual eight-port pairing is the disjoint sum of the two local pairings. Reattaching the two adjacent pairs changes the orbit relation on these eight flags to the orbit relation of the actual local-pairing sum followed by the connector. This is the original endpoint-pairing reattachment theorem, applied to the constructed cut.

For any four-port cut module, the two left labels are in the same corner/band rotation orbit exactly when its actual pairing is D. Apply this observation to the two-module chain. The three structural forms of each local pairing and the two permutations of Fin(2) show that the two outer left labels are in different rotation orbits exactly when both local pairings are through. Induction, attaching the final module to the existing chain, proves the assertion for every length. The explicit equivalence with the tagged original carrier transports the original corner and band actions and all four outer labels.

No connectedness or restriction on unmarked components is imposed. The construction keeps components missing all local ports and closed components meeting internal ports but missing the four outer ports. They do not change the marked orbit relations used above. This result is the deterministic series rule; it makes no assertion about diamond counts, sign distributions, physical edge categories, necklace graph properties, expected values, thresholds or limits.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/SerialEndpointPairing.serial_endpoint_pairing`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/SerialEndpointPairing.two_forms`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch](FiniteBandSwitch.md)
