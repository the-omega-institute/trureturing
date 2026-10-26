# Weighted Reattachment and the Fair-Band Distribution

## Abstract

Actual cut paths determine the complete reattached cycle inventory and its independent fair-band law.

Let X be finite and s,r involutive permutations. Put E=Fix(r), q=s*r, and P equal to the constructed first-return endpoint pairing. For any permutation J of E, reattach by f=s*(r*extend(J)). The length l_J(x) is the actual least positive q-time from J(x) to the next exposed endpoint. The reattached return permutation is H=P*J. No supplied boundary pairing, classifier transport, orbit size, or cycle partition is assumed. The theorem remains valid without fixed-point-freeness; physical ribbon interpretations additionally use a free corner matching.

**Theorem 1.1 (Actual Reattachment Retains Every Cycle and Its Length).**

$$\forall X \in FiniteType,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall r \in \operatorname{Perm}\left(X\right),\; \left(\operatorname{Involutive}\left(s\right) \land \operatorname{Involutive}\left(r\right)\right) \Rightarrow \left(\forall J \in \operatorname{Perm}\left(\operatorname{Fix}\left(r\right)\right),\; \operatorname{CompleteWeightedReattachment}\left(s, r, J\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/WeightedReattachment.reattachment_weighted_cycle_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement supplies original cut first-visit witnesses, the full tower successor conjugacy, equality of untouched-cycle sets, equality of every untouched iterate before and after reattachment, and the complete inventory identity. It constructs return data using FiniteEndpointPairing, then consumes the greedy tower and least-period proofs. If L_J(x) is the sum of l_J around the H-cycle, the marked term is sum_x l_J(x) Z^L_J(x)/L_J(x). The unmarked term uses the original q-periods.

For the exact conditional signed-ribbon law, let B be any finite set of unresolved bands and e:B times Fin(4) -> E a bijection. Every sign state is a function omega:B->Bool, each equally likely. On one labelled quadruple the two matchings are J0=(0 2)(1 3) and J1=(0 3)(1 2); bandPairs(omega) uses the selected matching independently on each band. Transport it by e to obtain J_omega. The remaining attachments and corner matching are held fixed. This models conditioning on rotations and all resolved signs. Distinct flags are required by e even when the underlying graph has loops or parallel bands.

**Theorem 1.2 (The Entire Cycle-Inventory Distribution Under Fair Band Signs).**

$$\forall X \in FiniteType,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall r \in \operatorname{Perm}\left(X\right),\; \left(\operatorname{Involutive}\left(s\right) \land \operatorname{Involutive}\left(r\right)\right) \Rightarrow \left(\forall B \in FiniteType,\; \forall e \in \operatorname{Equiv}\left(\operatorname{Product}\left(B, \operatorname{Fin}\left(4\right)\right), \operatorname{Fix}\left(r\right)\right),\; \forall test \in \operatorname{Function}\left(\operatorname{Polynomial}\left(Rational\right), Rational\right),\; \operatorname{FairMeanOriginalInventoryTest}\left(s, r, e, test\right) = \operatorname{FairMeanWeightedInventoryTest}\left(s, r, e, test\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/WeightedReattachment.fair_band_inventory_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both sides average test over the 2^card(B) equally weighted Boolean sign states. The arbitrary rational-valued test is applied to the complete inventory polynomial before averaging. Indicator tests therefore recover every inventory probability and every joint cycle-length event, rather than only separate expected cycle counts. The proof is the pointwise constructed inventory identity followed by finite averaging. No claim is made of a polynomial-time evaluation, a new circuit-nullity theorem, unlabelled-map uniformity, or an exact-thirds law. This is reusable formal infrastructure for an explicitly stated labelled sampler.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/WeightedReattachment.fair_band_inventory_law`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/WeightedReattachment.reattachment_weighted_cycle_inventory`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch](FiniteBandSwitch.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers](FiniteReturnTowers.md)
