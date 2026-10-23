# Finite Alternating Paths and Endpoint Pairing

## Abstract

Finite alternating paths pair exposed endpoints and determine all reattached endpoint orbits.

The first-return witnesses give the same least positive first-visit length for the original cut path from J(x) and the reattached path from x, with terminal endpoint (P*J)(x). These lengths are the segment weights in the complete reattachment inventory.

Let X be finite and let s and r be involutive permutations of X. Put E = {x : r(x)=x} and q=s*r, with the right factor applied first. For x in E, take the least positive n with q^n(x) in E. Such n exists by finite permutation recurrence. P(s,r)(x) is this actual first-return endpoint. A first-return segment has no intermediate point in E. For a permutation J of E, extend(J) acts as J on E and fixes X outside E.

**Theorem 1.1 (First Return Reverses the Same Path).**

$$\forall X \in FiniteType,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall r \in \operatorname{Perm}\left(X\right),\; \left(\operatorname{Involutive}\left(s\right) \land \operatorname{Involutive}\left(r\right)\right) \Rightarrow \operatorname{Involutive}\left(\operatorname{P}\left(s, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing.endpoint_pairing_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity q^n*r*q^n=r reverses any segment with endpoints fixed by r. If a reverse segment met E earlier, reversing that shorter segment would contradict minimality of the original return time. Thus the two return times agree and P squares to the identity.

**Theorem 1.2 (A Free Corner Matching Gives Distinct Endpoints).**

$$\forall X \in FiniteType,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall r \in \operatorname{Perm}\left(X\right),\; \left(\operatorname{Involutive}\left(s\right) \land \operatorname{Involutive}\left(r\right)\right) \Rightarrow \left(\operatorname{FixedPointFree}\left(s\right) \Rightarrow \left(\forall x \in \operatorname{Fix}\left(r\right),\; \operatorname{apply}\left(\operatorname{P}\left(s, r\right), x\right) \ne x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing.endpoint_pairing_fixed_point_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a first return ended where it began, an even-length return would give an earlier r-fixed midpoint. An odd-length return would give an s-fixed midpoint. The first is excluded by minimality and the second by the absence of fixed points of s.

**Theorem 1.3 (The Constructed Pairing Computes Reattached Orbits).**

$$\forall X \in FiniteType,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall r \in \operatorname{Perm}\left(X\right),\; \left(\operatorname{Involutive}\left(s\right) \land \operatorname{Involutive}\left(r\right)\right) \Rightarrow \left(\forall J \in \operatorname{Perm}\left(\operatorname{Fix}\left(r\right)\right),\; \forall x \in \operatorname{Fix}\left(r\right),\; \forall y \in \operatorname{Fix}\left(r\right),\; \operatorname{SameCycle}\left(s \cdot r \cdot \operatorname{extend}\left(J\right), x, y\right) \Leftrightarrow \operatorname{SameCycle}\left(\operatorname{P}\left(s, r\right) \cdot J, x, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing.endpoint_pairing_reattach_same_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Changing the attachment acts only at E. Starting at x, the new walk first attaches to J(x), then follows the unchanged interior path to P(J(x)). Induction on a finite walk length decomposes every return into these actual segments. Conversely, each P*J step is a finite segment of the original permutation, so the two orbit relations agree.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing.endpoint_pairing_fixed_point_free`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing.endpoint_pairing_involutive`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing.endpoint_pairing_reattach_same_cycle`
