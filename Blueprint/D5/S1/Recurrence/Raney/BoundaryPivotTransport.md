# Boundary-Pivot Transport

## Abstract

Boundary pivots make the signed endpoint corrections of actual descent edges eventually periodic.

The BKS block mechanism supplies bounded edge corrections but does not by itself identify one finite family for every actual block. This owner follows the actual complementary letters at both endpoints through consecutive descent edges. Extremal choices make the next state deterministic, while retaining the left and right pivots as one paired state preserves their joint realization.

**Definition 1.1 (A letter image contains an outside letter).**

$$\operatorname{imageMeetsComplement}\left(g, Delta, a\right) \iff \exists t \in \operatorname{Fin}\left(Q\right),\; \neg (\operatorname{uniformLetter}\left(g, a, t\right) \in Delta)$$

*Formalization.* `D5/S1/Recurrence/Raney/BoundaryPivotTransport.imageMeetsComplement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

For a Q-uniform morphism g, imageMeetsComplement(g,Delta,a) means that some offset in Fin(Q) has g(a)[offset] outside Delta. The existential offset is literal and is later extremized separately at the two boundaries.

**Theorem 1.2 (Two actual edges transport both boundary pivots).**

$$\operatorname{IsBksDescentStep}\left(Q, grand, parent\right) \land \operatorname{IsBksDescentStep}\left(Q, parent, child\right) \Rightarrow \operatorname{existsExtremalPivotsWithSignedEquations}\left(Q, grand, parent, child\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/BoundaryPivotTransport.actual_boundary_pivot_transport_at_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

Fix q>0 and Q=P^q together with the Q-uniform fixed-word and support-stability facts. Given actual edges grandparent->parent and parent->child, the left boundary is represented by the outside exit at parent.first-1 and the right boundary by the outside exit at parent.last+1. On the left choose the rightmost image entry whose own image meets the complement; on the right choose the leftmost. The theorem returns exit, entry, and next-exit offsets in Fin(Q), their letters and extremality conditions, and the exact signed equations grand.first-Q*parent.first=Q*entry+nextExit+1-Q*(exit+1) and (grand.last+1)-Q*(parent.last+1)=Q*entry+nextExit-Q*exit.

**Definition 1.3 (The paired outside-letter state).**

$$\operatorname{actualBksPivotState}\left(Q, w, (i, j)\right) = (\operatorname{w}\left(\operatorname{div}\left(i - 1, Q\right)\right), \operatorname{w}\left(\operatorname{div}\left(j + 1, Q\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Raney/BoundaryPivotTransport.actualBksPivotState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

For endpoints (i,j), the state is the pair of word letters at quotient indices (i-1)/Q and (j+1)/Q. Natural subtraction gives the boundary-safe value at i=0, although descent edges themselves are late. Keeping the pair together is essential: separate left and right optima would not certify a common block.

**Theorem 1.4 (Paired states determine the next state and correction).**

$$\operatorname{twoEdgeWindows}\left(Q, blocks, i, j\right) \Rightarrow (((\operatorname{state}\left(i\right) = \operatorname{state}\left(j\right)) \Rightarrow (\operatorname{state}\left(i + 1\right) = \operatorname{state}\left(j + 1\right))) \land ((\operatorname{state}\left(i\right) = \operatorname{state}\left(j\right) \land \operatorname{state}\left(i + 1\right) = \operatorname{state}\left(j + 1\right)) \Rightarrow (\operatorname{first}\left(\operatorname{blocks}\left(i + 1\right)\right) - Q \cdot \operatorname{first}\left(\operatorname{blocks}\left(i\right)\right) = \operatorname{first}\left(\operatorname{blocks}\left(j + 1\right)\right) - Q \cdot \operatorname{first}\left(\operatorname{blocks}\left(j\right)\right) \land \operatorname{last}\left(\operatorname{blocks}\left(i + 1\right)\right) + 1 - Q \cdot \left(\operatorname{last}\left(\operatorname{blocks}\left(i\right)\right) + 1\right) = \operatorname{last}\left(\operatorname{blocks}\left(j + 1\right)\right) + 1 - Q \cdot \left(\operatorname{last}\left(\operatorname{blocks}\left(j\right)\right) + 1\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/BoundaryPivotTransport.actual_bks_pivot_state_dynamics_at_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

For one fixed q and a sequence of blocks, two adjacent valid descent edges determine the next paired pivot state from the current one. Moreover, if two two-edge windows have equal current and following paired states, their two signed endpoint displacements are equal. The proof uses the extremal offsets returned by actual_boundary_pivot_transport_at_power, not an unrealized product of marginal choices.

**Theorem 1.5 (Signed endpoint displacements are eventually periodic).**

$$\exists q \in \mathbb{N},\; 0 < q \land \forall Delta \in FinsetA,\; \forall blocks \in \operatorname{Seq}\left(\operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right)\right),\; (\forall k \in \mathbb{N},\; \operatorname{IsBksDescentStep}\left(P^{q}, \operatorname{blocks}\left(k + 1\right), \operatorname{blocks}\left(k\right)\right)) \Rightarrow (\exists N0 \in \mathbb{N},\; \exists t \in \mathbb{N},\; 0 < t \land \forall k \in \mathbb{N},\; (N0 \leq k) \Rightarrow (\operatorname{first}\left(\operatorname{blocks}\left(k + t + 1\right)\right) - Q \cdot \operatorname{first}\left(\operatorname{blocks}\left(k + t\right)\right) = \operatorname{first}\left(\operatorname{blocks}\left(k + 1\right)\right) - Q \cdot \operatorname{first}\left(\operatorname{blocks}\left(k\right)\right) \land \operatorname{last}\left(\operatorname{blocks}\left(k + t + 1\right)\right) + 1 - Q \cdot \left(\operatorname{last}\left(\operatorname{blocks}\left(k + t\right)\right) + 1\right) = \operatorname{last}\left(\operatorname{blocks}\left(k + 1\right)\right) + 1 - Q \cdot \left(\operatorname{last}\left(\operatorname{blocks}\left(k\right)\right) + 1\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/BoundaryPivotTransport.exists_eventually_periodic_actual_bks_signed_displacements` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

For every infinite sequence of actual descent edges at the selected power Q, there are N and a positive period t such that for all k>=N both corrections repeat after t: the left correction is block(k+1).first-Q*block(k).first, and the right correction uses last+1 in the same way. Finite paired states force a repeated state; deterministic transition propagates it, and equal adjacent state pairs give equal corrections. The conclusion is about signed Int displacements, so boundary borrowing is preserved.

## References

- Truth anchor: `D5/S1/Recurrence/Raney/BoundaryPivotTransport.actualBksPivotState`
- Truth anchor: `D5/S1/Recurrence/Raney/BoundaryPivotTransport.actual_bks_pivot_state_dynamics_at_power`
- Truth anchor: `D5/S1/Recurrence/Raney/BoundaryPivotTransport.actual_boundary_pivot_transport_at_power`
- Truth anchor: `D5/S1/Recurrence/Raney/BoundaryPivotTransport.exists_eventually_periodic_actual_bks_signed_displacements`
- Truth anchor: `D5/S1/Recurrence/Raney/BoundaryPivotTransport.imageMeetsComplement`
- Dependency: [D5/S1/Recurrence/Raney/MaximalBlockDescent](MaximalBlockDescent.md)
