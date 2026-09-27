# Finite Paths and Coefficient Families

## Abstract

Finite roots and normalized periodic boundary corrections place every actual maximal-block length in finitely many affine power families.

This owner closes the gap between eventual behavior along an infinite state trajectory and a uniform statement about every finite actual descent path. It carries the finite roots and literal edge contexts together with a common factorial period, then solves the length recurrence without claiming that every resulting coefficient family is attained.

**Theorem 1.1 (A factorial period works on every sufficiently deep finite path).**

$$\exists q \in \mathbb{N},\; 0 < q \land \operatorname{finiteRootAndContextData}\left(P^{q}\right) \land S = \operatorname{card}\left(\operatorname{Prod}\left(Alphabet, Alphabet\right)\right) \land T = \operatorname{factorial}\left(S\right) \land 0 < T \land \forall j \in \mathbb{N},\; (S \leq j \land j + T < n \land \operatorname{finiteActualDescentPath}\left(Q, blocks, n\right)) \Rightarrow (\operatorname{first}\left(\operatorname{blocks}\left(j + T + 2\right)\right) - Q \cdot \operatorname{first}\left(\operatorname{blocks}\left(j + T + 1\right)\right) = \operatorname{first}\left(\operatorname{blocks}\left(j + 2\right)\right) - Q \cdot \operatorname{first}\left(\operatorname{blocks}\left(j + 1\right)\right) \land \operatorname{last}\left(\operatorname{blocks}\left(j + T + 2\right)\right) + 1 - Q \cdot \left(\operatorname{last}\left(\operatorname{blocks}\left(j + T + 1\right)\right) + 1\right) = \operatorname{last}\left(\operatorname{blocks}\left(j + 2\right)\right) + 1 - Q \cdot \left(\operatorname{last}\left(\operatorname{blocks}\left(j + 1\right)\right) + 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/FinitePathDisplacements.exists_bounded_root_and_finite_path_displacements` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

Choose the same support-stabilizing q and Q=P^q returned by the actual descent theorem. The owner retains Q-uniformity, the fixed-word equation, support stability, finite early roots, finite late root words, finite context pairs, and an actual root chain for every block. Let S be the cardinality of Alphabet x Alphabet and T=S!. Then T>0. For any finite block sequence whose first n+1 edges are actual descent steps, every j with S<=j and j+T<n has the same left and right signed displacement at edges j+1 and j+T+1. Pigeonhole gives a state period at most S, and divisibility by S! makes T a common period; no infinite chain is appended to the supplied finite path.

**Theorem 1.2 (Every actual block length belongs to one finite coefficient family).**

$$\forall Delta \in \operatorname{Finset}\left(Alphabet\right),\; \exists C \in \operatorname{Finset}\left(\operatorname{Prod}\left(\mathbb{Z}, \mathbb{Z}, \mathbb{N}\right)\right),\; (\forall abc \in \operatorname{members}\left(C\right),\; 0 < \operatorname{third}\left(abc\right)) \land (\forall first \in \mathbb{N},\; \forall last \in \mathbb{N},\; (\operatorname{IsMaximalDeltaInterval}\left(Delta, w, first, last\right)) \Rightarrow (\exists abc \in \operatorname{members}\left(C\right),\; \exists m \in \mathbb{N},\; \operatorname{third}\left(abc\right) \cdot \left(last + 1 - first\right) = \operatorname{first}\left(abc\right) \cdot P^{m} + \operatorname{second}\left(abc\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/FinitePathDisplacements.exists_finite_actual_maximal_block_coefficient_families` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

For every finite letter set Delta, one finite set C of triples (a,b,c) is chosen before first and last. Every triple has c>0. For every actual maximal Delta interval [first,last], some triple in C and m in N satisfy c*(last+1-first)=a*P^m+b in the integers. The construction sets Q=P^q, T=(card(Alphabet x Alphabet))!, and A=Q^T. Short path lengths form a finite set. Longer paths split after a bounded prefix into T-step chunks; periodic signed corrections turn the length recurrence into an affine geometric progression with denominator A-1. Constant families cover bounded paths. Membership asserts containment only, not converse realization of every triple or exponent.

## References

- Truth anchor: `D5/S1/Recurrence/Raney/FinitePathDisplacements.exists_bounded_root_and_finite_path_displacements`
- Truth anchor: `D5/S1/Recurrence/Raney/FinitePathDisplacements.exists_finite_actual_maximal_block_coefficient_families`
- Dependency: [D5/S1/Recurrence/Raney/BoundaryPivotTransport](BoundaryPivotTransport.md)
