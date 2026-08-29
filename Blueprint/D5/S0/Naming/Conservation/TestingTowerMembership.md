# Testing Tower Membership

## Abstract

Finite tables and program codes admit a primary height with finite sublevels.

**Definition 1.1 (Names are finite tables or program codes).**

$$\forall O: \operatorname{Type}, \operatorname{TestingName}\left(O\right) = \operatorname{Sum}\left(\sigma_{S: \operatorname{Finset}\left(\mathbb{N}\right)} (S \to O), \mathbb{N}\right).$$

*Formalization.* `D5/S0/Naming/Conservation/TestingTowerMembership.TestingName` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A name is either a function on a self-selected finite support or a natural-number code for a program-based test.

**Lemma 1.2 (Binary description length supplies the primary filtration).**

$$\begin{gathered}\forall O: \operatorname{Type},\\{}\forall code: \operatorname{TestingName}\left(O\right) \to \operatorname{List}\left(Bool\right), \forall hC: \operatorname{TestingName}\left(O\right) \to \mathbb{N},\\{}\operatorname{Injective}\left(code\right) \Rightarrow \exists i: Bool, \forall Q: \mathbb{N},\\{}\operatorname{Finite}\left(\left\{\operatorname{ite}\left(i, \operatorname{hC}\left(a\right), \operatorname{length}\left(\operatorname{code}\left(a\right)\right)\right) \leq Q \mid a \in \operatorname{TestingName}\left(O\right)\right\}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/Conservation/TestingTowerMembership.testing_tower_is_multi_filtration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

TestingName O is the disjoint sum of finite functional tables on self-selected finite supports and natural-number program codes. The theorem keeps this source carrier public rather than replacing it with a prepackaged naming-system witness.

An injective self-delimiting Boolean code is the algorithmic height, while execution cost is an arbitrary secondary height. Choosing the code coordinate reduces every bounded sublevel to the injective preimage of the finite set of Boolean lists of bounded length.

Repository body-shape searches found only the raw-program special case. Pinned Mathlib supplies List.finite_length_le, which is applied directly to establish the finite-level-set clause.

## References

- Truth anchor: `D5/S0/Naming/Conservation/TestingTowerMembership.TestingName`
- Truth anchor: `D5/S0/Naming/Conservation/TestingTowerMembership.testing_tower_is_multi_filtration`
