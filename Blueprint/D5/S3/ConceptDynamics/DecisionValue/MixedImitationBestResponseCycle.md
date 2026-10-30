# A persistent cycle in mixed imitation and best-response dynamics

## Abstract

A four-agent coordination network has a persistent mixed imitation and best-response trajectory that never reaches equilibrium.

**Definition 1.1 (Accumulated utility).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(adj: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(pay: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\mathbb{R}\right)\right)\right)\right), \left(\forall \left(x: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right), \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.utility}\left(adj, pay, x, i\right) = \sum_{j \in \operatorname{Finset.filter}\left(adj\left(i\right), \left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)} \left(pay\left(i, x\left(i\right), x\left(j\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.utility` (`✓ std3`).

*Citation.* Nazanin Hasheminejad; Pouria Ramazi (2023). *Equilibration of Coordinating Imitation and Best-Response Dynamics*. DOI: [10.1109/LCSYS.2023.3292049](https://doi.org/10.1109/LCSYS.2023.3292049). URL: <https://arxiv.org/abs/2306.03243v3>.

*Commentary.*

For n agents, adj specifies the neighbours and pay gives each agent's real payoff for a pair of Boolean strategies. The strategy false represents A and true represents B. Utility is the sum of pay i (x i) (x j) over all neighbours j of i; an empty neighbourhood contributes zero. This is the accumulated utility in Section 2, lines 134–148 of the v3 TeX source.

**Definition 1.2 (A strategy among the highest-earning neighbours).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(adj: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(pay: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\mathbb{R}\right)\right)\right)\right), \left(\forall \left(x: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right), \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(s: \operatorname{Bool}\right), \left(\left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.hasMaximizer}\left(adj, pay, x, i, s\right)\right) \Leftrightarrow \left(\exists \left(j: \operatorname{Fin}\left(n\right)\right), \left(\left(adj\left(i, j\right)\right) \land \left(\left(x\left(j\right) = s\right) \land \left(\forall \left(k: \operatorname{Fin}\left(n\right)\right), \left(\left(adj\left(i, k\right)\right) \to \left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.utility}\left(adj, pay, x, k\right) \le \operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.utility}\left(adj, pay, x, j\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.hasMaximizer` (`✓ std3`).

*Citation.* Nazanin Hasheminejad; Pouria Ramazi (2023). *Equilibration of Coordinating Imitation and Best-Response Dynamics*. DOI: [10.1109/LCSYS.2023.3292049](https://doi.org/10.1109/LCSYS.2023.3292049). URL: <https://arxiv.org/abs/2306.03243v3>.

*Commentary.*

The predicate says that a neighbour j uses s and has utility at least that of every neighbour k of i. Utilities are those of the neighbours themselves in the unchanged state x. This expresses the maximization in the imitation rule at lines 149–155. Both strategies can have maximizing neighbours; with no neighbours neither strategy does.

**Definition 1.3 (The active agent's new strategy).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(adj: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(imitator: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right), \left(\forall \left(pay: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\mathbb{R}\right)\right)\right)\right), \left(\forall \left(x: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right), \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.update}\left(adj, imitator, pay, x, i\right) = \operatorname{ite}\left(imitator\left(i\right) = \operatorname{Bool.true}, \operatorname{ite}\left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.hasMaximizer}\left(adj, pay, x, i, \operatorname{Bool.false}\right), \operatorname{ite}\left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.hasMaximizer}\left(adj, pay, x, i, \operatorname{Bool.true}\right), x\left(i\right), \operatorname{Bool.false}\right), \operatorname{ite}\left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.hasMaximizer}\left(adj, pay, x, i, \operatorname{Bool.true}\right), \operatorname{Bool.true}, x\left(i\right)\right)\right), \operatorname{ite}\left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.utility}\left(adj, pay, \operatorname{Function.update}\left(x, i, \operatorname{Bool.false}\right), i\right) < \operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.utility}\left(adj, pay, \operatorname{Function.update}\left(x, i, \operatorname{Bool.true}\right), i\right), \operatorname{Bool.true}, \operatorname{ite}\left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.utility}\left(adj, pay, \operatorname{Function.update}\left(x, i, \operatorname{Bool.true}\right), i\right) < \operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.utility}\left(adj, pay, \operatorname{Function.update}\left(x, i, \operatorname{Bool.false}\right), i\right), \operatorname{Bool.false}, x\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.update` (`✓ std3`).

*Citation.* Nazanin Hasheminejad; Pouria Ramazi (2023). *Equilibration of Coordinating Imitation and Best-Response Dynamics*. DOI: [10.1109/LCSYS.2023.3292049](https://doi.org/10.1109/LCSYS.2023.3292049). URL: <https://arxiv.org/abs/2306.03243v3>.

*Commentary.*

An agent with imitator i equal to true copies the strategy of its highest-earning neighbours when that strategy is unique. If both strategies occur among those neighbours, it retains x i. An agent with imitator i equal to false compares its own utilities after replacing its strategy by false and by true, takes the strictly better strategy, and retains x i when the utilities are equal. These are the rules and tie convention of lines 149–167. As a repository totalization convention, an imitator with no neighbours retains x i; the cited argmax rule leaves this case unspecified.

**Definition 1.4 (One asynchronous update).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(adj: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(imitator: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right), \left(\forall \left(pay: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\mathbb{R}\right)\right)\right)\right), \left(\forall \left(x: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right), \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.step}\left(adj, imitator, pay, x, i\right) = \operatorname{Function.update}\left(x, i, \operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.update}\left(adj, imitator, pay, x, i\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.step` (`✓ std3`).

*Citation.* Nazanin Hasheminejad; Pouria Ramazi (2023). *Equilibration of Coordinating Imitation and Best-Response Dynamics*. DOI: [10.1109/LCSYS.2023.3292049](https://doi.org/10.1109/LCSYS.2023.3292049). URL: <https://arxiv.org/abs/2306.03243v3>.

*Commentary.*

Only coordinate i changes, to the value prescribed by update. Every other coordinate remains equal to its value in x. This is the asynchronous convention at lines 150–151.

**Definition 1.5 (The trajectory of an activation sequence).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(adj: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(imitator: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right), \left(\forall \left(pay: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\mathbb{R}\right)\right)\right)\right), \left(\forall \left(x: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right), \left(\forall \left(a: \left(\mathbb{N}\right) \to \left(\operatorname{Fin}\left(n\right)\right)\right), \left(\left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.traj}\left(adj, imitator, pay, x, a, \left(0: \mathbb{N}\right)\right) = x\right) \land \left(\forall \left(t: \mathbb{N}\right), \left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.traj}\left(adj, imitator, pay, x, a, t + \left(1: \mathbb{N}\right)\right) = \operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.step}\left(adj, imitator, pay, \operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.traj}\left(adj, imitator, pay, x, a, t\right), a\left(t\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.traj` (`✓ std3`).

*Citation.* Nazanin Hasheminejad; Pouria Ramazi (2023). *Equilibration of Coordinating Imitation and Best-Response Dynamics*. DOI: [10.1109/LCSYS.2023.3292049](https://doi.org/10.1109/LCSYS.2023.3292049). URL: <https://arxiv.org/abs/2306.03243v3>.

*Commentary.*

The trajectory begins at x. At time t, the sequence a selects the active agent, and one asynchronous step produces the state at time t + 1. This recursion expresses the decision-making dynamics described at lines 150–167 and 206.

**Definition 1.6 (Equilibrium under every activation sequence).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(adj: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\forall \left(imitator: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right), \left(\forall \left(pay: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\mathbb{R}\right)\right)\right)\right), \left(\forall \left(x: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right), \left(\left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.IsEquilibrium}\left(adj, imitator, pay, x\right)\right) \Leftrightarrow \left(\forall \left(a: \left(\mathbb{N}\right) \to \left(\operatorname{Fin}\left(n\right)\right)\right), \left(\forall \left(t: \mathbb{N}\right), \left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.traj}\left(adj, imitator, pay, x, a, t\right) = x\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.IsEquilibrium` (`✓ std3`).

*Citation.* Nazanin Hasheminejad; Pouria Ramazi (2023). *Equilibration of Coordinating Imitation and Best-Response Dynamics*. DOI: [10.1109/LCSYS.2023.3292049](https://doi.org/10.1109/LCSYS.2023.3292049). URL: <https://arxiv.org/abs/2306.03243v3>.

*Commentary.*

A state is an equilibrium when every activation sequence leaves it fixed at every natural time. The sequence in this definition is arbitrary, without a persistence restriction, as in lines 207–215.

**Definition 1.7 (Arbitrarily late activations of every agent).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(a: \left(\mathbb{N}\right) \to \left(\operatorname{Fin}\left(n\right)\right)\right), \left(\left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.IsPersistent}\left(a\right)\right) \Leftrightarrow \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(t: \mathbb{N}\right), \left(\exists \left(u: \mathbb{N}\right), \left(\left(t \le u\right) \land \left(a\left(u\right) = i\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.IsPersistent` (`✓ std3`).

*Citation.* Nazanin Hasheminejad; Pouria Ramazi (2023). *Equilibration of Coordinating Imitation and Best-Response Dynamics*. DOI: [10.1109/LCSYS.2023.3292049](https://doi.org/10.1109/LCSYS.2023.3292049). URL: <https://arxiv.org/abs/2306.03243v3>.

*Commentary.*

For every agent i and every natural time t, some time u at least t activates i. Thus every agent is activated infinitely often, the persistence condition at lines 217–218.

**Definition 1.8 (Universal equilibration on finite undirected graphs).**

$$\left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.claim}\right) \Leftrightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(adj: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Prop}\right)\right)\right), \left(\left(\operatorname{Symmetric}\left(adj\right)\right) \to \left(\left(\operatorname{Std.Irrefl}\left(adj\right)\right) \to \left(\forall \left(imitator: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right), \left(\forall \left(pay: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\mathbb{R}\right)\right)\right)\right), \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{max}\left(pay\left(i, \operatorname{Bool.true}, \operatorname{Bool.false}\right), pay\left(i, \operatorname{Bool.false}, \operatorname{Bool.true}\right)\right) < \operatorname{min}\left(pay\left(i, \operatorname{Bool.false}, \operatorname{Bool.false}\right), pay\left(i, \operatorname{Bool.true}, \operatorname{Bool.true}\right)\right)\right)\right) \to \left(\forall \left(x: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right), \left(\forall \left(a: \left(\mathbb{N}\right) \to \left(\operatorname{Fin}\left(n\right)\right)\right), \left(\left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.IsPersistent}\left(a\right)\right) \to \left(\exists \left(t: \mathbb{N}\right), \left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.IsEquilibrium}\left(adj, imitator, pay, \operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.traj}\left(adj, imitator, pay, x, a, t\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nazanin Hasheminejad; Pouria Ramazi (2023). *Equilibration of Coordinating Imitation and Best-Response Dynamics*. DOI: [10.1109/LCSYS.2023.3292049](https://doi.org/10.1109/LCSYS.2023.3292049). URL: <https://arxiv.org/abs/2306.03243v3>.

*Commentary.*

For every natural n and every symmetric irreflexive adjacency relation, choose any assignment of imitation and best-response rules and any real payoffs satisfying the strict coordination inequality at every agent. The claim says that every initial state and every persistent activation sequence reach an equilibrium at some natural time. It gives the general-graph reading of the question at lines 225 and 668; it asserts no separate conclusion about dense trees or potential functions.

**Theorem 1.9 (A persistent four-agent cycle).**

$$\neg \left(\operatorname{D5.S3.ConceptDynamics.DecisionValue.MixedImitationBestResponseCycle.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.result` (`✓ std3`). ∎

*Resolves.* `Problems/hasheminejad-ramazi-2023-mixed-imitation-best-response-nonequilibration` (refuted) by `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hasheminejad-ramazi-2023-mixed-imitation-best-response-nonequilibration","declaration_gid":"D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nazanin Hasheminejad; Pouria Ramazi (2023). *Equilibration of Coordinating Imitation and Best-Response Dynamics*. DOI: [10.1109/LCSYS.2023.3292049](https://doi.org/10.1109/LCSYS.2023.3292049). URL: <https://arxiv.org/abs/2306.03243v3>.

*Commentary.*

Take four agents 0, 1, 2, 3, with edges {0,1}, {1,2}, {1,3}, {0,3}, {2,3}. Adjacency is symmetric and irreflexive. Agent 1 is a best-responder, and agents 0, 2, 3 are imitators. Their payoff quadruples (R,S,T,P), in that order, are (1,0,0,4), (3,2,2,3), (4,1,0,4), (4,3,3,4). The strict coordination inequalities reduce respectively to 0 < 1, 2 < 3, 1 < 4 and 3 < 4.

Repeat the activation block (2,0,3,1). Given any natural t, agents 0, 1, 2, 3 are activated at the respective times 4t + 1, 4t + 3, 4t and 4t + 2, all at least t, so the sequence is persistent. Its value at t + 8 equals its value at t.

Consider the eight states BABB, BABA, BBBA, BBAA, ABAA, ABAB, AAAB, AABB, with coordinates ordered 0, 1, 2, 3. Their utility vectors are respectively (4,6,4,11), (0,7,0,10), (4,8,4,9), (4,7,5,10), (1,6,5,11), (0,7,2,10), (1,8,5,9), (1,7,4,10). For these same states, agent 1's utility after choosing A is respectively 6, 7, 7, 8, 9, 8, 8, 7; after choosing B it is 9, 8, 8, 7, 6, 7, 7, 8. These values follow by summing the specified edge payoffs.

Starting from BABB, the activations at times 0 and 1 leave the state unchanged. From time 2, the next eight active agents are 3, 1, 2, 0, 3, 1, 2, 0. The utility comparisons above show that each activation takes the corresponding state in the eight-state list to the next, with AABB returning to BABB. Consequently the states at times 0, 1, 2 are BABB, and those at times 3 through 10 are BABA, BBBA, BBAA, ABAA, ABAB, AAAB, AABB, BABB.

The trajectory has period eight from time 2. For the initial equality, the states at times 10 and 2 are both BABB. For the induction step, equality of the states at t + 8 and t, together with equality of their active agents, gives equality after the same one-agent update at times t + 9 and t + 1. The shifted trajectory at times t + 2 is therefore periodic with period eight. Reducing t modulo eight shows that every state from time 2 belongs to the displayed eight-state list.

An equilibrium must be fixed by a step at every agent i: apply its defining condition at time 1 to the constant activation sequence with value i. Each state in the list is moved to a distinct next state by its designated active agent, so none is an equilibrium. The states at times 0 and 1 are also the first state in that list. Thus the trajectory is never at equilibrium. Applying the universal claim to this symmetric irreflexive network, its coordinating payoffs, initial state and persistent sequence would give a time when this very trajectory is at equilibrium, a contradiction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.IsEquilibrium`
- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.IsPersistent`
- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.claim`
- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.hasMaximizer`
- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.result`
- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.step`
- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.traj`
- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.update`
- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.utility`
