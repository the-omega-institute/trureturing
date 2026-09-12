# Profitable Deviations towards Antagonistic Tie-Breaking

## Abstract

Both players can gain by changing friendly to antagonistic tie-breaking.

Bhagat, Kulkarni, Larsson and Murali, "Tie-breaking in self interest cumulative subtraction games", arXiv:2510.24280v2 (20 January 2026), Section 6, Problem 6 asks: "Is it true that no player can have a positive discrepancy by going from AvF or FvA to AvA?" The answer is no. The authors' own sentence immediately before the problem reads "Experimental results point towards that this cannot happen if deviating towards AvA"; their experiments pointed the other way.

For subtraction set {7,12,13,38,50}, at heap 122 the AvF and AvA outcomes are (64,57) and (64,58), so Bob, the second player, gains by switching his own convention from friendly to antagonistic. At heap 172 the FvA and AvA outcomes are (107,64) and (108,64), so Alice, the opening player, gains by the same change. Problem 6 is a disjunction over AvF and FvA, and both disjuncts are refuted.

Nothing about Conjecture 4, the FvF-to-AvA statement, is established. There is no classification of such subtraction sets and no claim that these are the only or the smallest witnesses. The paper supplies the question and Definition 2; the declarations are repository constructions. Nat denotes the natural numbers, List(Nat) a finite list, and .1 and .2 are pair projections.

**Definition 1.1 (Mover-relative conventions).**

$$Convention = Bool \times Bool$$

*Formalization.* `D5/S0/Certificates/SelfInterestConventionDeviationGain.Convention` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Boolean records whether a player is antagonistic. Component 1 belongs to the mover, and component 2 belongs to the opponent.

**Definition 1.2 (Friendly versus friendly).**

$$FvF = (false, false)$$

*Formalization.* `D5/S0/Certificates/SelfInterestConventionDeviationGain.FvF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both players use friendly tie-breaking.

**Definition 1.3 (Antagonistic versus friendly).**

$$AvF = (true, false)$$

*Formalization.* `D5/S0/Certificates/SelfInterestConventionDeviationGain.AvF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mover is antagonistic and the opponent is friendly.

**Definition 1.4 (Friendly versus antagonistic).**

$$FvA = (false, true)$$

*Formalization.* `D5/S0/Certificates/SelfInterestConventionDeviationGain.FvA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mover is friendly and the opponent is antagonistic.

**Definition 1.5 (Antagonistic versus antagonistic).**

$$AvA = (true, true)$$

*Formalization.* `D5/S0/Certificates/SelfInterestConventionDeviationGain.AvA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both players use antagonistic tie-breaking.

**Definition 1.6 (Role reversal at every move).**

$$\forall convention: Convention, \operatorname{dual}(convention) = ((convention).2, (convention).1)$$

*Formalization.* `D5/S0/Certificates/SelfInterestConventionDeviationGain.dual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Swap the two components at every move, including moves in mixed conventions.

**Theorem 1.7 (Two role reversals restore the convention).**

$$\forall convention: Convention, \operatorname{dual}(\operatorname{dual}(convention)) = convention$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SelfInterestConventionDeviationGain.dual_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This holds for every convention without further hypotheses.

**Theorem 1.8 (Exactly the homogeneous conventions are fixed).**

$$\forall convention: Convention, \operatorname{dual}(convention) = convention \iff (convention = FvF \lor convention = AvA)$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SelfInterestConventionDeviationGain.dual_fixed_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence covers all four Boolean pairs.

**Definition 1.9 (Own total with a convention-dependent tie-break).**

$$\begin{aligned}\forall convention: Convention, \forall chosen, alternative: Nat \times Nat,\\\operatorname{Preferred}(convention, chosen, alternative) \iff (alternative).1 \leq (chosen).1 \land\\((alternative).1 = (chosen).1 \Rightarrow if (convention).1 then (chosen).2 \leq (alternative).2 else (alternative).2 \leq (chosen).2)\end{aligned}$$

*Formalization.* `D5/S0/Certificates/SelfInterestConventionDeviationGain.Preferred` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Own total is primary. On equality, an antagonistic mover minimizes the opponent's total and a friendly mover maximizes it. The Boolean conditional tests component 1 of the mover-relative convention.

**Definition 1.10 (Tabulated mover and opponent totals).**

$$\begin{aligned}\forall subtractions: \operatorname{List}(Nat), \forall convention: Convention, \forall heap: Nat,\\\operatorname{outcome}(subtractions, convention, heap) = \operatorname{readTable}(\operatorname{tabulate}(subtractions, heap+1), heap, convention)\end{aligned}$$

*Formalization.* `D5/S0/Certificates/SelfInterestConventionDeviationGain.outcome` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The result has type Nat times Nat: mover total followed by opponent total. readTable and tabulate are the module's private implementation functions. Structural tabulation stores all four conventions at each heap; a terminal position returns (0,0). The recurrence theorem proves the Definition 2 semantics, rather than assuming faithfulness of the table.

**Theorem 1.11 (Definition 2 holds for the tabulated outcome).**

$$\begin{aligned}\forall subtractions: \operatorname{List}(Nat), \forall convention: Convention, \forall heap: Nat,\\((\neg (\exists step \in subtractions, 0 < step \land step \leq heap)) \Rightarrow \operatorname{outcome}(subtractions, convention, heap) = (0, 0)) \land\\((\exists step \in subtractions, 0 < step \land step \leq heap) \Rightarrow\\\exists step \in subtractions, 0 < step \land step \leq heap \land\\\operatorname{outcome}(subtractions, convention, heap) = ((\operatorname{outcome}(subtractions, \operatorname{dual}(convention), heap-step)).2+step, (\operatorname{outcome}(subtractions, \operatorname{dual}(convention), heap-step)).1) \land\\\forall alternative \in subtractions, 0 < alternative \Rightarrow alternative \leq heap \Rightarrow\\\operatorname{Preferred}(convention, \operatorname{outcome}(subtractions, convention, heap), ((\operatorname{outcome}(subtractions, \operatorname{dual}(convention), heap-alternative)).2+alternative, (\operatorname{outcome}(subtractions, \operatorname{dual}(convention), heap-alternative)).1)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SelfInterestConventionDeviationGain.outcome_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both implications hold for every finite subtraction list, convention and natural heap. With no positive legal step the payoff is zero. Otherwise a positive legal step realizes the payoff, after role reversal, and that payoff is Preferred over every positive legal alternative. Heap subtraction is natural-number subtraction. The existential membership, both step bounds, the realization equality and the universally quantified optimality clause are all part of the proved statement.

**Definition 1.12 (The subtraction list).**

$$witnessSubtractions: \operatorname{List}(Nat) = [7,12,13,38,50]$$

*Formalization.* `D5/S0/Certificates/SelfInterestConventionDeviationGain.witnessSubtractions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both witnesses use this list, representing the subtraction set {7,12,13,38,50}. Only positive entries not exceeding the heap are legal. The general recurrence imposes no sorting or distinctness hypothesis.

**Theorem 1.13 (Four exact outcome pairs).**

$$\begin{aligned}\operatorname{outcome}(witnessSubtractions, AvF, 122) = (64, 57) \land\\\operatorname{outcome}(witnessSubtractions, AvA, 122) = (64, 58) \land\\\operatorname{outcome}(witnessSubtractions, FvA, 172) = (107, 64) \land\\\operatorname{outcome}(witnessSubtractions, AvA, 172) = (108, 64)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SelfInterestConventionDeviationGain.witness_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lean verifies all four equalities together using decide +kernel. These are evaluations of the tabulation whose recurrence is proved, not assumed values or outputs trusted from an external search.

**Definition 1.14 (Problem 6 as a proposition).**

$$\begin{aligned}noPositiveDiscrepancyToAvA \iff\\\forall subtractions: \operatorname{List}(Nat), \forall heap: Nat,\\(\operatorname{outcome}(subtractions, AvA, heap)).2 \leq (\operatorname{outcome}(subtractions, AvF, heap)).2 \land\\(\operatorname{outcome}(subtractions, AvA, heap)).1 \leq (\operatorname{outcome}(subtractions, FvA, heap)).1\end{aligned}$$

*Formalization.* `D5/S0/Certificates/SelfInterestConventionDeviationGain.noPositiveDiscrepancyToAvA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every subtraction list and heap, Bob's second component after AvF-to-AvA and Alice's first component after FvA-to-AvA do not exceed their values before the respective changes. Both inequalities are required.

**Theorem 1.15 (Typed refutation of Problem 6).**

$$\neg noPositiveDiscrepancyToAvA$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SelfInterestConventionDeviationGain.both_deviations_refute_no_positive_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This closed theorem negates the proposition without hypotheses. It uses both audited strict gains, for Bob at heap 122 and Alice at heap 172, to contradict the sum of the claimed upper bounds.

**Theorem 1.16 (Both changes towards AvA are profitable).**

$$\begin{aligned}(\operatorname{outcome}(witnessSubtractions, AvF, 122)).2 < (\operatorname{outcome}(witnessSubtractions, AvA, 122)).2 \land\\(\operatorname{outcome}(witnessSubtractions, FvA, 172)).1 < (\operatorname{outcome}(witnessSubtractions, AvA, 172)).1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SelfInterestConventionDeviationGain.both_deviations_profitable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are no hypotheses. Both strict inequalities are conclusions: Bob gains from 57 to 58 at heap 122, and Alice gains from 107 to 108 at heap 172. Each changes only their own friendly convention to antagonistic while the other player remains antagonistic.

## References

- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.AvA`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.AvF`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.Convention`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.FvA`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.FvF`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.Preferred`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.both_deviations_profitable`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.both_deviations_refute_no_positive_discrepancy`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.dual`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.dual_fixed_iff`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.dual_involutive`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.noPositiveDiscrepancyToAvA`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.outcome`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.outcome_recurrence`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.witnessSubtractions`
- Truth anchor: `D5/S0/Certificates/SelfInterestConventionDeviationGain.witness_values`
