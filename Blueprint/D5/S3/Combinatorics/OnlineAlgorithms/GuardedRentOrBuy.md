# The guarded repeated rent-or-buy rule

## Abstract

A guarded deterministic threshold rule for repeated rent-or-buy.

**Definition 1.1 (State before a new increment is billed).**

$$\mathrm{structure} \mathrm{State} \mathrm{where} \{\mathrm{carry}: \mathbb{R}, \mathrm{acc}: \mathbb{R}, \mathrm{previous}: \mathrm{Option}(\mathbb{R}), \mathrm{ordinarySeen}: \mathrm{Bool}, \mathrm{dropSeen}: \mathrm{Bool}\}$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real carry is the history left after the previous action. The real accumulator is the rent paid since the last reset. The state also stores the optional previous increment and two flags for whether an ordinary crossing or a strict drop has occurred.

**Definition 1.2 (Initial state).**

$$\mathrm{initial}=\{\mathrm{carry} := 0, \mathrm{acc} := 0, \mathrm{previous} := \mathrm{none}, \mathrm{ordinarySeen} := \mathrm{false}, \mathrm{dropSeen} := \mathrm{false}\}$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.initial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both real fields are zero. The previous increment is absent and both flags are false.

**Definition 1.3 (Ordinary threshold crossing).**

$$\forall (K a: \mathbb{R})(s: State), crossing(K, s, a)\Leftrightarrow K\le acc(s)+(carry(s)+a)$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.crossing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A crossing occurs when the accumulator plus the carry plus the new increment reaches or exceeds the reset price.

**Definition 1.4 (Strict decrease in the visible increments).**

$$\forall (s: State)(a: \mathbb{R}), drop(s, a)\Leftrightarrow \exists (p: \mathbb{R}), previous(s)=some(p)\land a<p$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.drop` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A drop occurs if a previous increment exists and the newly visible increment is strictly smaller.

**Definition 1.5 (Reset decision).**

$$\forall (K a: \mathbb{R})(s: State), reset(K, s, a)=decide(crossing(K, s, a)\lor (drop(s, a)\land ordinarySeen(s)=true\land dropSeen(s)=false))$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.reset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reset at a crossing, or at the first strict drop if an ordinary crossing occurred on an earlier call.

**Definition 1.6 (State after the billed call).**

$$\forall (K a: \mathbb{R})(s: \mathrm{State}), \mathrm{advance}(K, s, a)= \{\mathrm{carry} := (\mathrm{if} \mathrm{reset}(K, s, a)=\mathrm{true} \mathrm{then} 0 \mathrm{else} s.\mathrm{carry}+a), \mathrm{acc} := (\mathrm{if} \mathrm{reset}(K, s, a)=\mathrm{true} \mathrm{then} 0 \mathrm{else} s.\mathrm{acc}+(s.\mathrm{carry}+a)), \mathrm{previous} := \mathrm{some}(a), \mathrm{ordinarySeen} := s.\mathrm{ordinarySeen} || \mathrm{decide}(\mathrm{crossing}(K, s, a)), \mathrm{dropSeen} := s.\mathrm{dropSeen} || \mathrm{decide}(\mathrm{drop}(s, a))\}$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.advance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a reset, clear the carry and accumulator. Otherwise add the new increment to the carry and add that rent to the accumulator. Store the increment and update each flag by disjunction with the corresponding test on this call. A simultaneous drop and crossing counts as an ordinary crossing.

**Definition 1.7 (Comparator carry after the action).**

$$\forall (o a: \mathbb{R})(r: Bool), nextCarry(o, a, r)=(\mathrm{if} r=\mathrm{true} \mathrm{then} 0 \mathrm{else} o+a)$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.nextCarry` (`✓ std3`).

*Citation.* Vasco Schiavo (2026). *A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy*. URL: <https://arxiv.org/abs/2611.06955v1>.

*Commentary.*

The carry is zero after a reset and is the incoming carry plus the visible increment otherwise.

**Definition 1.8 (Bill on one call).**

$$\forall (K o a: \mathbb{R})(r: Bool), bill(K, o, a, r)=o+a+(\mathrm{if} r=\mathrm{true} \mathrm{then} K \mathrm{else} 0)$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.bill` (`✓ std3`).

*Citation.* Vasco Schiavo (2026). *A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy*. URL: <https://arxiv.org/abs/2611.06955v1>.

*Commentary.*

Charge incoming carry plus the visible increment on every call. Add the reset price exactly when the action resets.

**Definition 1.9 (Cost of a schedule from an incoming carry).**

$$\forall (K o a: \mathbb{R})(r: Bool)(xs: List(\mathbb{R}\times Bool)), comparatorCost(K, o, [])=0\land comparatorCost(K, o, cons((a, r), xs))=bill(K, o, a, r)+comparatorCost(K, nextCarry(o, a, r), xs)$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.comparatorCost` (`✓ std3`).

*Citation.* Vasco Schiavo (2026). *A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy*. URL: <https://arxiv.org/abs/2611.06955v1>.

*Commentary.*

The empty list has cost zero. For each increment and action pair, add the bill and continue from the carry given by that action.

**Definition 1.10 (Cost of the guarded rule from a state).**

$$\forall (K a: \mathbb{R})(s: State)(xs: List(\mathbb{R})), policyCost(K, s, [])=0\land policyCost(K, s, cons(a, xs))=bill(K, carry(s), a, reset(K, s, a))+policyCost(K, advance(K, s, a), xs)$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.policyCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty list has cost zero. For each increment, add the bill for the rule's reset decision, then continue with the updated state.

**Definition 1.11 (Horizon-blind decision on a visible prefix).**

$$\forall (K a: \mathbb{R})(xs: List(\mathbb{R})), prefixRule(K, [])=false\land prefixRule(K, xs ++ [a])=reset(K, \mathrm{xs}.\mathrm{foldl}(advance(K), \mathrm{initial}), a)$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.prefixRule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty prefix chooses no reset. For a nonempty prefix, replay every increment before its last entry from the initial state. Use the resulting state with the last entry to choose the reset.

**Theorem 1.12 (The first call does not reset).**

$$\forall (K: \mathbb{R}), prefixRule(K, [])=false$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.prefixRule_nil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Call one has no visible increment. Its decision is the value of the prefix rule at the empty list.

**Definition 1.13 (Increment and decision trace).**

$$\forall (K a: \mathbb{R})(s: State)(xs: List(\mathbb{R})), scheduled(K, s, [])=[]\land scheduled(K, s, cons(a, xs))=cons((a, reset(K, s, a)), scheduled(K, advance(K, s, a), xs))$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.scheduled` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Produce an empty trace on an empty list. Otherwise pair the first increment with the current reset decision and compute the remaining trace from the updated state.

**Theorem 1.14 (From the initial state only a crossing resets).**

$$\forall (K a: \mathbb{R}), reset(K, initial, a)=decide(crossing(K, initial, a))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.ordinary_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial state has no previous increment and has never crossed the threshold.

**Theorem 1.15 (The trace has the rule's cost).**

$$\forall (K: \mathbb{R})(s: State)(xs: List(\mathbb{R})), comparatorCost(K, carry(s), scheduled(K, s, xs))=policyCost(K, s, xs)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.scheduled_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induct on the list. Each recursive bill uses the same decision and carry as the rule.

**Theorem 1.16 (Each recorded decision uses exactly its visible prefix).**

$$\forall (K a: \mathbb{R})(seen tail: \mathrm{List}(\mathbb{R}))(i: \mathbb{N})(r: \mathrm{Bool}), \mathrm{let} \mathrm{trace} := \mathrm{scheduled}(K, \mathrm{seen}.\mathrm{foldl}(advance(K), \mathrm{initial}), \mathrm{tail}); (\exists (j: \mathrm{Fin}(\mathrm{trace}.\mathrm{length})), j.\mathrm{val}=i\land \mathrm{trace}.\mathrm{get}(j)=(a, r))\Rightarrow \mathrm{prefixRule}(K, \mathrm{seen} ++ \mathrm{tail}.\mathrm{take}(i+1))=r$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.scheduled_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bounded index in the display expresses the successful optional lookup in Lean. Induct on the unprocessed list. At the first index the decision is the one computed from the seen prefix and the new entry. For a later index, move the head to the seen prefix and advance the fold by that entry.

**Theorem 1.17 (Cycle accounting persists through a comparator action).**

$$\forall (K e A o q a: \mathbb{R})(r: Bool), (0\le K\land e\le A\land 0\le o\land (e+K\le q\lor (A\le q\land e\le o)))\Rightarrow (e+a+K\le q+bill(K, o, a, r)\lor (A+(e+a)\le q+bill(K, o, a, r)\land e+a\le nextCarry(o, a, r)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.billed_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let e be the rule carry, A its accumulated rent, o the comparator carry and q the comparator's billed cost in the unfinished cycle. If q is at least e + K, the next bill extends this cost lower bound to include the new increment. A comparator reset also establishes the updated lower bound. In the other alternative, the updated comparator carry and cost bound the rule's carry and accumulated rent, respectively.

**Theorem 1.18 (Factor three against every comparator trace).**

$$\forall (K: \mathbb{R})(steps: List(\mathbb{R}\times Bool))(first: Bool), (0<K\land (\forall (p: \mathbb{R}\times Bool), p\in steps\Rightarrow 0\le p.1))\Rightarrow comparatorCost(K, 0, scheduled(K, initial, \mathrm{steps}.\mathrm{map}(\mathrm{Prod}.\mathrm{fst})))\le 3\cdot (bill(K, 0, 0, first)+comparatorCost(K, 0, steps))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.factor_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an ordinary crossing, the comparator's total cost over the cycle is at least K. The comparison reserves one reset price after a crossing and spends it at the first later drop if that drop forces a reset. The invariant includes unfinished cycles, so it applies when a session ends after any bill, including when the comparator cost is zero.

## References

- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.State`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.advance`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.bill`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.billed_cycle`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.comparatorCost`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.crossing`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.drop`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.factor_three`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.initial`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.nextCarry`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.ordinary_initial`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.policyCost`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.prefixRule`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.prefixRule_nil`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.reset`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.scheduled`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.scheduled_cost`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.scheduled_prefix`
