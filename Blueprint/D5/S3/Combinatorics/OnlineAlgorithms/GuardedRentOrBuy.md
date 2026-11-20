# The guarded repeated rent-or-buy rule

## Abstract

A guarded deterministic threshold rule for repeated rent-or-buy.

**Definition 1.1 (State before a new increment is billed).**

$$State=\mathbb{R}\times \mathbb{R}\times Option(\mathbb{R})\times Bool\times Bool$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record is presented as an ordered tuple. The real carry is the history left after the previous action. The real accumulator is the rent paid since the last reset. The state also stores the optional previous increment and two flags for whether an ordinary crossing or a strict drop has occurred.

**Definition 1.2 (Initial state).**

$$initial=(0, 0, none, false, false)$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.initial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both real entries are zero. The previous increment is absent and both flags are false.

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

$$\forall (K a: \mathbb{R})(s: State), advance(K, s, a)=(choose(reset(K, s, a), 0, carry(s)+a), choose(reset(K, s, a), 0, acc(s)+(carry(s)+a)), some(a), ordinarySeen(s)\lor decide(crossing(K, s, a)), dropSeen(s)\lor decide(drop(s, a)))$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.advance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function choose selects its second argument when its first argument is true, and otherwise its third. On a reset, clear the carry and accumulator. Otherwise add the new increment to the carry and add that rent to the accumulator. Store the increment and update each flag by disjunction with the corresponding test on this call. A simultaneous drop and crossing counts as an ordinary crossing.

**Definition 1.7 (Comparator carry after the action).**

$$\forall (o a: \mathbb{R})(r: Bool), nextCarry(o, a, r)=choose(r, 0, o+a)$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.nextCarry` (`✓ std3`).

*Citation.* Vasco Schiavo (2026). *A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy*. URL: <https://arxiv.org/abs/2611.06955v1>.

*Commentary.*

The carry is zero after a reset and is the incoming carry plus the visible increment otherwise.

**Definition 1.8 (Bill on one call).**

$$\forall (K o a: \mathbb{R})(r: Bool), bill(K, o, a, r)=o+a+choose(r, K, 0)$$

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

$$\forall (K a: \mathbb{R})(xs: List(\mathbb{R})), prefixRule(K, [])=false\land prefixRule(K, append(xs, [a]))=reset(K, foldAdvance(K, initial, xs), a)$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.prefixRule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty prefix chooses no reset. The foldAdvance operation folds advance K over the list. For a nonempty prefix, replay every increment before its last entry from the initial state. Use the resulting state with the last entry to choose the reset.

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

$$\forall (K a: \mathbb{R})(seen tail: List(\mathbb{R}))(i: \mathbb{N})(r: Bool), getOptional(scheduled(K, foldAdvance(K, initial, seen), tail), i)=some((a, r))\Rightarrow prefixRule(K, append(seen, take(tail, i+1)))=r$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.scheduled_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induct on the unprocessed list. At the first index the decision is the one computed from the seen prefix and the new entry. For a later index, move the head to the seen prefix and advance the fold by that entry.

**Theorem 1.17 (Cycle accounting persists through a comparator action).**

$$\forall (K e A o q a: \mathbb{R})(r: Bool), (0\le K\land e\le A\land 0\le o\land (e+K\le q\lor (A\le q\land e\le o)))\Rightarrow (e+a+K\le q+bill(K, o, a, r)\lor (A+(e+a)\le q+bill(K, o, a, r)\land e+a\le nextCarry(o, a, r)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.billed_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let e be the rule carry, A its accumulated rent, o the comparator carry and q the comparator's billed cost in the unfinished cycle. If the comparator has already paid for the increments and a reset, its next bill covers the next increment as well. A comparator reset also establishes that alternative. Otherwise the comparator's carry and cost continue to dominate the rule's carried rent and accumulated rent.

**Theorem 1.18 (Factor three against every comparator trace).**

$$\forall (K: \mathbb{R})(steps: List(\mathbb{R}\times Bool))(first: Bool), (0<K\land (\forall (p: \mathbb{R}\times Bool), p\in steps\Rightarrow fst(p)\ge 0))\Rightarrow comparatorCost(K, 0, scheduled(K, initial, rates(steps)))\le 3\cdot (bill(K, 0, 0, first)+comparatorCost(K, 0, steps))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy.factor_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rates operation takes the first component of every step. At an ordinary crossing, the comparator has paid at least one reset price in that cycle. The comparison reserves one reset price after a crossing and spends it at the first later drop if that drop forces a reset. The invariant includes unfinished cycles, so it applies when a session ends after any bill, including when the comparator cost is zero.

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
