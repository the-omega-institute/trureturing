# Goal Words with an Independent Rank and Cost Budget

## Abstract

A termination rank and a separate potential construct a goal word with state-dependent charges.

**Definition 1.1 (Charges are evaluated at the states actually reached).**

$$\begin{gathered}\forall X: \operatorname{Type}(u), A: \operatorname{Type}(v),\\{}\forall t: X \to A \to X, c: X \to A \to \mathbb{N}, s: X,\\{}\operatorname{cost}(t, c, s, \operatorname{nil}()) = 0 \land \forall a: A, w: \operatorname{List}(A),\\{}\operatorname{cost}(t, c, s, \operatorname{cons}(a, w)) = \operatorname{c}(s, a) + \operatorname{cost}(t, c, \operatorname{t}(s, a), w).\end{gathered}$$

*Formalization.* `D5/S1/Words/RankedCostDescent.wordCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let X and A be state and letter types in independent universes, and let t be the transition and c its natural-valued charge. The notation run(t,w,s) means the native left fold w.foldl t s. The empty word is nil, and cons(a,w) places a before w. The function cost(t,c,s,w) is wordCost t c s w: after paying c(s,a), the remaining charges are evaluated starting at t(s,a), rather than at the original state. Costs may be zero.

**Theorem 1.2 (Rank ensures termination while potential pays the charges).**

$$\begin{gathered}\forall X: \operatorname{Type}(u), A: \operatorname{Type}(v),\\{}\forall t: X \to A \to X, G: X \to Prop,\\{}R, V: X \to \mathbb{N}, c: X \to A \to \mathbb{N},\\{}x: X,\\{}(\forall s: X, \operatorname{not}(\operatorname{G}(s)) \Rightarrow \exists a: \operatorname{List}(A),\\{}\operatorname{R}(\operatorname{run}(t, a, s)) < \operatorname{R}(s) \land \operatorname{cost}(t, c, s, a) + \operatorname{V}(\operatorname{run}(t, a, s)) \leq \operatorname{V}(s))\\{}\Rightarrow \exists w: \operatorname{List}(A),\\{}\operatorname{G}(\operatorname{run}(t, w, x)) \land \operatorname{cost}(t, c, x, w) + \operatorname{V}(\operatorname{run}(t, w, x)) \leq \operatorname{V}(x).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RankedCostDescent.exists_goal_word_cost_add_potential_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary goal predicate G, let R be a natural-valued termination rank and V a separate natural-valued budget potential. At every state s outside G, assume a finite word a reaches a strictly lower rank and that its actual accumulated charge plus the endpoint potential is at most V(s). Then every starting state x admits a word reaching G with total charge plus final potential at most V(x). No finiteness, nonemptiness or decidable equality is required of either type. The endpoint potential may be positive, and zero-cost progress is allowed even when V is constant.

Strong induction on R(s) constructs the word. At a goal, use nil. Otherwise choose the local word a, recursively construct a goal suffix b at its lower-rank endpoint, and concatenate a followed by b. Cost concatenation uses the state reached after a as the suffix's starting state. The two budget inequalities cancel the intermediate potential. Only local endpoints must decrease in rank; no rank, potential or goal condition is imposed on their intermediate states.

A preparation-and-execution system has states (n,ready), goal n=0, potential n+5 and rank 2n plus one when ready is false. Preparation changes (n,false) to (n,true) at zero charge. Execution changes (n,true) to (n-1,false) at charge one. For n>0 both operations decrease rank and preserve the paid budget. Thus every start reaches the goal with total charge plus the residual five bounded by its initial potential. From (3,false), a preparation followed by execution has charge one and reaches (2,false); preparation alone leaves the potential unchanged.

For countdown on natural numbers, take R(n)=n, V(n)=2n+5 and charge one at even states and two at odd states. Every nonterminal predecessor step is affordable, so the theorem bounds the actual state-dependent total charge and retains a final potential of five. For example, the two steps from three through two to one cost three. A separate zero-charge countdown with constant potential seven shows that progress does not need to consume budget.

When every charge is one, cost equals word length. Setting R=V recovers the potential-drop word bound, including its independently polymorphic parameters and empty alphabet. This also gives the finite-uncertainty application on natural numbers: predecessor image decreases the maximum together with zero until cardinality is at most one. Cardinality itself may plateau, as in {0,2} to {0,1}. This application uses an infinite ambient state space.

Strict rank progress is essential: an identity transition with zero charges and an always-false goal satisfies local affordability but never reaches the goal. The theorem asserts existence, without a bound on finding local words, total word length when zero charges are allowed, shortest-word optimality or polynomial runtime. Native controller realization, legal operations, initialization and correct output need their own conditions; the polynomial native-controller claim of Section 21.5 in the capacity-coherence volume is not covered. The accounting is the standard potential method discussed in Library/Computability/tarjan1985amortized.md; no literature novelty is claimed.

## References

- Truth anchor: `D5/S1/Words/RankedCostDescent.exists_goal_word_cost_add_potential_le`
- Truth anchor: `D5/S1/Words/RankedCostDescent.wordCost`
