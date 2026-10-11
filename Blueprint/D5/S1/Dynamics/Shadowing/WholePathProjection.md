# Whole Path Projection and Finite Prefix Diagnostics

## Abstract

A given finite hidden graph retains every whole visible path exactly when all prefixes lift; a live finite target has a bounded failure certificate.

**Definition 1.1 (A prefix includes its initial vertex).**

$$\operatorname{PrefixLift}(EH, q, a, m) \Leftrightarrow \exists b: \operatorname{Fin}(m+1) \Rightarrow H, (\forall i: \operatorname{Fin}(m), \operatorname{EH}(\operatorname{b}(\operatorname{castSucc}(i)), \operatorname{b}(\operatorname{succ}(i)))) \land \forall i: \operatorname{Fin}(m+1), \operatorname{q}(\operatorname{b}(i))=\operatorname{a}(\operatorname{val}(i))$$

*Formalization.* `D5/S1/Dynamics/Shadowing/WholePathProjection.PrefixLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For hidden vertices H, visible vertices P, hidden edges EH and labels q:H→P, PrefixLift(EH,q,a,m) requires a hidden path on Fin(m+1) matching a at every time from zero through m. The m indices of Fin m specify its consecutive edges. Thus m counts edges, not vertices. At m=0 the condition is precisely a hidden preimage of a(0); it cannot be discarded as an empty-prefix check.

**Theorem 1.2 (All prefixes of the same whole path suffice).**

$$\operatorname{Finite}(H) \land \operatorname{EdgePreserving}(q, EH, EP) \Rightarrow (\operatorname{graphLanguage}(EH, q) = \operatorname{graphLanguage}(EP, id) \Leftrightarrow \forall a\in\operatorname{graphLanguage}(EP, id), \forall m\in\mathbb{N}, \operatorname{PrefixLift}(EH, q, a, m))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/WholePathProjection.graphLanguage_eq_iff_prefix_lifts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume H is finite and q preserves directed edges from EH to EP. The hidden graph's complete label language equals graphLanguage(EP,id) if and only if every finite prefix of every complete visible path lifts. The entire old target is retained, with all starting vertices allowed. There is no finiteness or live-vertex assumption on P for this criterion.

For one fixed whole visible path a, the finite types of its hidden lifts through each time m form an inverse system under literal truncation. Mathlib's nonempty_sections_of_finite_inverse_system supplies a compatible section when each prefix lifts. Read its time-m terminal coordinate to obtain a single entire hidden path. No truncation map is assumed onto, and individual finite lifts need not have continuations. Restriction of a whole lift proves the other implication; edge preservation pays the automatic hidden-to-visible language inclusion.

The reusable contribution is the graph-specific finite-prefix functor, its truncation laws and reconstruction of a whole graph path, composed with the existing inverse-system compactness theorem. Neither a new compactness proof nor a surjectivity theorem for the bonding maps is claimed.

**Theorem 1.3 (A bounded certificate for one candidate graph).**

$$\operatorname{FiniteLiveTarget}(P, EP) \land \operatorname{Finite}(H) \land \operatorname{EdgePreserving}(q, EH, EP) \land \operatorname{graphLanguage}(EH, q) \neq \operatorname{graphLanguage}(EP, id) \Rightarrow \exists a\in\operatorname{graphLanguage}(EP, id), \exists m\le N\cdot2^{M}, \neg\operatorname{PrefixLift}(EH, q, a, m)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/WholePathProjection.exists_bounded_prefix_without_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Now assume both vertex types are finite with N=card P and M=card H, q preserves edges, and each visible vertex starts some whole visible path. If the whole projection is not onto, there is a whole visible path a and a time m≤N·2^M whose prefix through m has no hidden lift. This is at most N·2^M+1 visible vertices. Hidden seriality is unnecessary.

The initial hidden subset is q⁻¹{a(0)}. Reading the tail labels uses Mathlib's NFA stepSet and subset-construction DFA. Hidden endpoints are identified with actual finite prefix lifts. The diagnostic DFA stores Option(P×Set H): a visible vertex and hidden subset, plus an absorbing invalid-visible-edge sink. Acceptance means a nonsink empty hidden subset. A shortest accepted tail has length less than this DFA's state cardinal by Mathlib's evalFrom_split: remove its supplied nonempty loop to contradict minimality. The upstream set, product and option cardinalities give N·2^M+1 states and hence a tail of at most N·2^M labels. The visible live hypothesis extends the valid shortened tail to a whole target path.

The empty visible type makes the entire target empty, so onto is vacuous. If the hidden type is empty and the target is nonempty, failure already occurs at m=0. Live trimming of the target may supply the stated assumption while preserving every original whole path; no trimming theorem or executable graph enumeration is asserted in this module.

The Reg variation uses a visible two-vertex full graph and a hidden four-vertex graph with states (x,k), label x, and edges (x,k)→(k,k). Every visible vertex and edge has a preimage, and all hidden vertices are live. Yet each hidden visible history is constant after time one: the visible prefix 0,1,0 cannot lift. This checks that vertex or edge onto was not substituted for whole-path onto and that checking only time zero is insufficient.

The suppliers are pinned Mathlib CofilteredSystem, NFA and DFA; their compactness, subset construction and pigeonhole loop removal are reused. This formalizes the finite diagnostic in the Peng visible/hidden research continuation. It checks a supplied candidate graph. It does not prove existence of a successful candidate, a finite horizon for actual source realizability, convergence of core/control/net choices, or a solution of Peng Questions 5.1 or 5.2. No originality or open-problem resolution is claimed.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/WholePathProjection.PrefixLift`
- Truth anchor: `D5/S1/Dynamics/Shadowing/WholePathProjection.exists_bounded_prefix_without_lift`
- Truth anchor: `D5/S1/Dynamics/Shadowing/WholePathProjection.graphLanguage_eq_iff_prefix_lifts`
- Dependency: [D5/S1/Dynamics/Shadowing/FiniteObservationSofic](FiniteObservationSofic.md)
