# Fixed-Base Tolerance Is Not a Group

## Abstract

Fixed-base semantic tolerance contains the identity but need not be closed under composition.

**Definition 1.1 (Partial monoid action).**

Lean statement: `D5/S0/Naming/ToleranceNonGroup.PartialAction`

*Formalization.* `D5/S0/Naming/ToleranceNonGroup.PartialAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A partial action assigns each monoid element and sentence an optional moved sentence. The identity is defined everywhere, and multiplication is exactly sequential optional composition through Option.bind.

**Definition 1.2 (Fixed-base semantic tolerance set).**

$$T_{\varepsilon}(s) = \{p \mid \exists sPrime, \operatorname{act}(p,s) = \operatorname{some}(sPrime) \land d(\sigma(sPrime), \sigma(s)) \leq \varepsilon\}$$

*Formalization.* `D5/S0/Naming/ToleranceNonGroup.toleranceSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A transformation is tolerated at a fixed base sentence s exactly when its partial action is defined there and the semantic displacement from s is at most epsilon.

**Theorem 1.3 (Fixed-base tolerance contains the identity but is not composition-closed).**

$$0 \leq \varepsilon \Rightarrow 1 \in T_{\varepsilon}(s)\\\land \exists \pi_{1}\in \operatorname{Perm}(\operatorname{Fin}(3)), \pi_{2}\in \operatorname{Perm}(\operatorname{Fin}(3)), \operatorname{IsCompositionCounterexample}(\operatorname{permutationAction}(\operatorname{Fin}(3)), \operatorname{sentenceMeaning}, 0, \operatorname{abc}, \pi_{1}, \pi_{2})\\\land \forall \pi_{1}\in P, \pi_{2}\in P, s_{1}\in S, s_{2}\in S, [\pi_{1}\in T_{\varepsilon}(s) \land \pi_{2}\in T_{\varepsilon}(s)\\\land \operatorname{act}(\pi_{1}, s) = \operatorname{some}(s_{1})\\\land \operatorname{act}(\pi_{2}, s_{1}) = \operatorname{some}(s_{2})] \Rightarrow [\operatorname{act}(\pi_{2}*\pi_{1}, s) = \operatorname{some}(s_{2})\\\land d(\sigma(s_{2}), \sigma(s)) \leq d(\sigma(s_{2}), \sigma(s_{1})) + \varepsilon\\\land \exists baseMoved, \operatorname{act}(\pi_{2}, s) = \operatorname{some}(baseMoved) \land d(\sigma(baseMoved), \sigma(s)) \leq \varepsilon]$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/ToleranceNonGroup.tolerance_non_group` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Clause (i): for every partial monoid action, meaning map, base sentence, and nonnegative epsilon, the everywhere-defined identity belongs to the fixed-base tolerance set.

Clause (ii): the total permutation action on three positions supplies a concrete special case. Swapping positions 2 and 3 sends ABC to ACB, swapping positions 1 and 2 sends ABC to BAC, and applying the second swap after the first sends ACB to CAB. The meanings of ABC, ACB, and BAC are zero, while CAB has meaning one. At epsilon zero both nontrivial swaps are tolerated at ABC, but their composite is not, so the nonempty tolerance set is not closed under composition.

Clause (iii): whenever the first action, the intermediate second action, and the composite are defined, the metric triangle inequality bounds the composite displacement by d(sigma(s2), sigma(s1)) + epsilon. Membership of the second transformation in the tolerance set controls only its separate action at the original sentence s; it gives no prior bound on its displacement at the moved sentence s1. The Lean conclusion retains both facts explicitly.

Repository and pinned-mathlib searches found no matching partial-action tolerance theorem. Loogle returned zero declarations named PartialAction. GitHub code search required authentication, LeanSearch GET probes were unavailable, and grep.app was rate-limited. The proof reuses mathlib's metric triangle inequality; the explicit finite permutation witness is checked directly.

## References

- Truth anchor: `D5/S0/Naming/ToleranceNonGroup.PartialAction`
- Truth anchor: `D5/S0/Naming/ToleranceNonGroup.toleranceSet`
- Truth anchor: `D5/S0/Naming/ToleranceNonGroup.tolerance_non_group`
