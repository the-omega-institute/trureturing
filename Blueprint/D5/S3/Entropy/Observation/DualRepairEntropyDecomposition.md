# Dual Repair Entropy Decomposition

## Abstract

Canonical predictive-interior and forgetting-closure quotients split conditional entropy into the two repair costs.

**Theorem 1.1 (Conditional entropy telescopes across both canonical repairs).**

$$\begin{gathered}\forall X: \operatorname{Type}, F: X \to X, R: \operatorname{Setoid}(X), mu: X \to \mathbb{R},\\{}\operatorname{Fintype}(X) \land (\forall x: X, 0 < mu(x)) \land \sum_{x: X}mu(x) = 1 \Rightarrow\\{}I := \operatorname{congruenceInterior}(F, R), C := \operatorname{congruenceClosure}(F, R),\\{}Q_{I} := \operatorname{Quotient}(\operatorname{congruenceInterior}(F, R)), Q_{R} := \operatorname{Quotient}(R),\\{}Q_{C} := \operatorname{Quotient}(\operatorname{congruenceClosure}(F, R)),\\{}f_{I} := \operatorname{FintypeOfFinite}(Q_{I}), f_{R} := \operatorname{FintypeOfFinite}(Q_{R}),\\{}f_{C} := \operatorname{FintypeOfFinite}(Q_{C}),\\{}pi_{IR}: Q_{I} \to Q_{R} := \operatorname{QuotientMap}(id, \operatorname{congruenceInterior}(F, R) \subseteq R),\\{}pi_{RC}: Q_{R} \to Q_{C} := \operatorname{QuotientMap}(id, R \subseteq \operatorname{congruenceClosure}(F, R)),\\{}q_{I}: X \to Q_{I} := (x \mapsto \operatorname{QuotientMk}(\operatorname{congruenceInterior}(F, R), x)),\\{}mu_{I} := \operatorname{pushforward}(q_{I}, mu), mu_{R} := \operatorname{pushforward}(pi_{IR}, mu_{I}),\\{}\operatorname{Hcond}(\operatorname{pushforward}((i \mapsto (pi_{RC}(pi_{IR}(i)), i)), mu_{I})) = \operatorname{Hcond}(\operatorname{pushforward}((r \mapsto (pi_{RC}(r), r)), mu_{R})) + \operatorname{Hcond}(\operatorname{pushforward}((i \mapsto (pi_{IR}(i), i)), mu_{I})).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/DualRepairEntropyDecomposition.dual_repair_entropy_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be finite, let F update X, let R be an equivalence relation, and let mu be a normalized law with positive mass at every state. The predictive interior and forgetting closure are the imported canonical congruence repairs.

Their inclusion proofs induce canonical quotient maps from X/I to X/R and from X/R to X/C. The displayed laws are deterministic pushforwards of mu along these quotient maps, so no entropy target is used to define a source object.

Applying the repository quotient-fiber entropy decomposition to I to C, I to R, and R to C gives three entropy balances. Pushforward composition identifies the two closure laws, and the balances telescope to the claimed equality.

Pinned Mathlib and installed-package searches found no finite real-valued conditional-entropy theorem with these canonical repair quotients.

## References

- Truth anchor: `D5/S3/Entropy/Observation/DualRepairEntropyDecomposition.dual_repair_entropy_decomposition`
- Dependency: [D5/S3/Entropy/Fusion/QuotientFiberDecomposition](../Fusion/QuotientFiberDecomposition.md)
- Dependency: [D5/S3/Observer/Separation/CongruenceClosureDuality](../../Observer/Separation/CongruenceClosureDuality.md)
