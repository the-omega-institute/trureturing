# Substitution Tower Clause

## Abstract

The substitution-tower clause, its assertions conjoined, including the refutation of the one that is false.

The clause makes several assertions at once: that the gap refinement of a tower is that tower's own substitution, that the champion is the ergodic optimum of the corresponding expanding map, a closed form for the champion value with its numerics, the boundary limit, and the behaviour past the Pisot boundary. Each already had a proof somewhere in the tree. What did not exist was any statement that they hold together and stand for one clause.

One of the assertions is false. The clause claims the strict forbidden region empties by depth sixty; the backward survivor set at that very depth is nonempty. The conjunction carries the refutation rather than the claim, and rather than a weakened restatement that would be true. Rewriting that conjunct back into the clause's own wording makes this module fail to compile, which is the property a false sentence should have once it has been settled.

Assembling it also produced something no single module could see. This is the first module to bring two of the frontier modules into one scope, and doing so revealed that they define the same spectrum name with different underlying value maps. A consumer opening only one of them gets a different function under that name with no diagnostic.

**Theorem 1.1 (The substitution tower clause).**

$$\operatorname{Nonempty}\left(\operatorname{tribonacciBackwardSurvivor}\left(\mathit{tribonacciStrictSurvivorSet}, 60\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisotVerdict/SubstitutionTowerClause.substitution_tower_clause` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed conjunct is the refutation, shown because it is the one that contradicts the source. Nothing in this module is proved for the first time; every conjunct is an existing theorem applied without restatement.

## References

- Truth anchor: `D5/S0/Tower/NonPisotVerdict/SubstitutionTowerClause.substitution_tower_clause`
- Dependency: [D5/S0/Tower/NonPisotVerdict/NotEventuallyPeriodic](NotEventuallyPeriodic.md)
