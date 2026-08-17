# D-Bonacci Permanent Survivors

## Abstract

Strict four- and five-bonacci permanent survival is empty, while each closed threshold retains its champion period-two carrier.

The typed d-bonacci alphabet gives four gap kinds at order four and five gap kinds at order five. A uniform transition sends a zero label to the top gap and splits every positive label into a top or predecessor branch. Two order-specific barrier inequalities force a hypothetical strict permanent orbit onto the expanding top-gap two-cycle. The inverse-square distance estimate then forces its boundary point, which the strict domain excludes.

**Theorem 1.1 (The strict four-bonacci permanent set is empty).**

$$\mathit{dbonacciFourStrictPermanentSet} = \mathit{emptySet}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciSurvivors/DBonacciPermanentSurvivors.dbonacci_four_strict_permanent_set_eq_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is an all-depth intersection statement: no four-gap state survives every finite backward depth. It does not assert that the finite survivor set at depth 60 is empty.

**Theorem 1.2 (The strict five-bonacci permanent set is empty).**

$$\mathit{dbonacciFiveStrictPermanentSet} = \mathit{emptySet}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciSurvivors/DBonacciPermanentSurvivors.dbonacci_five_strict_permanent_set_eq_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is likewise an all-depth intersection statement, not a proof that the finite depth-60 survivor set is empty.

**Theorem 1.3 (The closed four-bonacci permanent set is nonempty).**

$$\exists s \in \operatorname{State}\left(4\right),\; s \in \mathit{dbonacciFourClosedPermanentSet}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciSurvivors/DBonacciPermanentSurvivors.dbonacci_four_closed_permanent_set_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The top and predecessor champion states form a closed period-two orbit. This proves a lower bound for the closed permanent set and is not used to prove strict emptiness.

**Theorem 1.4 (The closed five-bonacci permanent set is nonempty).**

$$\exists s \in \operatorname{State}\left(5\right),\; s \in \mathit{dbonacciFiveClosedPermanentSet}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciSurvivors/DBonacciPermanentSurvivors.dbonacci_five_closed_permanent_set_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five-bonacci champion states give the analogous closed period-two carrier. Strict and closed thresholds remain separate definitions and separate theorems.

## References

- Truth anchor: `D5/S0/Tower/DBonacciSurvivors/DBonacciPermanentSurvivors.dbonacci_five_closed_permanent_set_nonempty`
- Truth anchor: `D5/S0/Tower/DBonacciSurvivors/DBonacciPermanentSurvivors.dbonacci_five_strict_permanent_set_eq_empty`
- Truth anchor: `D5/S0/Tower/DBonacciSurvivors/DBonacciPermanentSurvivors.dbonacci_four_closed_permanent_set_nonempty`
- Truth anchor: `D5/S0/Tower/DBonacciSurvivors/DBonacciPermanentSurvivors.dbonacci_four_strict_permanent_set_eq_empty`
- Dependency: [D5/S0/Tower/DBonacci/ChampionOrbit](../DBonacci/ChampionOrbit.md)
- Dependency: [D5/S0/Tower/DBonacci/OrbitAlgebra](../DBonacci/OrbitAlgebra.md)
- Dependency: [D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit](../DBonacciGeneral/FiveChampionOrbit.md)
