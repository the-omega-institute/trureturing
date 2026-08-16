# Tribonacci Finite-Name Bound

## Abstract

Terminating Tribonacci names have zero survivor liminf and satisfy the corrected champion upper bound.

**Definition 1.1 (Terminating-name carrier).**

$$\forall x \in R,\; x \in \mathit{Dfin} \Leftrightarrow \left(\exists Q \in N,\; x \in \operatorname{tribonacciNameGrid}\left(Q\right)\right)$$

*Formalization.* `D5/S0/Tower/DBonacciGeneral/TribonacciFiniteNameBound.tribonacciFiniteNameCarrier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is the union of all finite Tribonacci name grids. This is an arithmetic domain selected by terminating admissible expansions, not a predicate manufactured only to remove the endpoint counterexample.

**Theorem 1.2 (Finite names have zero liminf).**

$$\forall x \in \mathit{Dfin},\; \operatorname{liminfAtTop}\left(\operatorname{tribonacciSurvivor}\left(Q, x\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciFiniteNameBound.tribonacci_finite_name_liminf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending zero digits preserves an admissible name and its real value. Consequently a point in one finite grid belongs to every later grid, so its normalized grid distance is eventually identically zero.

**Theorem 1.3 (Champion bound on finite names).**

$$\forall x \in \mathit{Dfin},\; \operatorname{liminfAtTop}\left(\operatorname{tribonacciSurvivor}\left(Q, x\right)\right) \le \operatorname{championValue}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciFiniteNameBound.tribonacci_finite_name_liminf_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact zero liminf lies below the positive Tribonacci champion value. This theorem covers only terminating name points. It does not prove the source sentence on the full interior interval, and it does not include the nonterminating champion orbit.

## References

- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciFiniteNameBound.tribonacciFiniteNameCarrier`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciFiniteNameBound.tribonacci_finite_name_liminf`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciFiniteNameBound.tribonacci_finite_name_liminf_upper_bound`
- Dependency: [D5/S0/Tower/DBonacciGeneral/TribonacciGlobalBound](TribonacciGlobalBound.md)
