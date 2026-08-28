# Champion Middle Bridge

## Abstract

The indexed middle coordinate is the general one at the Perron root, so the limit carries across.

One value was written twice: once indexed by the arity and once as a function of the base, twenty-three minutes apart. The indexed one was already frozen when the general one appeared, so the link could not be made where it belonged, in the module that generalised it.

Stating the identity is what remains, and it earns its place rather than only tidying: the limit was proved for the general form, and this carries it to the indexed form, which had no limit statement of its own.

**Theorem 1.1 (The two middle coordinates are one).**

$$\left(\forall d \in N,\; \operatorname{championMid}\left(d\right) = \operatorname{championMidCoordinate}\left(\operatorname{dbonacciPerronRoot}\left(d\right)\right)\right) \land \operatorname{Tendsto}\left(\mathit{championMid}, \mathit{atTop}, \operatorname{nhds}\left(\frac{1}{3}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/ChampionMidBridge.the_two_middle_coordinates_are_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pattern that would have avoided this is one directory over: the base itself is a short name whose body is the single source it delegates to, so the two can never drift. When a general form arrives for something already in the tree, it owes the specific form that link, and the debt falls due in the same change.

## References

- Truth anchor: `D5/S0/Tower/DBonacciGeneral/ChampionMidBridge.the_two_middle_coordinates_are_one`
- Dependency: [D5/S0/Tower/DBonacciGeneral/ChampionLimit](ChampionLimit.md)
- Dependency: [D5/S0/Tower/DBonacciSurvivors/FiniteDepth](../DBonacciSurvivors/FiniteDepth.md)
