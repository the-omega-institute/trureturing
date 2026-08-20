# Base Identification

## Abstract

The frontier base and the older non-Pisot base are one number, and it is irrational.

Two modules define the positive root of the quadratic with constant term three, under two names, thirty hours apart. The bodies are identical, so the identifications hold by reflexivity. Both modules are frozen, so neither definition can be withdrawn; what can be done is to state the identity and let a machine check it, which turns a second silent source into an alias that would go red if the two ever diverged.

The bridge also carries something across rather than only tidying: the irrationality of the base was proved on the older side and is imported here instead of reproved, and the conjugate's irrationality follows from it because the conjugate is one minus the base.

**Theorem 1.1 (The two bases are one).**

$$\mathit{betaThirteen} = \mathit{beta13} \land \left(\mathit{betaThirteenConjugate} = \mathit{beta13Conjugate} \land \left(\operatorname{Irrational}\left(\mathit{betaThirteen}\right) \land \operatorname{Irrational}\left(\mathit{betaThirteenConjugate}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisotFrontier/BaseIdentification.the_two_bases_are_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The search that would have prevented the duplication is one on the object, the square root of thirteen or the quadratic itself, rather than on the name about to be introduced. Searching for a name you are about to write can only confirm that you have not written it yet.

## References

- Truth anchor: `D5/S0/Tower/NonPisotFrontier/BaseIdentification.the_two_bases_are_one`
- Dependency: [D5/S0/Tower/NonPisot/Beta13](../NonPisot/Beta13.md)
- Dependency: [D5/S0/Tower/NonPisotFrontier/BetaThirteen](BetaThirteen.md)
