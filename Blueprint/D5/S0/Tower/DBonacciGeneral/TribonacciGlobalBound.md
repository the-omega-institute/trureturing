# Tribonacci Global-Bound Refutation

## Abstract

The unrestricted real-line Tribonacci champion upper bound is false.

**Theorem 1.1 (The terminal point liminf is t inverse).**

$$\operatorname{liminfAtTop}\left(\operatorname{tribonacciSurvivor}\left(Q, 1\right)\right) = t^{0 - 1}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciGlobalBound.tribonacci_survivor_one_liminf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The final name is nearest to the omitted endpoint one. Its terminal gap scales by t inverse cubed every three levels, giving normalized survivor phases 1, t-1, and t inverse. The last phase is the exact filter liminf.

**Theorem 1.2 (The unrestricted global upper bound is false).**

$$\neg \left(\forall x \in R,\; \operatorname{liminfAtTop}\left(\operatorname{tribonacciSurvivor}\left(Q, x\right)\right) \le \operatorname{championValue}\left(t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciGlobalBound.tribonacci_unrestricted_global_liminf_upper_bound_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the Tribonacci root, championValue(t) is (1-t inverse)/2, strictly below the endpoint liminf t inverse. Thus the requested statement for every real x cannot follow from a forbidden-region iteration: it is false for the frozen real-line survivor itself.

## References

- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciGlobalBound.tribonacci_survivor_one_liminf`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciGlobalBound.tribonacci_unrestricted_global_liminf_upper_bound_false`
- Dependency: [D5/S0/Tower/DBonacciGeneral/ChampionValue](ChampionValue.md)
