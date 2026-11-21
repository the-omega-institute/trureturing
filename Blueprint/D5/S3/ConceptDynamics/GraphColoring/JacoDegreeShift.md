# Maximum degree, Beatty outdegree and the shifted order

## Abstract

Every finite linear Jaco maximum degree is b_n or b_n-1, and the order n+Delta_n then has maximum degree n or n-1.

**Theorem 1.1 (The two cases and the shifted order).**

$$\forall n \in \mathrm{Nat},\; ((\operatorname{Delta}\left(n\right) = \operatorname{b}\left(n\right)) \lor (\operatorname{Delta}\left(n\right) + 1 = \operatorname{b}\left(n\right))) \land (((\operatorname{Delta}\left(n\right) = \operatorname{b}\left(n\right)) \Leftrightarrow (\operatorname{frac}\left(n\right) < \frac{1}{phi})) \land (((\operatorname{Delta}\left(n\right) + 1 = \operatorname{b}\left(n\right)) \Leftrightarrow (\frac{1}{phi} < \operatorname{frac}\left(n\right))) \land (((\operatorname{Delta}\left(n\right) = \operatorname{b}\left(n\right)) \Rightarrow (\operatorname{Delta}\left(n + \operatorname{Delta}\left(n\right)\right) = n)) \land ((\operatorname{Delta}\left(n\right) + 1 = \operatorname{b}\left(n\right)) \Rightarrow (\operatorname{Delta}\left(n + \operatorname{Delta}\left(n\right)\right) + 1 = n)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoDegreeShift.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

Write Delta_n for the maximum degree of the finite linear Jaco graph jaco n, b_n=beattyOut n=floor((n+1)/phi) for the existing Beatty outdegree, and frac n for the fractional part of (n+2)/phi. For every natural n, Delta_n=b_n exactly when frac n<1/phi, Delta_n=b_n-1 exactly when frac n>1/phi, and one of the two always holds; in the first case the order n+Delta_n has maximum degree n, in the second n-1. Theorem 2.9 of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, arXiv:1404.0484v1, printed page 7, states only that the order n+Delta_n has maximum degree n or n-1; its proof splits on the outdegree d+(v_n)=b_n and leaves the second case undecided between n and n-1. The case-matched values and the threshold criterion, for every natural n, are repo-derived. Proof: JacoAdditionLaw.delta_eq_floor gives Delta_n=floor((n+2)/phi)-1, and b_n=floor((n+2)/phi-1/phi). The value frac n=1/phi is impossible, since it would make (n+1)/phi an integer although (n+1)/phi is irrational. Below the threshold b_n=floor((n+2)/phi)-1, above it b_n=floor((n+2)/phi). Using 1/phi^2=1-1/phi one gets (n+Delta_n+2)/phi=n+2-(1+frac n)/phi, and (1+frac n)/phi lies in (0,1) below the threshold and in (1,2) above it, because (1+1/phi)/phi=1; so the maximum degree of the shifted order is n or n-1.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoDegreeShift.result`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw](JacoAdditionLaw.md)
