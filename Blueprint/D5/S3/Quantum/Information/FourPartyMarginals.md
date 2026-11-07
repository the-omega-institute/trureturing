# Four Party Density Entropies

## Abstract

The Zhang-Yeung defect is evaluated on actual four-party marginals.

A, B, C, D are arbitrary finite carriers. Each displayed entropy is the project natural-log entropy of a reduceState marginal, with its tensor-coordinate permutation defined explicitly. The defect is I(A:B)+I(A:CD)+3 I(C:D|A)+I(C:D|B)-2 I(C:D). Defining it makes no assertion of nonnegativity for unrestricted quantum states.

**Definition 1.1 (The entropy defect).**

$$\operatorname{Delta}\left(\rho\right) = \operatorname{ZY}\left(\rho\right)$$

*Formalization.* `D5/S3/Quantum/Information/FourPartyMarginals.zhangYeungDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mutual and conditional mutual informations are expanded using the actual A, B, C, D, AB, AC, AD, BC, BD, CD, ACD and BCD density marginals. The final theorem restricts the input state to the AD-classical family.

## References

- Truth anchor: `D5/S3/Quantum/Information/FourPartyMarginals.zhangYeungDefect`
- Dependency: [D5/S3/Quantum/Information/MarginalCalculus](MarginalCalculus.md)
