# The corrected Jaco maximum-degree addition law

## Abstract

The maximum degrees of finite linear Jaco graphs obey an exact additive correction law with golden fractional parts.

**Definition 1.1 (Maximum degree as an integer).**

$$\operatorname{delta}\left(n\right) = \operatorname{maxDegree}\left(\operatorname{jaco}\left(n\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.delta` (`✓ std3`).

*Citation.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

delta n is the ordinary maximum degree of the existing finite linear Jaco graph jaco n on the labels 1 through n, cast to an integer so that differences may be negative.

**Definition 1.2 (The golden fractional part).**

$$\operatorname{frac}\left(n\right) = \operatorname{fract}\left(\frac{n + 2}{phi}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.frac` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

frac n is the fractional part of (n+2)/phi, where phi=(1+sqrt(5))/2 is the golden ratio; it lies in [0,1).

**Definition 1.3 (The correction constant).**

$$alpha = \operatorname{sqrt}\left(5\right) - 2$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

alpha=sqrt(5)-2, approximately 0.236, equals 1-2/phi up to sign: 2/phi=sqrt(5)-1.

**Theorem 1.4 (The multi-summand correction law).**

$$\forall s \in \operatorname{Finset}\left(iota\right),\; \forall n \in iota \to \mathrm{Nat},\; ((\operatorname{Nonempty}\left(s\right)) \land (\forall j \in s,\; 1 \le n_{j})) \Rightarrow (\operatorname{delta}\left(\sum_{j in s} (n_{j})\right) - \sum_{j in s} (\operatorname{delta}\left(n_{j}\right)) = \left\lfloor\sum_{j in s} (\operatorname{frac}\left(n_{j}\right)) - (\operatorname{card}\left(s\right) - 1) \cdot alpha\right\rfloor)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.sum_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

For every nonempty finite family of positive orders n_j, j in s, with r=|s| members and total N, the maximum degree of J_N exceeds the sum of the members' maximum degrees by exactly floor(sum_j frac(n_j)-(r-1)alpha). Proof: the existing maximum-degree theorem gives delta n=floor((n+2)/phi)-1 for n at least two, and the one-vertex graph has maximum degree zero, which matches floor(3/phi)-1=0. Hence delta n=(n+2)/phi-frac(n)-1 as real numbers. Subtracting, the summands' constants (n_j+2)/phi cancel against (N+2)/phi except for (2-2r)/phi, and 2/phi=sqrt(5)-1 turns the remaining constant into -(r-1)alpha. The integer difference therefore equals sum_j frac(n_j)-(r-1)alpha-frac(N), and since frac(N) lies in [0,1) it is the floor of sum_j frac(n_j)-(r-1)alpha. The source states only the two-branch conjecture for two distinct summands at least three, which is false; this law replaces it for any number of positive summands.

**Theorem 1.5 (Two-summand trichotomy and witnesses).**

$$(\forall s \in \operatorname{Finset}\left(iota\right),\; \forall n \in iota \to \mathrm{Nat},\; ((\operatorname{Nonempty}\left(s\right)) \land (\forall j \in s,\; 1 \le n_{j})) \Rightarrow (\operatorname{delta}\left(\sum_{j in s} (n_{j})\right) - \sum_{j in s} (\operatorname{delta}\left(n_{j}\right)) = \left\lfloor\sum_{j in s} (\operatorname{frac}\left(n_{j}\right)) - (\operatorname{card}\left(s\right) - 1) \cdot alpha\right\rfloor)) \land ((\forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; ((1 \le n) \land (1 \le m)) \Rightarrow ((\operatorname{delta}\left(n + m\right) - \operatorname{delta}\left(n\right) - \operatorname{delta}\left(m\right) = \left\lfloor\operatorname{frac}\left(n\right) + \operatorname{frac}\left(m\right) - alpha\right\rfloor) \land (((\operatorname{delta}\left(n + m\right) - \operatorname{delta}\left(n\right) - \operatorname{delta}\left(m\right) = -1) \Leftrightarrow (\operatorname{frac}\left(n\right) + \operatorname{frac}\left(m\right) < alpha)) \land (((\operatorname{delta}\left(n + m\right) - \operatorname{delta}\left(n\right) - \operatorname{delta}\left(m\right) = 0) \Leftrightarrow ((alpha \le \operatorname{frac}\left(n\right) + \operatorname{frac}\left(m\right)) \land (\operatorname{frac}\left(n\right) + \operatorname{frac}\left(m\right) < 1 + alpha))) \land ((\operatorname{delta}\left(n + m\right) - \operatorname{delta}\left(n\right) - \operatorname{delta}\left(m\right) = 1) \Leftrightarrow (1 + alpha \le \operatorname{frac}\left(n\right) + \operatorname{frac}\left(m\right))))))) \land ((\operatorname{delta}\left(3 + 11\right) - \operatorname{delta}\left(3\right) - \operatorname{delta}\left(11\right) = -1) \land ((\operatorname{delta}\left(3 + 4\right) - \operatorname{delta}\left(3\right) - \operatorname{delta}\left(4\right) = 0) \land (\operatorname{delta}\left(4 + 6\right) - \operatorname{delta}\left(4\right) - \operatorname{delta}\left(6\right) = 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok; Paul Fisher; Bettina Wilkens; Mokhwetha Mabula; Vivian Mukungunugwa (2014). *Characteristics of Finite Jaco Graphs, J_n(1), n in N*. DOI: [10.48550/arXiv.1404.0484](https://doi.org/10.48550/arXiv.1404.0484).

*Commentary.*

The first clause restates the multi-summand law. For two positive orders n,m it reads delta(n+m)-delta n-delta m=floor(frac n+frac m-alpha). Because both fractional parts lie in [0,1) and 0<alpha<1, the argument lies in [-alpha,2-alpha), so the correction is -1 exactly when frac n+frac m<alpha, 0 exactly when alpha<=frac n+frac m<1+alpha, and 1 exactly when 1+alpha<=frac n+frac m. Exact rational bounds 8/5<phi<13/8 give delta 3=2, delta 4=2, delta 6=3, delta 7=4, delta 10=6, delta 11=7 and delta 14=8, so the distinct pairs (3,11), (3,4) and (4,6) attain the values -1, 0 and 1. The pair (3,11) is the one that refutes the source's first branch, and (4,6) realises the plus-one correction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.alpha`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.delta`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.frac`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.result`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.sum_law`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree](JacoMaximumDegree.md)
