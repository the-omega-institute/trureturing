# Factor Complexity of Irrational Lower Mechanical Words

## Abstract

Count factors of every irrational lower mechanical word at an arbitrary intercept.

Fix an irrational real slope alpha in the half-open interval from zero to one and an arbitrary real intercept rho. Factors begin only at natural indices, and the lower mechanical word retains its frozen half-open boundary convention.

**Definition 1.1 (The factor set records exactly the factors at natural starts).**

$$FactorSet(\alpha,\rho,n) = \{w_\alpha,\rho(i,n) : i\in\mathbb{N}\}$$

*Formalization.* `D5/S1/Words/Mechanical/MechanicalFactorComplexity.lowerMechanicalFactorSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite Boolean function represents each candidate word. Filtering by occurrence and mapping through List.ofFn gives a finite set whose membership is equivalent to occurrence at some natural starting index.

**Theorem 1.2 (Every irrational lower mechanical word has complexity n plus one).**

$$\forall \alpha,\rho\in\mathbb{R}, 0 \leq \alpha < 1 \land \operatorname{Irrational}(\alpha) \Rightarrow \forall n\in\mathbb{N}, \operatorname{card}(FactorSet(\alpha,\rho,n)) = n + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalFactorComplexity.lower_mechanical_factor_complexity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper bound classifies a factor by how many of its n irrational breakpoints lie at or below the translated phase. Equal ranks give equal successive prefix counts and hence equal letters.

For the lower bound, irrational rotation is dense after translation by rho. Every open interval between adjacent sorted breakpoints therefore contains a natural-start phase, realizing every rank from zero through n.

The theorem is a factor-complexity statement for lower mechanical words. It does not assert the converse characterization of all Sturmian words.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalFactorComplexity.lowerMechanicalFactorSet`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalFactorComplexity.lower_mechanical_factor_complexity`
- Dependency: [D5/S1/Words/Mechanical/MechanicalBalance](MechanicalBalance.md)
