# Least Nontrivial Metallic Value

## Abstract

The golden ratio uniquely minimizes the positive integer members of the metallic family.

**Theorem 1.1 (The golden ratio is the unique least nontrivial value).**

$$\begin{aligned}metallicValue(1) = \varphi \land\\\forall n \in \mathbb{N}, 0 < n \Rightarrow\\\varphi \le metallicValue(n) \land (metallicValue(n) = \varphi \iff n = 1).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/MetallicMinimum.metallic_value_minimal_nontrivial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parameter-one value explicitly realizes the golden ratio. For every positive integer parameter, comparison of the two radicands gives the golden lower bound, and equality forces the parameter back to one.

The source derives positivity of the integer fusion coefficient from noninvertibility. The Lean statement exposes that derived condition as 0 < n because it reuses the repository's numerical metallic family rather than introducing a second fusion-category carrier.

## References

- Truth anchor: `D5/S0/Asymptotics/MetallicMinimum.metallic_value_minimal_nontrivial`
- Dependency: [D5/S0/Asymptotics/MetallicFamily](MetallicFamily.md)
