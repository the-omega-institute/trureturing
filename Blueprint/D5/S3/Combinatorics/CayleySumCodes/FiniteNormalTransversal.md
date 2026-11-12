# Normal transversals in arbitrary finite groups

## Abstract

The elementary normal-transversal characterization of finite abelian groups.

**Theorem 1.1 (Every subgroup NLT forces commutativity).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/FiniteNormalTransversal.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/FiniteNormalTransversal.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

For every finite group G, if every subgroup has a conjugation-invariant left transversal in G, then G is abelian. Strong induction on the actual group cardinal passes the property to proper subgroups and normal-subgroup quotients. A proper nontrivial normal subgroup and its quotient are abelian, so the solvable theorem applies. In the remaining simple case, every proper subgroup is abelian. Distinct maximal subgroups intersect trivially and are self-normalizing. The proof counts their actual conjugacy orbits and disjoint sets of nonidentity elements, then proves the exact covering equality. The equality contradicts properness. No order-sixty restriction, classification of finite simple groups, or finite sample is used. The general simple-center lemma and nonidentity injection are reused from SimpleOrderSixty with its Moonshine-in-Kansas/atlas attribution; their declarations themselves have no order-sixty hypothesis.

**Theorem 1.2 (Abelian groups and subgroup sum-graph codes).**

Lean statement: `D5/S3/Combinatorics/CayleySumCodes/FiniteNormalTransversal.equivalence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CayleySumCodes/FiniteNormalTransversal.equivalence` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Subgroup total perfect codes in Cayley sum graphs: a missing case and its consequences*. DOI: [10.5281/zenodo.23375144](https://doi.org/10.5281/zenodo.23375144). URL: <https://doi.org/10.5281/zenodo.23375144>.

*Commentary.*

A finite group is abelian exactly when every subgroup is a perfect or total perfect code of some loopless Cayley sum graph with a normal connection set. The graph and code type may depend on the subgroup. Every code supplies NLT, including the two-element total-code branch where the identity is removed from the connection set. Conversely, abelian groups admit perfect-code witnesses for every subgroup. Together these are the three equivalent properties in Theorem 4.5 of both public correction versions by Ma, Nikandish and Zhang. NLT restriction is not an assertion of total-code quotient inheritance, and this elementary route does not independently certify the unaffected CFSG casework in the antecedent article.

## References

- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/FiniteNormalTransversal.equivalence`
- Truth anchor: `D5/S3/Combinatorics/CayleySumCodes/FiniteNormalTransversal.result`
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal](PerfectCodeTransversal.md)
- Dependency: [D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal](SolvableNormalTransversal.md)
- Dependency: [D5/S3/FiniteGroups/SimpleOrderSixty](../../FiniteGroups/SimpleOrderSixty.md)
