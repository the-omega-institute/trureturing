# Conditional Square-Energy of Forest Constraints

## Abstract

An unsatisfiable finite forest of actual constraints has total conditional square-energy at least two thirds.

**Definition 1.1 (Mass of the actual forbidden fibre).**

Lean statement: `D5/S3/Arith/Congruence/ForestConstraintEnergy.forbiddenMass`

*Formalization.* `D5/S3/Arith/Congruence/ForestConstraintEnergy.forbiddenMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a node v with finite domain D(v) and weight w(v,y), forbiddenMass sums w(v,y) over values y that are pure forbidden or conflict with a supplied parent value. A missing parent value selects only the pure forbidden set. The indicator records membership in the union, so a value satisfying both forbidden conditions is counted once.

**Theorem 1.2 (An unsatisfiable forest costs at least two thirds).**

Lean statement: `D5/S3/Arith/Congruence/ForestConstraintEnergy.unsatisfiable_forest_square_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ForestConstraintEnergy.unsatisfiable_forest_square_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite vertex set have at most one parent per vertex and a natural-valued level strictly increasing from parent to child. Each node has its own finite domain and fixed nonnegative weights summing to one on that domain. Pure forbidden sets and binary parent-child forbidden relations are arbitrary. Zero weights are allowed; weights at a node do not depend on the parent value.

Write alpha(v,z) for forbiddenMass at boundary z. At a root the energy epsilon(v) is alpha(v,none) squared. At a nonroot v with parent p it is the sum over z in D(p) of w(p,z) times alpha(v,some z) squared. If there is no simultaneous assignment respecting every domain and avoiding every pure and binary forbidden condition, then the sum of epsilon(v) over all vertices is at least 2/3.

The proof applies ExactForestMessages to construct exact residual domains A(v) and incoming messages B(v). For a nonroot, beta(v) is the parent-domain weight of B(v); at a root it is the indicator that A(v) is empty. Let c(v) be the sum of beta over the children. Actual coverage by a local forbidden fibre and the child messages gives 1 <= alpha(v,z)+c(v) whenever that boundary is blocked. The weighted union bound and averaging of squares yield beta(v)(1-c(v))^2 <= epsilon(v) when c(v) <= 1.

For Phi(t)=t-t^3/3 on [0,1], the proof derives Phi(beta(v)) <= epsilon(v)+sum_child Phi(beta). When c <= 1, the sum of the child cubes is at most c^3. The case beta <= c follows from monotonicity; for c <= beta the difference equals c(1-beta)^2+(beta-c)^3/3. When c >= 1, each child contributes at least 2 beta/3 to its potential, while every parent potential is at most 2/3. These estimates are proved inside the theorem.

Summing the local inequalities counts every nonroot potential once on each side. The remaining root potential is bounded by total energy. Exact message feasibility and the assumed absence of an assignment force one root to have beta=1 and potential 2/3. The result therefore holds with arbitrary branching and path length.

The theorem concerns arbitrary finite weighted constraints. Applying it to congruence systems additionally requires the constraint encoding and the bounds on the actual conditional square-energies.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ForestConstraintEnergy.forbiddenMass`
- Truth anchor: `D5/S3/Arith/Congruence/ForestConstraintEnergy.unsatisfiable_forest_square_energy`
- Dependency: [D5/S3/Arith/Congruence/ExactForestMessages](ExactForestMessages.md)
