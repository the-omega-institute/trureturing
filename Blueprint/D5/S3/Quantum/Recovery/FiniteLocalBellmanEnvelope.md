# FiniteLocalBellmanEnvelope

## Abstract

The five-point Bellman value on the closed Euclidean Bloch-ball product.

**Theorem 1.1 (Whole-domain finite-tree Bellman identity).**

Lean statement: `D5/S3/Quantum/Recovery/FiniteLocalBellmanEnvelope.source_bellman_finite_tree_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FiniteLocalBellmanEnvelope.source_bellman_finite_tree_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix r > 0 with 1/2 < r squared < 2. The domain is the product of the two closed unit balls in EuclideanSpace real (Fin 3). The terminal payoff is h times the indicator of the actual five-ray set K_s. Each finite node changes one coordinate by a complete barycentric split. Branching is arbitrary and finite; zero weights, boundary points, unequal depths and immediate stopping are included.

K_s is compact. Starting with the terminal payoff, the original recurrence takes the maximum of the two five-point split values at each stage. Every finite iterate is jointly upper semicontinuous, stays between zero and h, and increases with the stage. Each actor maximum is attained by five points, with zero padding permitted, and bounds every finite split. Each stage value is attained by a tree of depth at most that stage and bounds every tree with that depth budget.

VInfinity is the supremum of these original iterates. At every point of the entire closed domain it equals the supremum of all finite-tree rewards. It satisfies finite Jensen inequalities separately in each coordinate and is the least real separately concave majorant of the terminal payoff. The proof uses active coordinates together with the reward in a four-dimensional convex hull, compact hypographs and a common-error grafting of finitely many continuations. No topological regularity or attainment of VInfinity is required.

Writing fSEP = (1 - a dot b)/(12 kappa) and psi = fSEP - VInfinity, the value lies between zero and fSEP. It equals h on K_s and vanishes on the unit pure diagonal. The function psi is separately convex, lies between zero and fSEP, and vanishes on K_s and the unit pure diagonal.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FiniteLocalBellmanEnvelope.source_bellman_finite_tree_identity`
- Dependency: [D5/S3/Quantum/Recovery/FiniteLocalLatitudeGeometry](FiniteLocalLatitudeGeometry.md)
