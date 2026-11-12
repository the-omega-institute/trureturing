# Primal attainment on the original cone

## Abstract

The original cone base norm attains its primal minimum with the original strictly positive unit.

For the primal optimization in Quantum Origin VI, the original-carrier theorem retains the arbitrary strictly positive original unit, the entire compact base and the generating cone. Full-support compression, determinant normalization, a same-object saturating dual effect, extraction from an actual failed local antipodal pair, purity transport and the return to the original carrier remain open. Primal attainment alone does not complete Proposition 93.3 or supply block classification, Jordan structure, self-duality or a zero-gluing premise.

**Theorem 1.1 (An attained primal on the original cone with its original unit).**

Lean statement: `D5/S3/Quantum/Foundation/RealRogFailureQuantitative.original_primal_attainment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RealRogFailureQuantitative.original_primal_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be an arbitrary finite-dimensional real normed vector space, C a pointed cone whose real span is all of A, and u the same real linear functional throughout. Assume u is strictly positive on every nonzero point of C and the entire base C intersect {u=1} is compact. For every z in A, there exist X,Y in C with z=X-Y and u(X)+u(Y) equal to BaseNormContraction.baseNorm for this C,u,z. The same X,Y minimize the original mass cost over every feasible pair in C. Their masses are respectively (baseNorm(z)+u(z))/2 and (baseNorm(z)-u(z))/2. In particular u(z)=0 forces equal masses on this actual optimum; no change of unit or matrix representation occurs.

The compactness step identifies the entire mass cap {a in C : u(a)<=R} with [0,R] times the original base with zero adjoined, including the zero vector and empty-base case. The product of two such compact caps, intersected with the closed original difference fiber X-Y=z, is compact and contains an initial feasible decomposition supplied by PointedCone.mem_span. A continuous mass minimum on this fiber is a global minimum: every lower-cost feasible pair lies in both caps, and every pair outside the cost bound has larger cost. IsLeast.csInf_eq then identifies this actual minimum with the existing source-defined base norm. The mass-cap parametrization supplies the compactness needed for the minimizing fiber.

This proves the primal portion used in (93.12) and (93.23), on the whole original carrier and without trace normalization, ROG or a zero-gluing assumption. It does not produce a dual functional, prove base-norm polarity or the failed-pair bound 0<baseNorm(p-r)<2, or establish saturation by a common proper effect. Those obligations cannot be inferred from attainment alone. The cone base-norm definition is reused from BaseNormContraction; finite-dimensional continuity and compact minimization are pinned Mathlib inputs. The mass-cap and global-minimum argument implements the source's compactness proof in 90.9; no literature-priority claim is made.

The base-norm definition and nonnegativity of the original unit on the cone are reused directly from BaseNormContraction. The base and the normalized nonzero cone-point membership theorem are reused directly from CircuitBalancedConfirmation.base and CircuitBalancedConfirmation.normalized_mem. Finite-dimensional continuity, compact scalar-set multiplication, compact minimization and IsLeast.csInf_eq are pinned Mathlib inputs. The mass-cap parametrization and global-minimum argument implement the compactness proof in 90.9; no literature-priority claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/RealRogFailureQuantitative.original_primal_attainment`
- Dependency: [D5/S3/Quantum/Dynamics/BaseNormContraction](../Dynamics/BaseNormContraction.md)
- Dependency: [D5/S3/Quantum/Foundation/CircuitBalancedConfirmation](CircuitBalancedConfirmation.md)
