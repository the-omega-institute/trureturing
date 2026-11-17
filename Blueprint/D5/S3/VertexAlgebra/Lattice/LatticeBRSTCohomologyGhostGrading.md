# Integer ghost grading of the full original BRST quotient

## Abstract

Integer ghost grading of the full original BRST quotient

The carrier is literally State D, Q is totalCharge D H, Z is the existing cycles D H, B is the existing boundaries D H h26 hHG hGH, and C is the existing Cohomology D H h26 hHG hGH. Every quotient theorem keeps D : LatticeData, H : Matrix (Fin D.rank) (Fin D.rank) Complex, h26 : D.rank = 26, hHG : H * gramComplex D = 1, and hGH : gramComplex D * H = 1. No momentum or energy sector, relative antighost kernel, NullFrame, positivity, or finite-dimensionality assumption is added.

Write N for tensorNumber D. The existing all-state law NQ-QN=Q gives QNz=0 for a cycle z and N(Qx)=Q(Nx+x) for every original state x. Thus N descends once to the actual quotient. The full tensor basis has integral weights charge(S), the odd occupation count minus the even occupation count. Existing private all-state diagonality laws are reused through their original source module; the basis agrees definitionally with fullBasis. Integer weights are cast injectively into Complex, including negative weights.

**Definition 1.1 (project).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.project`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.project` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A full-state linear map Pi_g defined on the full tensor basis by retaining precisely basis labels of integer ghost number g. Applying the existing number/Q commutator to basis coefficients forces every nonzero Q coefficient to have output weight input weight plus one. Consequently Pi_g Q = Q Pi_(g-1). This gives closed projected cycles, without assuming a degree law.

**Definition 1.2 (stateDegrees).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.stateDegrees`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.stateDegrees` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image of ghost charge on the finite support of fullBasis.repr x. This finite set depends on x; no uniform grade interval or finite-dimensional state space is asserted. The original state is the sum of its Pi_g components over this set.

**Definition 1.3 (cycleNumber).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.cycleNumber`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.cycleNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original number operator restricted to the actual full Q-kernel. Its boundary preservation uses the explicit original primitive Nx+x for the image of Qx.

**Definition 1.4 (cycleProject).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.cycleProject`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.cycleProject` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pi_g restricted to actual cycles using the proved Q shift. No family of quotient projection operators is introduced.

**Definition 1.5 (number).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.number`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.number` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nbar on the existing full critical quotient, constructed with Submodule.mapQ. Its value at the class of z is the class of Nz.

**Definition 1.6 (grade).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.grade`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.grade` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

G(g) is the eigenspace of Nbar at the Complex cast of g, indexed by every integer.

**Theorem 1.7 (finite_class_decomposition).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.finite_class_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.finite_class_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each actual cycle z, the finite sum over stateDegrees z of classOf(cycleProject g z) equals classOf z. Each summand belongs to G(g) because N Pi_g z = g Pi_g z. The finite support and Q shift are proved on the original unrestricted carrier.

**Theorem 1.8 (grades_internal).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.grades_internal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.grades_internal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

DirectSum.IsInternal G for the actual full quotient. Surjectivity follows from the finite class decomposition and surjectivity of classOf. Independence reuses Mathlib's eigenspaces_iSupIndep composed with the injective integer-to-Complex cast. This proves the canonical sum of the eigenspace inclusions is bijective.

**Theorem 1.9 (project_same_class).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.project_same_class`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.project_same_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer g and every original cycle z whose class belongs to G(g), classOf(cycleProject g z) = classOf z. The proof separates the g component from the finite sum and uses independence against the supremum of all other integer grades. It includes absent support and the zero class. An arbitrary representative is not assumed homogeneous.

**Theorem 1.10 (homogeneous_cycle_lift).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.homogeneous_cycle_lift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.homogeneous_cycle_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every g and c in G(g), there exists an actual cycle z with classOf z = c and tensorNumber z = (g : Complex) times z. The lift is obtained by projecting any original cycle representative, with equality of classes supplied by project_same_class.

Attribution remains with the actual lattice and ghost suppliers, Bakalov-Kac, Scott Carnahan, Kalle Kytola, and Mathlib's basis, quotient and eigenspace machinery. This result establishes the algebraic integer grading and lift on the specified BRST complex. It makes no product degree, Delta degree, bracket degree, parity conversion, physical spacetime reconstruction, complete string theory, AdS/CFT or literature novelty claim.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.cycleNumber`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.cycleProject`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.finite_class_decomposition`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.grade`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.grades_internal`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.homogeneous_cycle_lift`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.number`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.project`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.project_same_class`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading.stateDegrees`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTZeroEnergyReduction](LatticeBRSTZeroEnergyReduction.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology](LatticeRelativeBRSTCohomology.md)
