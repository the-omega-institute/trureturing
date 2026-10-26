# Exact projective-plane integer incidence

## Abstract

Integer incidence lattices on every actual finite nondegenerate projective plane.

Let P and L be the original finite point and line types with a Mathlib Configuration.ProjectivePlane instance. Write q for its derived order, so q>=2 and both cardinalities are q^2+q+1. Each line contains q+1 points and each point lies on q+1 lines. Distinct lines meet once and distinct points have one joining line. These standard geometric facts are reused from Thomas Browning's Mathlib Configuration source. No plane is postulated at an arbitrary integer order. Singer's 1938 cyclic trace construction is geometry context only; it does not supply the integer-lattice inference.

**Definition 1.1 (Original line indicators).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.row`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

row l x is the integer 0 or 1 according to original incidence x in l.

**Definition 1.2 (Original integer potentials).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.incidence`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.incidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F(a)(x)=sum_l row(l,x)*a(l), for arbitrary signed integer coefficients on ALL original lines.

**Definition 1.3 (Original line sums).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.lineSum`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.lineSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

h_l(z)=sum_x row(l,x)*z(x), with all sums in the ambient integers.

**Definition 1.4 (Exact image).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.lattice`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.lattice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M is exactly range F in Z^P. It is neither a saturation nor a rational span.

**Theorem 1.5 (Total mass identity).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.total_incidence`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.total_incidence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer potential a, sum_x F(a)(x)=(q+1)*sum_l a(l). Interchanging finite sums uses the actual q+1 line cardinality.

**Theorem 1.6 (Line mass identity).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.lineSum_incidence`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.lineSum_incidence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original line l and integer potential a, h_l(F(a))=q*a(l)+sum_k a(k). The self-intersection contributes q+1 and every other original line contributes one.

**Theorem 1.7 (Unique original potentials).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.incidence_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.incidence_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

F is injective on Z^L. Equality of totals fixes the coefficient total, and equality of original line sums fixes each integer coefficient. Only nonzero integer factors are cancelled.

**Theorem 1.8 (Unique integer reconstruction).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.integer_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.integer_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer z and integer s satisfying the total equation and every original-line divisibility, there is exactly one original integer potential a with F(a)=z, total coefficient sum s, and a(l)=(h_l(z)-s)/q after divisibility is known. Injectivity supplies uniqueness.

**Theorem 1.9 (Divisibility-certified reconstruction).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.mem_lattice_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.mem_lattice_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every z in Z^P, z lies in M iff there is an INTEGER s with sum_x z(x)=(q+1)*s and q divides h_l(z)-s for EVERY original line l. After these divisibilities, the integer coefficient is (h_l(z)-s)/q. The dual pair-count identity gives q*F(a)(x)=q*z(x) at each original point; ambient integer cancellation reconstructs z.

**Definition 1.10 (Boolean original supports).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.indicator`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.indicator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

indicator S is 1 on the original finite support S and 0 at every other original point.

**Theorem 1.11 (Complete proper Boolean closure).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.boolean_mem_lattice_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.boolean_mem_lattice_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty proper original support S, indicator S is in M iff S is an original line. If indicator S=F(a), total mass gives 1<=s<=q. Line sums give 0<=q*a(l)+s<=q+1. If s>=2 all coefficients are nonpositive, contradicting their positive sum. For s=1 they are all 0 or 1 and exactly one is 1. This excludes ALL hidden larger proper Boolean members, not merely extra generator rows.

**Definition 1.12 (Original integer unit vectors).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.unit`

*Formalization.* `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.unit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

unit x is the indicator of the singleton original point x.

**Theorem 1.13 (The signed unit ideal).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.unit_mem_lattice_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.unit_mem_lattice_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original x and every signed integer k, k*e_x is in M iff q*(q+1) divides k. A line avoiding x forces q to divide the integer coefficient total. The upper certificate is (q+1)*W_x-T, with W_x=sum_{l contains x}[l]=q*e_x+U and T=sum_l[l]=(q+1)*U.

**Theorem 1.14 (The signed difference ideal).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.difference_mem_lattice_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.difference_mem_lattice_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all distinct original x,y and all signed integer k, k*(e_x-e_y) is in M iff q divides k. The coefficient total is zero, and a line through x but not y forces the lower bound. The upper certificate is W_x-W_y.

**Theorem 1.15 (The signed full-total ideal).**

Lean statement: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.constant_mem_lattice_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.constant_mem_lattice_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed integer k, k*U is in M iff q+1 divides k. Since n=1+q*(q+1), the total equation gives k=(q+1)*(s-q*k). The upper certificate uses coefficient 1 on every original line.

The new reusable inference is integer reconstruction, complete Boolean closure and the exact signed ideals, derived here from the supplied native proof and Mathlib geometry. This is repo-derived content, without an external novelty or priority claim. Public identities serve the reconstruction and closure deductions; internal sum and geometric helpers have live consumers. Utility none: these are universal symbolic theorems, not finite enumerations, numeric reductions or certified instances.

In the universal quotient Z^P/M these ideals identify the exact annihilators of original units, differences and the full total. In particular nonzero q-torsion in original differences is retained; no cancellation is performed in this quotient. Each original point occurs in q+1 complete minimal Boolean rows, so this family genuinely exceeds incidence at most two, with unbounded q whenever actual planes exist. Primitive-free refers only to the original units and differences, not all primitive integer vectors: the line rows themselves are primitive.

Information-escape registration is unfinished for the nine public theorems; the source-bound audit gap is tracked at https://github.com/the-omega-institute/trureturing/issues/22019. The mathematical kernel check is separate from this incomplete registration. No declared_validated claim is made.

Mere line-zero equations in an arbitrary target group do not establish this complete Boolean closure. Further quotienting by the full-total vector makes line complements zero too; pair-intersection line sums still rule out original unit or difference collapse for q>=2. Thus an arbitrary group transfer requires a completeness hypothesis on ALL minimal zero supports. Exact orders stated here concern the universal quotient, not every target group. No ordering theorem, formal Good theorem, unrestricted integral blocker, general Good or AM result is claimed.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.boolean_mem_lattice_iff`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.constant_mem_lattice_iff`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.difference_mem_lattice_iff`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.incidence`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.incidence_injective`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.indicator`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.integer_reconstruction`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.lattice`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.lineSum`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.lineSum_incidence`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.mem_lattice_iff`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.row`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.total_incidence`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.unit`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/ProjectivePlaneIntegerLattice.unit_mem_lattice_iff`
