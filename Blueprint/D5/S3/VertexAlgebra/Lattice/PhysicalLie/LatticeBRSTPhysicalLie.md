# The original current gives a Lie algebra on the actual physical image

## Abstract

The original current gives a Lie algebra on the actual physical image

The full critical telescope means D : LatticeData, H : Matrix (Fin D.rank) (Fin D.rank) Complex, h26 : D.rank = 26, hHG : H * gramComplex D = 1 and hGH : gramComplex D * H = 1. For quotient statements let C = Cohomology D H h26 hHG hGH, cl = classOf D H h26 hHG hGH, J = cohomologyCurrent D H h26 hHG hGH, pi = parity D H h26 hHG hGH, delta = Delta D H h26 hHG hGH and P = product D H h26 hHG hGH. Every occurrence retains the original lattice, Gram/inverse and epsilon inputs. PhysicalStates and its representative closure have the separately stated weaker telescopes.

For original states put Q = totalCharge D H, N = tensorNumber D, B_j = ghostB D j, L_0 = totalL0 D H and K(x,y) = originalMode D 0 (B_(-1)x) y. The existing cycles are ker Q and the existing boundaries are the global image of Q from all State D. The independently descended J is used in both arguments. No relative-only boundary relation, charge cutoff or positivity premise replaces that global quotient.

Source-specific four-slot Reg audits for the public theorems remain unfinished: https://github.com/the-omega-institute/trureturing/issues/29596. Adjacent templates do not supply the complete original telescopes, source selections and checked escape coordinates for these owners. No declared_validated registration is claimed; this delivery uses the explicit linked-issue exception.

**Theorem 1.1 (Integer degree of the existing quotient current).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.current_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.current_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, for a,b : C and p,q : Int with a in grade p and b in grade q, J(a,b) belongs to grade (p+q-1). The existing homogeneous cycle lifts and current_number prove this on the original quotient. No replacement quotient or new mode-grading assumption is used.

**Theorem 1.2 (Skew symmetry of the literal unsigned current).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.current_skew`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.current_skew` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, for arbitrary a,b : C with pi(a) = -a and pi(b) = -b, J(a,b) = -J(b,a). The existing Delta product-defect identity, oddness of Delta and product supercommutativity prove the equality. These hypotheses are parity conditions; integer degree one is sufficient but is not assumed in this statement.

**Theorem 1.3 (Full vector Leibniz on odd quotient classes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.current_leftLeibniz`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.current_leftLeibniz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, if a,b : C satisfy pi(a) = -a and pi(b) = -b, then for every c : C, J(a,J(b,c)) = J(J(a,b),c) + J(b,J(a,c)). Homogeneous cycle lifts for a,b and an unrestricted cycle lift for c descend the exact original-state identity from LatticeBRSTCurrentIdentities. The third class need not be homogeneous.

**Definition 1.4 (The native ghost-one eigenspace).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.DegreeOne`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.DegreeOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, DegreeOne D H h26 hHG hGH abbreviates grade D H h26 hHG hGH 1 inside C. This is the existing number eigenspace of the global quotient; it is not a new relative cohomology or an assertion that every ghost-one class has a physical representative.

**Definition 1.5 (A literal LieRing on native ghost-one cohomology).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.degreeOneLieRing`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.degreeOneLieRing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, DegreeOne carries a LieRing with bracket given by the existing unsigned J, restricted using current_grade at p=q=1. Number-one parity supplies the oddness needed for skew symmetry and vector Leibniz. Characteristic zero gives the self-bracket law. Bilinearity is inherited from the original current.

**Definition 1.6 (Complex Lie algebra on the native degree-one subtype).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.degreeOneLieAlgebra`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.degreeOneLieAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, the preceding LieRing on DegreeOne carries LieAlgebra Complex, with scalar compatibility supplied by linearity in the second argument of J. The carrier and bracket are the actual eigenspace subtype and restricted original current.

**Theorem 1.7 (Cyclic vector Jacobi in the original global quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.current_jacobi`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.current_jacobi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, for a,b,c : C with all three classes in grade 1, J(a,J(b,c)) + J(b,J(c,a)) + J(c,J(a,b)) = 0. The proof combines full vector left-Leibniz, skew symmetry, and grade closure of J(a,b). It is an equality of quotient vectors, with every original charge retained.

**Definition 1.8 (The literal simultaneous physical equations).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalStates`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalStates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For D : LatticeData and arbitrary H : Matrix (Fin D.rank) (Fin D.rank) Complex, physicalStates D H is the original-state submodule defined by Qx = 0, B_0 x = 0, Nx = x, and totalL0 D H x = 0, simultaneously. This definition uses neither h26 nor either inverse-Gram equation. It imposes no momentum, positive-norm or nonzero-charge restriction.

**Theorem 1.9 (Physical representatives close before quotienting).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalStates_current`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalStates_current` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For D and H with hHG : H * gramComplex D = 1 and hGH : gramComplex D * H = 1, and x,y : physicalStates D H, K(x,y) belongs to physicalStates D H. The four components follow from actual Q-closure, current_b0, current_number at p=q=1, and current_L0. This theorem does not assume D.rank = 26. It proves the equations on the literal representative before the unrestricted global quotient.

**Definition 1.10 (The actual class map from physical representatives).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalClass`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, physicalClass is the linear map physicalStates D H to C obtained by including each physical state in cycles D H and applying the existing classOf. Only Q-closure is needed for this inclusion; the target keeps the existing global boundary relation.

**Definition 1.11 (The actual range inside global cohomology).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalImage`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalImage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, physicalImage D H h26 hHG hGH is exactly LinearMap.range (physicalClass D H h26 hHG hGH), as a submodule of C. Equality of its represented classes is still tested using boundaries generated by Q on all of State D. Primitives need not be physical, relative, homogeneous, zero-energy or in a fixed momentum sector.

**Theorem 1.12 (Restriction of the already descended current to the actual range).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalImage_closed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalImage_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, for a,b : C with a and b in physicalImage, J(a,b) lies in physicalImage. Choose literal physical representatives x,y; physicalStates_current supplies K(x,y), and the existing current_classOf equation identifies its class with J(a,b). No new quotient current is defined.

**Definition 1.13 (A literal LieRing on physicalImage itself).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalImageLieRing`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalImageLieRing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, physicalImage itself carries a LieRing whose bracket is J restricted by physicalImage_closed. The proof embeds its elements in the existing degree-one eigenspace for the Lie laws; the operation remains on the literal image subtype. It is not transported along an equivalence or installed on a replacement quotient.

**Definition 1.14 (Complex Lie algebra on the actual physical image).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalImageLieAlgebra`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalImageLieAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, the preceding LieRing on physicalImage carries LieAlgebra Complex, using the existing second-argument linearity of J. This is a literal instance on physicalImage D H h26 hHG hGH. No pairing or positivity statement follows from the instance.

**Definition 1.15 (The same image as a Lie subalgebra of ghost-one cohomology).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalLieSubalgebra`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalLieSubalgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, physicalLieSubalgebra is a LieSubalgebra Complex (DegreeOne D H h26 hHG hGH). Its underlying submodule is physicalImage.comap (grade 1).subtype, so membership is exactly the global-image predicate after inclusion in C. Closure uses physicalImage_closed and the already installed degree-one bracket.

The global representative consequence uses exactly the full critical telescope above, x,x',y,y' : cycles D H and u,v : State D, with Q u = ((x'-x : cycles D H) : State D) and Q v = ((y'-y : cycles D H) : State D). Then cl(cycleCurrent D H hHG hGH x' y') = cl(cycleCurrent D H hHG hGH x y). Here cycleCurrent is the original cycle restriction of K, and all four cycles map to C through the same cl. Bilinearity expands the difference as cycleCurrent(x'-x,y') + cycleCurrent(x,y'-y); the existing left-boundary and right-boundary descent proofs place each term in the existing boundaries, so Submodule.Quotient.eq yields equality. The primitives u and v are unrestricted original states in both slots, not physical or relative states. This is an application of the existing descent construction, not an additional retained named theorem.

The global-image consequence also uses exactly D,H,h26,hHG,hGH above: mapping (physicalLieSubalgebra D H h26 hHG hGH).toSubmodule along (grade D H h26 hHG hGH 1).subtype gives exactly physicalImage D H h26 hHG hGH. In the forward direction membership in the comap is already the global-image predicate. Conversely, every a in physicalImage has number-one class by the original representative equation Nx = x, so a lifts to grade 1 and then to the comap. This states the equality of the underlying actual images; no separate named consequence, alternative quotient or stronger physical identification is introduced.

The original lattice, ghost, Bakalov-Kac, Scott Carnahan, Kalle Kytola and Mathlib attributions in the reused suppliers remain in force. The construction establishes BV-defect skew symmetry, vector Leibniz/Jacobi and literal LieRing/LieAlgebra structures on the stated actual image. It does not assert nontriviality of that image, a positive physical pairing, positivity in neutral or all-charge sectors, a rank-26 no-ghost theorem, complete string theory, a physical spacetime construction, an AdS/CFT correspondence or literature novelty.

Direct mathematical suppliers: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTCurrentIdentities`; `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance`; `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder`

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.DegreeOne`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.current_grade`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.current_jacobi`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.current_leftLeibniz`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.current_skew`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.degreeOneLieAlgebra`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.degreeOneLieRing`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalClass`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalImage`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalImageLieAlgebra`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalImageLieRing`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalImage_closed`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalLieSubalgebra`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalStates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalLie.physicalStates_current`
- Dependency: [D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTCurrentIdentities](LatticeBRSTCurrentIdentities.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance](LatticeMatterGhostNumberCovariance.md)
- Narrative reference: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder](../LatticeBRSTCohomologyBVSecondOrder.md)
- Narrative reference: [D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTCurrentIdentities](LatticeBRSTCurrentIdentities.md)
- Narrative reference: [D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeMatterGhostNumberCovariance](LatticeMatterGhostNumberCovariance.md)
