# Locally nilpotent perturbation on literal cohomology

## Abstract

Pointwise inverse polynomials yield actual quotient inverses and incoming primitives.

Over a commutative ring R, let c be the FinitePerturbation.Input on R-modules U,V: d0²=D²=0 for D=d0+delta, p i=id, d0 i=p d0=0, d0 h+h d0=id-i p and h²=h i=p h=0. Assume pointwise local nilpotence: for every x∈V some n satisfies (h delta)^n x=0. The global linear operator K=(1+h delta)⁻¹ agrees on that x with Σ_{j<n}(-h delta)^j x. Injectivity of 1+h delta uses a cutoff for x-y, and surjectivity uses a cutoff for the desired output. This constructs a linear inverse without a uniform exponent. The opposite inverse is J=1-delta K h. Set I=K i, P=p J, H=K h and d_U=p delta I.

Attribution: Gugenheim–Lambe–Stasheff's algebraic perturbation lemma is implemented by the existing finite and locally nilpotent suppliers. The literal quotient and generic descent follow FinitePerturbationCohomology, the repository LatticeOriginalAbsoluteZeroCohomology pattern and Joël Riou's Mathlib homology construction. Mathlib's units, linear maps, quotient equality and induction retain Johannes Hölzl, Mario Carneiro, Kevin Buzzard and Yury Kudryashov attribution, Apache 2.0. Batteries.OpenPrivate is due to Mario Carneiro and Microsoft Corporation, Apache 2.0.

**Definition 1.1 (Global quotient equivalence from vectorwise finite inverses).**

Lean statement: `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cohomologyEquiv`

*Formalization.* `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cohomologyEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For c and the stated pointwise nilpotence hypothesis, the source is the actual ker D modulo range(D into ker D); the target is the same quotient construction for the actual transferred d_U. Its square-zero and chain laws are derived by locally_nilpotent_perturbation. Submodule.mapQ descends P and I because P D=d_U P and D I=I d_U carry actual images to actual images.

On a source cycle x the round trip has difference x-I(P x)=D(H x), so H x is the boundary witness in the source quotient. On a target cycle u the retract P I=id gives equality before quotienting. Quotient induction proves both inverse laws on all classes. Evaluation of H x uses a finite cutoff for h x; evaluation of I u uses a cutoff for i u. A single exponent for the entire carrier is unnecessary.

**Theorem 1.2 (The homotopy gives the actual difference primitive).**

Lean statement: `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cycle_primitive`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cycle_primitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a D-cycle x∈V, the asserted equality is D(H x)=x-I(P x). It evaluates D H+H D=id-I P at x and uses D x=0. Thus the discrepancy between x and its included projection is the differential of a specified vector in V.

Here H x=K(h x). Choose n only for h x with (h delta)^n(h x)=0; the global inverse evaluates as the finite alternating polynomial on that vector. The equality does not say x itself is exact unless the included projected contribution is also removed. It is precisely the source inverse witness used in the cohomology equivalence.

**Theorem 1.3 (Projection of each literal cycle representative).**

Lean statement: `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cohomologyEquiv_mk`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cohomologyEquiv_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x∈V with D x=0, the equivalence sends its actual quotient class to [P x] in ker d_U/range d_U. The target membership follows from d_U(P x)=P(D x)=0; the theorem reuses the representative readout of cohomologyProjection.

The projected vector is p J x=p(x-delta K(h x)). A cutoff for h x evaluates the K term as a finite polynomial, while the globally defined J makes P linear on all V. Changing a lift by D y changes P x by d_U(P y), exactly the boundary required for quotient descent.

**Theorem 1.4 (Corrected inclusion of each transferred cycle).**

Lean statement: `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cohomologyEquiv_symm_mk`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cohomologyEquiv_symm_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For u∈U with d_U u=0, the inverse equivalence sends [u] to [I u]. The corrected representative I u=K(i u) is a D-cycle by the inclusion-chain law. A cutoff for i u gives the concrete finite sum Σ_{j<n}(-h delta)^j(i u).

This is the representative formula of cohomologyInclusion, which descends I using its actual chain identity. A target boundary d_U v lifts to D(I v). The formula therefore describes the inverse on the literal kernel/image quotients, including when d_U is nonzero.

**Theorem 1.5 (Transferred exactness produces an original-module preimage).**

Lean statement: `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.boundary_iff_transferred_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.boundary_iff_transferred_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a D-cycle x, exactness D y=x in V is equivalent to d_U u=P x for some u∈U. The forward implication takes u=P y, using P D=d_U P. It compares genuine differential images on the full modules.

For the reverse implication the constructed vector is I u+H x. The inclusion-chain law gives D(I u)=I(d_U u), and cycle_primitive gives D(H x)=x-I(P x); their sum is x. Both corrections can be evaluated by finite inverse polynomials with their own vector-dependent cutoffs. No zero-transfer premise is used.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.boundary_iff_transferred_boundary`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cohomologyEquiv`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cohomologyEquiv_mk`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cohomologyEquiv_symm_mk`
- Truth anchor: `D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cycle_primitive`
- Dependency: [D5/S3/HomologicalAlgebra/FinitePerturbationCohomology](FinitePerturbationCohomology.md)
- Dependency: [D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbation](LocallyNilpotentPerturbation.md)
