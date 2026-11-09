# Original relative BRST cohomology and exact transverse representatives

## Abstract

Original relative BRST cohomology and exact transverse representatives

The state space is the original all-charge lattice carrier tensor the original occupation bc Fock space. The relative shell is fixedMomentum(p) intersect ker(b(0)) intersect ker(matterMode(0)+ghostVirasoro(0)), with unshifted total energy. Its differential is the restriction of the original totalCharge, whose invariance follows from the native Ward and covariance identities. The remainder is exactly Q-d0, including the chargeEnergy(p)c(0) contribution.

Let N=massShellCutoff(D,p)=(1-chargeEnergy(D,p)).toNat. For every lattice rank, integral momentum p including zero, null frame F, arbitrary finite complex transverse basis B, and matrix H satisfying H*gramComplex(D)=gramComplex(D)*H=1, actual h(Q-d0) preserves this shell. Induction on k shows that every nonzero actualBasis coefficient after k steps has original filtration degree at least -N+k. The accepted shell coefficient theorem simultaneously bounds that degree above by N. At k=2N+1 no coefficient survives. No finite-basis choice, real transverse basis or positivity of a Gram form enters this argument.

The actual signed ghost-number operator preserves all three shell constraints. Its commutators with delta and h have degrees +1 and -1, so it commutes with h*delta, delta*h and their finite inverse polynomials. On the literal b(0) kernel, a zero-quartet-count occupation has only the {1} sector: the possible {1,3} coefficient is killed by b(0). Consequently N*P0=P0 and P0*N=P0 on this shell. Corrected inclusion has ghost number one, and projection after N equals projection. Applying delta to corrected inclusion has ghost number two; projection would also give ghost number one. Over Complex the equality of the output with twice itself forces actual transferred differential zero, for every rank and momentum.

For cohomology require additionally rank(D)=26 and pPlus(F,p) nonzero. The native total-square anomaly gives Q squared zero. The actual quartet maps satisfy the unperturbed contraction, and native FinitePerturbation.Input.finite_perturbation applies at the proved exponent. Its corrected inclusion I, projection P and homotopy Hcorr give every original cycle x the decomposition x=I(P(x))+Q(Hcorr(x)). Actual image-Q boundaries are exactly the kernel of corrected projection on cycles. Mathlib's first isomorphism theorem therefore identifies the genuine cycles/image-Q quotient with the transverse ground target.

The polynomial target is defined independently by coefficients: each nonzero coefficient at exponent nu obeys weight(nu)+chargeEnergy(D,p)=1, where weight sums multiplicity times the positive oscillator frequency r+1. The original groundMap is injective on all polynomials, and maps this exact-energy submodule exactly to the shell intersect ker(M). Restriction to its image supplies the final polynomial coordinates. Corrected representatives have actual ghost number one and are unique modulo actual Q boundaries. A cycle of integer ghost number q different from one has an explicit primitive of ghost number q-1; at ghost number one the correction primitive has number zero.

The contraction and cohomology statements retain nonzero pPlus. All-charge nilpotence and zero transfer do not establish a contraction at p=0 or pPlus=0. These are algebraic statements about the specified original BRST model; they do not assert the full no-ghost theorem, Monster moonshine, a complete VOA/CFT or AdS/CFT construction, or new literature results.

The source escape audit remains unfinished at https://github.com/the-omega-institute/trureturing/issues/25942. Compilation of these algebraic results does not complete that registration.

**Theorem 1.1 (h_full_remainder_nilpotent_on_relativeMassShell).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.h_full_remainder_nilpotent_on_relativeMassShell`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.h_full_remainder_nilpotent_on_relativeMassShell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual ambient word h*(totalCharge-d0), iterated exactly 2*massShellCutoff(D,p)+1 times, vanishes on every vector of the literal original relative shell. The all-powers degree induction and shell preservation prove uniform nilpotence without a nilpotence hypothesis.

**Definition 1.2 (Number.shellQ).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.shellQ`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.shellQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original totalCharge restricted using totalCharge_mem_relativeMassShell, with both inverse-Gram equations. No replacement or zero-mode-corrected differential is used.

**Definition 1.3 (Number.shellN).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.shellN`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.shellN` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original signed occupation ghost-number operator restricted to the literal shell by its proved invariance.

**Definition 1.4 (Cohomology).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.Cohomology`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.Cohomology` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex vector space of actual original-Q cycles modulo the actual image of original Q, with rank 26 providing the image-to-kernel map.

**Definition 1.5 (cohomologyEquivEnergy).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.cohomologyEquivEnergy`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.cohomologyEquivEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original lattice of rank 26, null frame F, arbitrary finite complex transverse basis B, two-sided inverse Gram matrix H, and momentum p with pPlus(F,p) nonzero, a complex-linear equivalence from the original cycles/image-Q quotient to the independently defined exact-energy transverse polynomial submodule.

**Theorem 1.6 (off_charge_one_exact).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.off_charge_one_exact`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.off_charge_one_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under rank 26, both inverse-Gram equations and nonzero pPlus, every original-Q cycle x with actual ghost number q different from one equals Q(Hcorr(x)); the displayed primitive has actual ghost number q-1.

**Theorem 1.7 (exact_energy_representative).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.exact_energy_representative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.exact_energy_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same cohomology hypotheses, every original-Q cycle has a unique exact-energy transverse polynomial coordinate whose corrected representative differs from it by an actual original-Q boundary and has actual ghost number one. If the cycle itself has ghost number one, the constructed primitive has ghost number zero.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.Cohomology`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.cohomologyEquivEnergy`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.exact_energy_representative`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.h_full_remainder_nilpotent_on_relativeMassShell`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.off_charge_one_exact`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.shellN`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTCohomology.shellQ`
- Dependency: [D5/S3/HomologicalAlgebra/FinitePerturbation](../../HomologicalAlgebra/FinitePerturbation.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTFullOriginalRaising](LatticeBRSTFullOriginalRaising.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode](LatticeBRSTRelativeZeroMode.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare](LatticeBRSTSquare.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard](LatticeBRSTWard.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree](LatticeMatterGhostDegree.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction](LatticeQuartetContraction.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTGround](LatticeRelativeBRSTGround.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell](LatticeRelativeMassShell.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeRelativeShellDegreeBounds](LatticeRelativeShellDegreeBounds.md)
