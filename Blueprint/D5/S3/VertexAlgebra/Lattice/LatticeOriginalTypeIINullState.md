# Original Type II null state outside primary translations

## Abstract

The original Type II null state, finite oscillator obstruction and explicit relative BRST boundary.

The lattice data are arbitrary of rank 26. The actual complex matrix H satisfies both H Gc=1 and Gc H=1; the integral charge p is assumed, rather than asserted to exist, and has B(p,p)=-2. All operators act on the existing finite-charge oscillator carrier. No positivity, signature, unimodularity, transverse frame or cohomology comparison hypothesis is supplied.

**Definition 1.1 (The literal state).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState.typeII`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState.typeII` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For v=single(p,1), put S=L(-2)v+(3/2)T(Tv), with the actual original charge-sensitive translation T=L(-1). This is the classical Type II null-vector formula; original refers to the literal repository carrier and operators, not a claim of new physics.

**Theorem 1.2 (Physical nullity and the finite Fock obstruction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState.original_typeII_null_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState.original_typeII_null_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

S has actual L(0) weight one and is killed by every strictly positive integer mode. It is Hm-orthogonal to every actual positive-mode primary, hence in particular to every original weight-one physical state. S is nonzero and cannot equal T(u) for any original finite-charge u with L(1)u=0. The final image exclusion spells out T(P0) using the literal original modes, without a second public primary-space API.

The private functional ell_p sums the coefficient of X(i,1), the oscillator of frequency two, against q_i=sum_j G(i,j)p_j in charge p. Polynomial derivation and the original current commutator prove ell_p(Tu)=coeff_0((L(1)u)_p) for arbitrary finite-charge u. The charge-polynomial multiplication cannot contribute a single frequency-two variable. The frequency-two current extracts ell_p from L(-2)v, giving B(p,p); derivation gives ell_p(T²v)=B(p,p). Consequently ell_p(S)=-5. Both nonzero and nontranslation consume this actual coefficient.

The accepted Virasoro relation gives L(1)L(-2)v=3Tv, L(1)T²v=-2Tv, L(2)L(-2)v=9v and L(2)T²v=-6v. Higher positive modes vanish. The actual Hm_sugawaraMode identity moves the two negative modes to positive modes on the second argument; Hm_smul_left retains the conjugation of 3/2.

The coefficient obstruction separates this actual physical null state from literal primary translations. The relative BRST calculation below supplies an explicit boundary for the same state. Equality of comparison kernel and radical, a no-ghost theorem, product or Lie compatibility and the full string, Moonshine and AdS/CFT bridges remain outside these statements. The exact source reconstruction in the owning Reg mirror is a partial registration attempt: lawful readout, whole-family intervention, sensitivity, observational dependence and a validated four-slot Contract.Registration remain unfinished. No declared_validated status is asserted; the parent delivery owns the existing-issue exception and independent review.

**Definition 1.3 (The original relative primitive).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState.typeIIPrimitive`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState.typeIIPrimitive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the same ground state v, U=(3/2)(Tv tensor ket(empty))+v tensor ket(0,1). The occupation labels belong to the original SL2 ghost Fock space; the formula does not prescribe a replacement differential or shift the ghost grading.

**Theorem 1.4 (A nonzero relative boundary outside primary translations).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState.original_typeII_relative_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState.original_typeII_relative_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual totalCharge sends U to S tensor ket(1). Both lie in fixed momentum p, are killed by the original b(0), and have unshifted total L(0) equal to zero. Their native ghost numbers are zero and one respectively; the output is an actual cycle and is nonzero. The same matter state S retains the coefficient obstruction to T(ker L(1)) and hence to literal T(P0).

Finite capture of the original matter sum and the exact ghost vacuum cuts give Q(Tv tensor vacuum)=T²v tensor ket(1)-2v tensor ket(5). The original ghost Ward identities give Q(v tensor ket(0,1))=L(-2)v tensor ket(1)+3v tensor ket(5). The ket(5) terms cancel because (3/2)(-2)+3=0. The auxiliary ghost computations use the original CAR, finite support of R(1) on the vacuum, and the original ghost Virasoro vacuum action; no bounded numerical sample replaces an infinite sum.

This is a boundary computation in the original relative carrier. It asserts no identification of physical states modulo primary translations with BRST cohomology. The coupled ghost super-VOA derivation, no-ghost theorem and complete string-theory goal remain unfinished. Four-slot information-audit registration and independent review remain separate unfinished obligations owned by the parent delivery.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState.original_typeII_null_obstruction`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState.original_typeII_relative_boundary`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState.typeII`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeOriginalTypeIINullState.typeIIPrimitive`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell](LatticeRelativeMassShell.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraConformal](../LatticeSugawaraConformal.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/OriginalMatterHermitian](../SourceBPZ/OriginalMatterHermitian.md)
