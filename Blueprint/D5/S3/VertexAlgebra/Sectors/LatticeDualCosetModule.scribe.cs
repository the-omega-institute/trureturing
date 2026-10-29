using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeDualCosetModuleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dual-coset Fock sectors inside an auxiliary even lattice.",
        H("Dual-Coset Fock Modules by Invariant Restriction"),
        Blocks(
            Paragraph(Text("Let D be any finite-rank integral symmetric lattice with even diagonal, including rank zero. Let beta be any integral charge. E has Gram matrix [[G,beta],[beta^T,0]]. It may be singular or indefinite. Oscillators are complex multivariate polynomials indexed by Fin(rank(D)) times N, and V_D is their finite-support direct sum over integral charges. Rho renames old variables into E; its retraction kills the added variables. J_t sends single(n,P) to single((n,t),rho(P)); P_t extracts last charge t and applies that polynomial retraction. P_t J_t is identity. action(a) compresses the actual ambient Y_E(J0(a)) between J1 and P1. Truncation is inherited state by state; product compatibility is proved separately.")),
            Paragraph(Text("Creation series commute with the explicit polynomial rename by the pinned PowerSeries map and substitution laws. Translation polynomials and their coefficient supports transport along the same injective rename. The new acting charge has last coordinate zero, so the added cocycle terms vanish while every original half-diagonal contribution remains. Old current derivatives commute with rename, and derivatives in the added variables vanish. The original minus-one product theorem gives canonical multiplication recursion, which extends both coefficient transports to the entire original state space.")),
            Describe.Lean(
                DescribeId.Create("dual-coset-source-transport"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.source_transport"),
                H("All original source products"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original state a,b and integer m, J0((Y_D(a))_m b)=(Y_E(J0(a)))_m J0(b). No source-product compatibility is assumed. The auxiliary construction, coefficient transport and canonical polynomial multiplication recursion prove this identity."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dual-coset-action-monomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.action_monomial"),
                H("The original occurrence recipe"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integral charge a and every finite oscillator exponent e, action(single(a,monomial(e,1))) is shiftedWord(a,occurrences_D(e)). The recursion uses the original occurrence list. It does not compare independently chosen occurrence lists in the two lattices."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dual-coset-module-transport"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.module_transport"),
                H("Invariant all-state Fock realization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original state a, every module vector v and every integer m, J1((action(a))_m v)=(Y_E(J0(a)))_m J1(v). Thus every mode of every original input preserves this actual sector."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dual-coset-module-vacuum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.module_vacuum"),
                H("Vacuum action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D and beta, action(vacuum_D) is the identity field: its mode -1 is identity and every other integer mode is zero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dual-coset-module-input-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.module_input_derivative"),
                H("Input differentiation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original state a and every integer m, (action(T_D(a)))_m=-m (action(a))_(m-1). Only J0 transports the original translation to the ambient translation. Ambient translation is not restricted to sector one."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dual-coset-module-borcherds"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.module_borcherds"),
                H("Three supports and literal module Borcherds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original a,b, every module vector v and all integers p,q,r, each of moduleLeft, moduleFirst and moduleSecond has finite support on the natural offset i. With B(p,i) the complex cast of Ring.choose(p,i), moduleLeft(i)=B(p,i) action((Y_D(a))_(r+i)b)_(p+q-i)v, moduleFirst(i)=(-1)^i B(r,i) action(a)_(p+r-i)(action(b)_(q+i)v), and moduleSecond(i)=(-1)^i B(r,i) ((-1)^r action(b)_(q+r-i)(action(a)_(p+i)v)). The sum of moduleLeft is the sum of moduleFirst minus moduleSecond, equivalently the literal weighted difference. The exponent r is integral; the exponent i is natural. The original ambient Borcherds theorem supplies three supports, transported separately through the injective J1 before sums are subtracted."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dual-coset-physical-pairing-integral"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.physical_pairing_integral"),
                H("Exact physical dual pairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every rational vector mu satisfying sum_j G_ij mu_j=beta_i for every i, and every integral a, sum_ij a_i G_ij mu_j equals the rational cast of the integer sum_i a_i beta_i. No integrality of mu or unimodularity is required."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dual-coset-action-ground-coefficients"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.action_ground_coefficients"),
                H("Shifted ground coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integral a,n, every oscillator polynomial P and integer m, action(single(a,1))_m single(n,P) equals shiftedRawSingle(1,a,-m-1,n,P). In raw power k the creation coefficient index is k-B_D(a,n)-sum_i a_i beta_i+d, with d ranging over the finite coefficient support of translatedPolynomial_D(a,P). The multiplier is the original epsilon_D(a,n), including its half-diagonal term, and the resulting charge is a+n."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dual-coset-physical-ground-action"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.physical_ground_action"),
                H("Physical meaning of the actual ground action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every rational mu, integral beta, exact hDual, integral a,n, polynomial P and integer m, both the integral physical-pairing identity and the complete shifted ground coefficient formula hold. The index of each creation coefficient is -m-1-B_D(a,n)-sum_i a_i beta_i+d. Thus the physical dual shift is proved, rather than supplied as a field-isomorphism premise."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dual-coset-action-current-coefficients"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.action_current_coefficients"),
                H("Literal shifted currents"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every current i, integral charge n, polynomial P and integer m, the source state single(0,X_(i,0)) acts as single(n,shiftedCurrentPolynomial(1,i,n,m)(P)). Negative m multiplies by X_(i,-m-1). Mode zero multiplies by B_D(e_i,n)+beta_i. Positive m is m times sum_j G_ij partial_(j,m-1)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dual-coset-action-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.action_expansion"),
                H("Entire all-state normal-product action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite-charge input v, action(v) is the finite sum over n in its charge support and e in the monomial-coordinate support of v(n), of its actual monomial coefficient times shiftedWord(n,occurrences_D(e)). The field action is defined for arbitrary nonhomogeneous inputs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dual-coset-retraction-injection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.retraction_injection"),
                H("Explicit sector retraction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer t and actual module vector v, P_t(J_t(v))=v, with the concrete charge extraction and complementary-variable evaluation defined above."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dual-coset-injection-injective"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.injection_injective"),
                H("Each actual sector injection is injective"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer t, the concrete map J_t is injective, including rank zero. This follows from the explicit retraction, without any field compatibility premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dual-coset-fractional-dual-action"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule.fractional_dual_action"),
                H("A fractional charge-changing action"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For G=[2], mu=1/2 and beta=1, the exact dual equation holds and mu is not integral. The mode zero of the original charge -1 ground state sends the charge zero constant vector to the charge -1 constant vector with coefficient one. This uses the same full all-state action as the general theorem."))), DescribeRole.Theorem),
            Paragraph(Text("The original lattice construction is due to Bakalov-Kac, math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI 10.1142/9789812702562_0001. Original all-state field, locality, residue and Jacobi sources retain their upstream attribution, including Scott Carnahan, vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache-2.0. The new bridge is the explicit invariant realization on the actual original Fock carrier. It is not a claim of global mathematical novelty.")),
            Paragraph(Text("These are ungraded vertex-algebra module statements. The action of the original conformal state, shifted Virasoro and translation operators, exact rational positive energy, attained minimum, finite grades, coherent representative changes, discriminant classification, irreducibility, fusion, anomaly, Monster or Moonshine realization, CFT, string theory and AdS/CFT remain outside these statements. Under positive definiteness, the later energy target is spectrum inclusion in h+N; equality requires positive rank, because rank zero has only energy zero.")))));
}
