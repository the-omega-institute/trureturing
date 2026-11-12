using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeMatterGhostNumberCovarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-state number covariance of the original matter-ghost modes",
        H("All-state number covariance of the original matter-ghost modes"), Blocks(
            Paragraph(Text("The operators are the original bc occupation ghostNumber and the tensor operator N = tensorNumber D, acting on State D. The field is the original occupation-word state-field map, and mu_n = originalMode D n. Write B_j = ghostB D j, P for the actual parity, and K(x,y) = mu_0(B_(-1)x,y). All five public statements retain their original telescopes; no H, inverse-Gram or rank-26 hypothesis occurs.")),
            Paragraph(Text("LatticeData retains exactly its rank, integral symmetric Gram matrix and even diagonal. The signed site weight is the original odd-minus-even occupation count, not a replacement number convention. Pointwise finite ghost words and tensor convolutions prove statements for every integer mode and every actual state; no uniform truncation, positivity, nonzero-rank or fixed-charge premise is assumed.")),
            Paragraph(Text("Source-specific four-slot Reg audits for the public theorems remain unfinished: https://github.com/the-omega-institute/trureturing/issues/29596. Adjacent templates do not supply the complete original telescopes, source selections and checked escape coordinates for these owners. No declared_validated registration is claimed; this delivery uses the explicit linked-issue exception.")),
            Describe.Lean(DescribeId.Create("latticematterghostnumbercovariance-ghost-number-field"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostNumberCovariance.ghost_number_field"),
                H("Number covariance for every original ghost field"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any a in the original bc occupation Fock space and integer n, ghostNumber * (Y(a)[[n]]) - (Y(a)[[n]]) * ghostNumber = Y(ghostNumber a)[[n]]. Signed normal products add the original occupation weights; divided derivatives retain each generator weight. Induction through the actual sorted occupation word, then linear extension from ket states, covers all ghost states. No homogeneous a is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latticematterghostnumbercovariance-number-mode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostNumberCovariance.number_mode"),
                H("Full-state covariance at every integer tensor mode"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D : LatticeData, x,y : State D and integer n, N(mu_n(x,y)) = mu_n(Nx,y) + mu_n(x,Ny). Here N = tensorNumber D and mu_n = originalMode D n. The ghost-field commutator passes through the actual matter/ghost tensor coefficient and its pointwise finite convolution. Both inputs may mix ghost numbers, momenta and energies; there is no matrix, critical-rank, Gram-inverse or parity hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latticematterghostnumbercovariance-number-b-apply"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostNumberCovariance.number_b_apply"),
                H("The original lowering law on actual tensor states"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D, integer m and x : State D, N(B_m x) = B_m(Nx) - B_m x. This directly reuses the native N_b operator relation from the original relative BRST module. Its live consumer current_number uses it together with number_mode; no new grading axiom is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latticematterghostnumbercovariance-current-number"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostNumberCovariance.current_number"),
                H("The unsigned current has integer degree minus one"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D, x,y : State D and p,q : Int, if Nx = (p : Complex) times x and Ny = (q : Complex) times y, then N(K(x,y)) = ((p+q-1 : Int) : Complex) times K(x,y). The exact original lowering relation for B_(-1) and all-integer number_mode give the result. Negative degrees, zero states and all original lattice charges remain included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latticematterghostnumbercovariance-number-one-parity"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostNumberCovariance.number_one_parity"),
                H("Ghost number one implies actual odd parity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D and original state x, Nx = x implies Px = -x. In the finite support of fullBasis.repr x, each nonzero coefficient has integer ghost charge one. The original odd-minus-even occupation count forces odd total occupation cardinality, hence actual parity -1. Matter states may be mixed; no restriction to a pure tensor, a charge sector, a positive Gram form or nonzero rank is made."))), DescribeRole.Theorem),
            Paragraph(Text("Attribution remains with the original ghost construction, Scott Carnahan's signed residue calculus and Mathlib. The result supplies actual number covariance and number-one parity for later current arguments. It does not provide a positive physical form, a no-ghost theorem, a complete string model, spacetime reconstruction, AdS/CFT or a literature novelty claim.")),
            Paragraph(Text("Direct mathematical suppliers: "), Ref("D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading"), Text("; "), Ref("D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder")))));
}
