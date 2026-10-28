using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourZhuFiniteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Dimension of the Actual Norm-Four Zhu Quotient.",
        H("Finite Dimension of the Actual Norm-Four Zhu Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normfourzhufinite-circle"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite.circle"),
                H("Actual homogeneous circle product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a lattice D, natural weight n and actual states u,v, circle is the entire sum over j from zero through n of binomial(n,j) times u_(j-2)v."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normfourzhufinite-zhuo"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite.zhuO"),
                H("Literal O-space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every lattice D, charge a and complex s, let S be the actual negative-axis-word vacuum span. The O-space is the ambient complex span of all circle(n,u,v) with u,v in S and actual axis L0(u)=n u. Both arguments stay in S; the definition uses the actual eigenvalue equation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normfourzhufinite-actual-zhu-quotient-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourZhuFinite.actual_zhu_quotient_finite"),
                H("Actual finite additive quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite integral symmetric even-diagonal lattice D, charge a with B(a,a)=4, and complex s with s squared equal to one, literal O is contained in S and the existing additive quotient of S by the inverse image of O is finite dimensional over the complex numbers, with dimension at most three. No determinant invertibility or rank specialization is required."))),
                DescribeRole.Theorem),
            Paragraph(Text("The actual C2 homogeneous pair decomposition and its three representatives are reused. Finite eigenvalue separation extracts a single homogeneous component of the C2-plus-representatives decomposition. For a pair of grade N, its minus-two product equals the full circle product minus terms of strictly smaller grade. Strong induction on grade places every actual vacuum descendant in O plus the span of the vacuum, axis and its minus-one square.")),
            Paragraph(Text("Finite spanning of the literal additive quotient follows without a multiplication premise or an independence premise. This is the classical C2-to-Zhu finite filtration argument in the actual lattice carrier, following Zhu's associative algebra construction. The norm-four vector retains its Dong-Mason-Zhu and Shimakura attribution. The complex multiplication and cubic presentation are the subject of NormFourZhuAlgebra.")))));
}
