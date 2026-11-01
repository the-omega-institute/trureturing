using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;
internal sealed class SchurOperatorBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite rectangular matrix has an L2 operator bound from its absolute row and column sums.",
        H("Finite Schur operator bound"),
        Blocks(Describe.Lean(DescribeId.Create("finite-schur-operator-bound"),
            DeclarationHandle.Create("D5/S3/SpectralTopology/SchurOperatorBound.l2_opNorm_le_schur"),
            H("Row and column bounds control the Euclidean operator"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/juexu2026finiteschur")),
            Blocks(Paragraph(Text("For every RCLike field K, finite row type I and finite column type J, with decidable equality on J, let A be an I by J matrix over K. If real R,C are nonnegative, every sum over j in J of the norm of A(i,j) is at most R, and every sum over i in I is at most C, then the Euclidean operator norm of A is at most sqrt(R*C). Empty row or column types are included. The norm is explicitly Matrix.Norms.L2Operator. Weighted Cauchy–Schwarz first bounds the squared action of each row, and summation uses the column bounds. The theorem is a minimal licensed port of Jue Xu's proof and is consumed by the actual Apollonian late adjacency estimate."))), DescribeRole.Theorem))));
}
