using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaTwistedColumnsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaTwistedColumns.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local finiteness retains every integer triple, and Laurent constant projection gives the complete weighted lattice sum.", H("CubicThetaTwistedColumns"), Blocks(
            Paragraph(Text("Local finiteness retains every integer triple, and Laurent constant projection gives the complete weighted lattice sum.")),
            Node("0", "variableUnit", "The invertible Laurent monomial for the integer Jacobi index.", DescribeRole.Definition),
            Node("1", "constantUnit", "The embedding of a scalar unit into the Laurent coefficient ring.", DescribeRole.Definition),
            Node("2", "variable_zpow", "Every integer power of the Laurent variable is its corresponding single monomial.", DescribeRole.Theorem),
            Node("3", "twist", "The Laurent ring homomorphism multiplying the variable by a scalar unit.", DescribeRole.Definition),
            Node("4", "twist_single", "A twisted Laurent monomial carries exactly the scalar phase at its integer index.", DescribeRole.Theorem),
            Node("5", "twistedCube", "The product of the Jacobi series twisted by u, its inverse, and one.", DescribeRole.Definition),
            Node("6", "columnZero", "The linear projection to the complete Laurent constant column.", DescribeRole.Definition),
            Node("7", "twisted_triple_term", "The zero-sum triple has norm exponent x^2+xy+y^2 and phase u^(x-y).", DescribeRole.Theorem),
            Node("8", "hasSum_twisted_column_zero", "All integer pairs occur in the constant Laurent column, with their exact phase.", DescribeRole.Theorem),
            Node("9", "twisted_column_zero", "The projected product is the full finite-fibre weighted theta.", DescribeRole.Theorem),
            Paragraph(Text("Statements and proof dependencies come from the exact scoped Lean report. Classical theta mathematics is attributed to Borwein and Cooper as quoted in Huang et al. arXiv:2507.16644v1. The repository InversionSeq207 triple-product supplier is reused. No literature priority, worldwide absence, journal-typeset inspection, CI or original-problem acceptance is certified by this document."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubicthetatwistedcolumns-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
