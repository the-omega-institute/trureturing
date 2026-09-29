using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SemiMeanderSecondDiagonal;

internal sealed class Stage4Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage4.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/hogan2026a400429");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Terminal path arguments characterize connectivity for the remaining local pairing cases.",
        H("Terminal Connectivity"),
        Blocks(
            Describe.Lean(DescribeId.Create("case-a"),
                DeclarationHandle.Create(Prefix + "connected_iff_A"),
                H("First terminal case"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The first admissible endpoint pattern is connected exactly under its stated rank condition."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("case-c"),
                DeclarationHandle.Create(Prefix + "connected_iff_C"),
                H("Second terminal case"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The second terminal pattern has the corresponding necessary and sufficient connectivity condition."))),
                DescribeRole.Theorem)),
        []));
}
