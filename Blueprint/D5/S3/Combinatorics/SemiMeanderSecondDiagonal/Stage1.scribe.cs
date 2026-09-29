using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SemiMeanderSecondDiagonal;

internal sealed class Stage1Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage1.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/hogan2026a400429");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Midpoint cuts isolate the local upper pairings and identify the four unpaired endpoints on each side.",
        H("Midpoint Cuts"),
        Blocks(
            Describe.Lean(DescribeId.Create("four-endpoints"),
                DeclarationHandle.Create(Prefix + "leftCut_four_endpoint_pairing_shape"),
                H("Four local endpoints"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At winding n minus four, the left cut has four endpoints in local upper pairs; their noncrossing shape has the classified alternatives."))),
                DescribeRole.Theorem)),
        []));
}
