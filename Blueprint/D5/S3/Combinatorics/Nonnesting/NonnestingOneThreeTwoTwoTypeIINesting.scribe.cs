using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingOneThreeTwoTwoTypeIINestingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeIINesting.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type II insertion preserves avoidance of both nesting patterns.",
        H("Nonnesting under Type II Insertion"),
        Blocks(
            Node("nonnesting-nonnestingonethreetwotwotypeiinesting-typeii-nonnesting", "Type II preserves nonnesting", "typeII_nonnesting",
                "Suppose every upper letter exceeds the pivot, every letter of the lower order is smaller than the pivot, the upper word has exactly two copies of each of its letters, and the lower order has distinct entries. If the upper word and the concatenation of two copies of the lower order avoid 1221 and 2112, and every first occurrence in the upper word lies before the cut, the type II word also avoids 1221 and 2112.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
