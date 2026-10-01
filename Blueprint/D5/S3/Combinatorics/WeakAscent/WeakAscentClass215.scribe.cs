using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscentClass215Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscentClass215.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two weak ascent sequence classes in Class 215 have equal cardinalities in every length.",
        H("Equinumerosity of the Weak Ascent Sequence Classes in Class 215"),
        Blocks(
            Node("weak-ascent-weakascentclass215-result", "The Class 215 equinumerosity", "result",
                "For every nonnegative integer n, the number of weak ascent sequences of length n avoiding 100, 101, 110 and 201 equals the number avoiding 021, 101, 201 and 210.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
