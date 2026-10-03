using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenSeven;

internal sealed class FishburnTenSevenShapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenShape.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Fishburn condition on a three-block permutation is a restriction on successive values.",
        H("FishburnTenSevenShape"),
        Blocks(
            Node("fishburntensevenshape-shape-fishburn-iff-theorem", "Fishburn condition for the block form", "shape_fishburn_iff",
                "Let D followed by one, I, a peak, and J be a permutation of one through n, with D and J decreasing, I increasing, and every entry of I and J below the peak. This permutation is Fishburn if and only if no entry t of J has t plus one in I.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
