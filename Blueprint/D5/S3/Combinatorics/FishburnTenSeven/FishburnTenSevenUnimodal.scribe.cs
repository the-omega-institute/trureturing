using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenSeven;

internal sealed class FishburnTenSevenUnimodalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenUnimodal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Avoiding 213 and 312 forces a list of distinct entries to increase and then decrease around its maximum.",
        H("FishburnTenSevenUnimodal"),
        Blocks(
            Node("fishburntensevenunimodal-unimodal-iff-theorem", "Unimodality and two-pattern avoidance", "unimodal_iff",
                "Let a list with no repeated entry consist of a left block, a peak, and a right block, with every entry of the two blocks below the peak. The list avoids both 213 and 312 if and only if the left block is strictly increasing and the right block is strictly decreasing.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
