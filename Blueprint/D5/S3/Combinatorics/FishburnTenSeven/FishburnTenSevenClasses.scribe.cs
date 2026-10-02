using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenSeven;

internal sealed class FishburnTenSevenClassesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenClasses.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative orders between three monotone blocks characterize two triple-avoidance classes.",
        H("FishburnTenSevenClasses"),
        Blocks(
            Node("fishburntensevenclasses-shape-classes-iff-theorem", "Avoidance conditions on three blocks", "shape_classes_iff",
                "Let D followed by one, I, a peak, and J be a permutation of one through n, with D and J decreasing, I increasing, and every entry of I and J below the peak. It is a Fishburn permutation avoiding 1324, 2143 and 1423 if and only if no entry t of J has t plus one in I and every entry of J is below every entry of D. It is a Fishburn permutation avoiding 1324, 1423 and 3124 if and only if the same successor condition holds and every entry of D below the peak is below every entry of I.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
