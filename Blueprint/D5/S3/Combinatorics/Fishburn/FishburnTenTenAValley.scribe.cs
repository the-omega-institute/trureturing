using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenTenAValleyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenTenAValley.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.",
        H("FishburnTenTenAValley"),
        Blocks(
            Node("fishburntentenavalley-a-valley-forms-theorem", "Valley permutations and their insertion positions", "a_valley_forms", "Suppose two is at most bottom, bottom is less than peak, and peak is at most n. Concatenate the decreasing block from peak through bottom plus one, the entry one, the increasing block from peak plus one through n, and the decreasing block from bottom through two. The resulting permutation is Fishburn and avoids 2143, 1423 and 3124. Inserting n plus one at a position from zero through n preserves these conditions exactly at zero or at n minus bottom plus one.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
