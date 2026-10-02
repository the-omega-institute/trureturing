using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenTenAMonotoneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenTenAMonotone.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.",
        H("FishburnTenTenAMonotone"),
        Blocks(
            Node("fishburntentenamonotone-a-monotone-forms-theorem", "Monotone permutations and maximum insertion", "a_monotone_forms", "For every nonnegative n, both the increasing and decreasing permutations of one through n are Fishburn permutations avoiding 2143, 1423 and 3124. Among positions zero through n, inserting n plus one into the increasing permutation preserves these conditions exactly at zero or at a position s with n at most s plus one. For the decreasing permutation the permitted positions are exactly zero and n.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
