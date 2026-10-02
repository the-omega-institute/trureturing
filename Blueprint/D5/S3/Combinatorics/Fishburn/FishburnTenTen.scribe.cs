using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenTenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenTen.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.",
        H("FishburnTenTen"),
        Blocks(
            Node("fishburntenten-result-theorem", "Equinumerous avoidance classes", "result", "For every nonnegative n, the number of Fishburn permutations of length n avoiding 2143, 1423 and 3124 equals the number of classical permutations of length n avoiding 321, 2143 and 3124, and this number also equals the number of classical permutations of length n avoiding 231, 4132 and 2134.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("egge-fishburn-conjecture-10-10"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
