using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenSeven;

internal sealed class FishburnTenSevenBEquivDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBEquiv.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An interval construction produces permutations in the second triple-avoidance class.",
        H("FishburnTenSevenBEquiv"),
        Blocks(
            Node("fishburntensevenbequiv-b-typeii-mem-theorem", "Membership of the second interval form", "B_typeII_mem",
                "Let two be at most d, d at most h, h less than m, and m at most n. For any Fishburn permutation q of length d minus two avoiding 213, concatenate the decreasing interval from n through m plus one, the decreasing interval from h through d, one, the increasing interval from h plus one through m minus one, m, and q with every entry increased by one. The resulting list is a Fishburn permutation of length n avoiding 1324, 2143 and 3124.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
