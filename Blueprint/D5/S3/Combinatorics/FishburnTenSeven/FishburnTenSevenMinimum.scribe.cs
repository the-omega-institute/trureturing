using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenSeven;

internal sealed class FishburnTenSevenMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenMinimum.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Occurrences of four patterns in a Fishburn permutation can be placed relative to its minimum.",
        H("FishburnTenSevenMinimum"),
        Blocks(
            Node("fishburntensevenminimum-minimum-pattern-tests-theorem", "Pattern tests around one", "minimum_pattern_tests",
                "Let p be a Fishburn permutation of one through n, and let one be the position of its entry one. An occurrence of 1324 exists if and only if three positions after one form 213, and an occurrence of 1423 exists if and only if three positions after one form 312. If p avoids 1324, an occurrence of 2143 exists if and only if positions first, second and third with first before one and one before second before third have the entry at first below that at third below that at second. Under the same avoidance assumption, an occurrence of 3124 exists if and only if such positions have the entry at second below that at first below that at third.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
