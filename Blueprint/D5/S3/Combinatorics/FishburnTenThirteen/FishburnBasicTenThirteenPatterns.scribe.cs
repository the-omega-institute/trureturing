using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenThirteen;

internal sealed class FishburnBasicTenThirteenPatternsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicTenThirteenPatterns.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "New occurrences of 2413 and 2431 after maximum insertion are determined by triples crossing the insertion position.",
        H("Crossing Pattern Tests"),
        Blocks(
            Node("fishburnbasictenthirteenpatterns-maximum-crossing-pattern-tests", "Occurrences involving the new maximum", "maximum_crossing_pattern_tests",
                "Let p be a permutation of one through n and let s be an insertion position from zero through its length. Inserting n + 1 at s gives an occurrence of 2413 exactly when p already contains 2413 or there are positions i, j, k with i less than s, s at most j, j less than k, and k less than the length of p for which the entry at j is less than the entry at i and the entry at i is less than the entry at k. The corresponding criterion for 2431 replaces these value inequalities by the entry at k being less than the entry at i and the entry at i being less than the entry at j. Positions are numbered from zero.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
