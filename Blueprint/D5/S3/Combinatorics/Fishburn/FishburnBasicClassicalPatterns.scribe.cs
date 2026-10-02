using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnBasicClassicalPatternsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnBasicClassicalPatterns.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.",
        H("FishburnBasicClassicalPatterns"),
        Blocks(
            Node("fishburnbasicclassicalpatterns-maximum-classical-pattern-tests-theorem", "Occurrences created by maximum insertion", "maximum_classical_pattern_tests", "Let p be a permutation of one through n, and insert n plus one at a position s between zero and n. The child contains 321 exactly when p already contains 321 or the suffix beginning at s contains a decreasing pair. It contains 231 exactly when p already contains 231 or an entry before s exceeds an entry at or after s. It contains 4132 exactly when p already contains 4132 or the suffix beginning at s contains three entries in increasing positions whose first value is less than the third and whose third value is less than the second.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
