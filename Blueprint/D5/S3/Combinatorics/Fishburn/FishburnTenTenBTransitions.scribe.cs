using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenTenBTransitionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenTenBTransitions.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.",
        H("FishburnTenTenBTransitions"),
        Blocks(
            Node("fishburntentenbtransitions-b-internal-transition-theorem", "Transitions after internal maximum insertion", "b_internal_transition", "Let p be a permutation of length n avoiding 321, 2143 and 3124. Suppose inserting n plus one at a position s strictly less than n preserves these conditions. Inserting n plus two into the resulting child at a position g from zero through n plus one preserves the same conditions exactly when g equals s plus one, or when g equals s plus two and inserting n plus one at position s plus one in p also preserves the same conditions.", DescribeRole.Theorem),
            Node("fishburntentenbtransitions-b-append-transition-theorem", "Transitions after appending the maximum", "b_append_transition", "Let p be a permutation of length n avoiding 321, 2143 and 3124, and suppose appending n plus one preserves these conditions. Inserting n plus two into this child at a position g from zero through n plus one preserves the conditions exactly when g equals n plus one, or when g is at most n and both the prefix of p before g and the suffix of p beginning at g are strictly increasing.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
