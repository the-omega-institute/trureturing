using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenTenCTransitionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenTenCTransitions.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.",
        H("FishburnTenTenCTransitions"),
        Blocks(
            Node("fishburntentenctransitions-c-insertion-transitions-theorem", "Transitions in the second classical class", "c_insertion_transitions", "Let p be a permutation of length n avoiding 231, 4132 and 2134, and suppose insertion of n plus one at position s from zero through n preserves these conditions. Inserting n plus two into the child at a position g from zero through n plus one preserves the conditions exactly in one of three cases: s equals n, g is at most n, and insertion of n plus one at g in p is permitted; s is less than n and g equals s; or g equals n plus one, appending n plus one to p is permitted, and the prefix of p before s is strictly increasing.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
