using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnBasicClassicalParentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnBasicClassicalParents.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.",
        H("FishburnBasicClassicalParents"),
        Blocks(
            Node("fishburnbasicclassicalparents-classical-maximum-insertion-bijection-theorem", "Maximum insertion and deletion", "classical_maximum_insertion_bijection", "For any collection of classical patterns and any nonnegative n, inserting n plus one gives a bijection from pairs consisting of an avoiding permutation of one through n and an insertion position whose child avoids the same patterns to the avoiding permutations of one through n plus one. Deleting the unique maximum recovers both the parent and its insertion position.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
