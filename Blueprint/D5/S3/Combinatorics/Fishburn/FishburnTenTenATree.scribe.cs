using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenTenATreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenTenATree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fishburn permutations and classical permutations avoiding specified patterns are classified by their forms and permitted insertion positions.",
        H("FishburnTenTenATree"),
        Blocks(
            Node("fishburntentenatree-a-classification-theorem", "Structural alternatives for the Fishburn class", "a_classification", "Every Fishburn permutation of length n at least two avoiding 2143, 1423 and 3124 is increasing, is obtained from the increasing permutation by reversing the interval from low plus one through high with low plus two at most high and high at most n, has the form of a decreasing block from peak through bottom plus one followed by one, an increasing block from peak plus one through n, and a decreasing block from bottom through two with two at most bottom and bottom less than peak and peak at most n, or permits insertion of the next maximum only at position zero.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
