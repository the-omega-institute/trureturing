using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenThirteen;

internal sealed class FishburnTenThirteenBIndecomposableDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBIndecomposable.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Component lists determine the active-position polynomial of indecomposable Fishburn permutations avoiding 2431 and 3241.",
        H("A Component-Weighted Indecomposable Recurrence"),
        Blocks(
            Node("fishburntenthirteenbindecomposable-inductive-counting", "The active-position polynomial recurrence", "inductive_counting",
                "Fix a positive integer n and call a position in a Fishburn permutation avoiding 2431 and 3241 active when insertion of its new maximum preserves those conditions. Let the component lists be all lists of nonempty sum-indecomposable permutations whose direct sum is a Fishburn permutation of length n avoiding both patterns. For a component list with r components, let t be the number of components after the first and let a be the number of active positions in its first component. The sum over sum-indecomposable avoiders of length n + 1 of X to the power their number of active positions minus two equals the sum over component lists of X to the power r minus one, plus the sum over component lists of X to the power one when t is zero or to the power t otherwise, multiplied by the sum of X to the power e over nonnegative e strictly less than a minus two. This is an identity of polynomials with rational coefficients, and subtractions in exponents and range lengths are truncated at zero.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
