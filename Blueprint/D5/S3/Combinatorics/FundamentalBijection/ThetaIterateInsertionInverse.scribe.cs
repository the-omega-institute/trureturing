using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateInsertionInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertionInverse.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prescribed boundary shape of an inverse image permits removal of three letters.",
        H("Recovering a Smaller Cycle from Insertion"),
        Blocks(
            Node("fundamental-bijection-thetaiterateinsertioninverse-insertion-cycle-inverse", "The recovered inner permutation", "insertion_cycle_inverse",
                "For a permutation w of size n at least five beginning with n whose inverse image begins with n, n minus one and ends with one, n minus two, there is a permutation q of size n minus three beginning with n minus three and ending with one such that I of the inverse image of q is the inverse image of w. That inverse image of q is a first-maximum permutation whose fundamental image and cycle from its maximum are q; if w avoids 132, then q avoids 132.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
