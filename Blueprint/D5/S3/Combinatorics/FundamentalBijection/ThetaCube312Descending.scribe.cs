using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaCube312DescendingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaCube312Descending.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A successor greater than one is incompatible with the fixed indecomposable 312-avoiding configuration.",
        H("The Entry Following the Maximum"),
        Blocks(
            Node("fundamental-bijection-thetacube312descending-successor-gt-one-absurd", "Exclusion of a large successor", "successor_gt_one_absurd",
                "There is no sum-indecomposable 312-avoiding permutation of size greater than three fixed by the third inverse iterate whose entry immediately after the maximum, read as zero beyond the word, is greater than one.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
