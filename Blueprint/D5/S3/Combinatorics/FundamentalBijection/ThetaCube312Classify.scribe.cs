using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaCube312ClassifyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaCube312Classify.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sum-indecomposable 312-avoiders fixed by the third iterate have size at most three.",
        H("Size Bound for Indecomposable Fixed 312-Avoiders"),
        Blocks(
            Node("fundamental-bijection-thetacube312classify-fixed312-large-absurd", "Exclusion beyond size three", "fixed312_large_absurd",
                "There is no sum-indecomposable 312-avoiding permutation of size greater than three fixed by three applications of the inverse fundamental bijection.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
