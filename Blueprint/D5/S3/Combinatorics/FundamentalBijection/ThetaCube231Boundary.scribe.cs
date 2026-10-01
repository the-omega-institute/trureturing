using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaCube231BoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaCube231Boundary.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Indecomposable fixed 231-avoiders have prescribed entries at their boundaries.",
        H("Boundary Entries of Fixed 231-Avoiders"),
        Blocks(
            Node("fundamental-bijection-thetacube231boundary-terminal-value-next-to-max", "The second and last entries", "terminal_value_next_to_max",
                "A sum-indecomposable 231-avoiding permutation of size n greater than three fixed by the third inverse iterate ends with n minus one and has one in position one, with positions numbered from zero.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
