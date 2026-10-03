using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateExceptionalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateExceptional.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three explicit orbit words leave the avoidance layers at successive depths.",
        H("Explicit Exceptional Orbits"),
        Blocks(
            Node("fundamental-bijection-thetaiterateexceptional-cyclic-last-endpoint", "The exceptional orbit chain", "cyclic_last_endpoint",
                "For size n at least three, let C be two through n followed by one and D be n followed by two through n minus one and then one. The fundamental images of C and D are respectively n followed by one through n minus one and C; D avoids 132 through depth two, and P of C followed by n plus one does so as well. For n at least four, let E be P of the increasing word of size n minus two. Its image is D; E lies at depth five but not six, D at depth four but not five, and C at depth three but not four.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
