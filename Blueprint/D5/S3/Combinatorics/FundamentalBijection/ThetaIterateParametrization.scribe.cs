using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateParametrizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateParametrization.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-step recursion enumerates the eligible first-maximum parameters.",
        H("Recursive Enumeration of First-Endpoint Parameters"),
        Blocks(
            Node("fundamental-bijection-thetaiterateparametrization-first-endpoint-parametrization", "The family decomposition and count", "first_endpoint_parametrization",
                "Let A(h) consist of first-maximum permutations r of size h for which P(r) avoids 132 through depth two. For h at least six, A(h) is the union of U(h), the decreasing word, W(h), and I applied to the members of A(h minus three) whose cycle from their maximum equals their fundamental image. Its cardinality is the latter count plus three and is the cardinality of A(h minus three) plus two. For every h at least two, the cardinality of A(h) is the integer part of (2h plus one) divided by three.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
