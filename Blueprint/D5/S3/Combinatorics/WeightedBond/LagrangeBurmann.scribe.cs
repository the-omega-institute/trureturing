using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeightedBond;

internal sealed class WeightedBondLagrangeBurmannDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeightedBond/LagrangeBurmann.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/gonzalezdeleonwachs2026weighted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Formal Lagrange-Bürmann extraction.",
        H("Formal Lagrange-Bürmann extraction"),
        Blocks(
            Node("lagrange_power_coefficient",
                "Over any commutative rational algebra, if A has constant coefficient zero and satisfies A = X F(A), then for positive k at most d, d times the degree-d coefficient of A to the k equals k times the degree-(d minus k) coefficient of F to the d.", DescribeRole.Theorem),
            Node("lagrange_burmann",
                "Over any commutative rational algebra, if A has constant coefficient zero and satisfies A = X F(A), then (n+1) times the degree-(n+1) coefficient of g(A) equals the degree-n coefficient of g prime times F to the (n+1).", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string name, string prose, DescribeRole role, Formula? formula = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(name), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);
}
