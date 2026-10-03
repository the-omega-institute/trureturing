using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerStripProductSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductSeries.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At both endpoint indices corresponding to heights 4m and 4m + 1, the Narayana numerator and denominator factor into signed continuants.",
        H("Separate Numerator and Denominator Factorizations"),
        Blocks(
            Node("cigler-strip-product-series-factorization", "The four continuant products", "product_factorization",
                "For t and z in any commutative ring, let P^+(t, z) and Q^+(t, z) be the continuants with coefficients alternating z and tz, and let P^-(t, z) and Q^-(t, z) be the continuants with coefficients repeating z, tz, -z, -tz. Each numerator P has initial values (0, 1), and each denominator Q has initial values (1, 1). For every nonnegative integer m and each index j equal to 4m + 1 or 4m + 2, P^+_j(t^2, z^2) = P^-_j(t, z)P^-_j(-t, -z) and Q^+_j(t^2, z^2) = Q^-_j(t, z)Q^-_j(-t, -z). The endpoint formulas and addition and doubling identities for the second-order recurrence give the two numerator products and the two denominator products.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
