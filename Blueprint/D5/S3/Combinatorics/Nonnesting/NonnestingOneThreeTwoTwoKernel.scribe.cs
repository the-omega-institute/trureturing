using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingOneThreeTwoTwoKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoKernel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The catalytic equation yields a quadratic and cubic coefficient recurrence.",
        H("Kernel Recurrence for 1322 Avoidance"),
        Blocks(
            Node("nonnesting-nonnestingonethreetwotwokernel-catalytic-recurrence", "Coefficient recurrence from the catalytic equation", "catalytic_recurrence",
                "Let S be a rational power series with constant coefficient one, let C be the Catalan series evaluated at xu, and suppose a series F with polynomial coefficients in u satisfies (1 - u + x times u squared times (S + C)) times F = 1 - u + xu times S squared + x times u squared times C times S. For every positive n, the coefficient s_n of S equals the sum of s_i times s_(n-i) over positive i smaller than n, plus the sum of s_i times s_j times s_k over nonnegative triples with i + j + k = n - 1.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
