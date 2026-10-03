using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DigitHankel;

internal sealed class BinaryDigitHankelNonzeroDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelNonzero.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sobolewski2026hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection induction evaluates the binary digit Hankel determinants at each center and its two adjacent indices.",
        H("Evaluations on the Threshold Triples"),
        Blocks(
            Node("binary-digit-hankel-nonzero-endpoint-evaluations", "The two adjacent determinant families", "endpoint_evaluations",
                "For every integer k at least two, put n_k = ceil(2^(k+2)/3). Then H(n_k-1,-2) = -2^((k+1)n_k - floor(3k/2) - 4) and H(n_k+1,-2) = 2^((k+1)n_k + floor(k/2) + 2 - (k mod 2)). Moreover E(n_k-1,-2) = 0 and E(n_k+1,-2) = 0. The initial values at k = 2 and the paired reflection recurrences give a simultaneous induction: reflection interchanges the two adjacent families, while the vanishing of E removes the additive term in the recurrence for H.", DescribeRole.Theorem),
            Node("binary-digit-hankel-nonzero-center-evaluations", "The determinant families at the centers", "center_evaluations",
                "For every nonnegative integer k, put n_k = ceil(2^(k+2)/3). Then E(n_k,-2) = (-1)^k 2^((k+1)n_k - floor((k+1)/2)) and 12 H(n_k,-2) = -(2^(k+1) + (-1)^k) E(n_k,-2). Reflection sends the center n_k to the preceding center for k at least two. The initial values at k = 0 and k = 1 and simultaneous induction give the two identities.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
