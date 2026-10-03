using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerStripProductAlgebraDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductAlgebra.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The period-four signed weights and period-two Narayana weights yield endpoint formulas in one second-order recurrence.",
        H("Endpoint Formulas for Periodic Continuants"),
        Blocks(
            Node("cigler-strip-product-algebra-minus-endpoints", "Endpoints for the signed weights", "minus_endpoints",
                "Let t and z belong to any commutative ring. Define F_0 = 0, F_1 = 1 and F_{n+2} = (1 - (1 + t^2)z^2)F_{n+1} - t^2 z^4 F_n. Let P and Q satisfy the continuant recurrence with coefficients repeating z, tz, -z, -tz and initial values (0, 1) and (1, 1), respectively. For every nonnegative integer m, P_{4m+1} = F_{m+1} + (z + z^2)F_m, Q_{4m+1} = F_{m+1} - tz^2 F_m, P_{4m+2} = F_{m+1} + tz^2 F_m, and Q_{4m+2} = F_{m+1} - z(F_{m+1} + t^2 z^2 F_m).", DescribeRole.Theorem),
            Node("cigler-strip-product-algebra-plus-endpoints", "Endpoints for the squared Narayana weights", "plus_endpoints",
                "Let t and z belong to any commutative ring. Define F_0 = 0, F_1 = 1 and F_{n+2} = (1 - (1 + t^2)z^2)F_{n+1} - t^2 z^4 F_n. Let P and Q satisfy the continuant recurrence with coefficients alternating z^2 and t^2 z^2 and initial values (0, 1) and (1, 1), respectively. For every nonnegative integer k, P_{2k+1} = F_{k+1} + z^2 F_k, Q_{2k+1} = F_{k+1}, P_{2k} = F_k, and Q_{2k} = F_{k+1} + t^2 z^2 F_k.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
