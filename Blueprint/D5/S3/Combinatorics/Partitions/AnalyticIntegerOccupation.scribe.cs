using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class AnalyticIntegerOccupationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed integer-frequency occupations with occurrence parity and an absolute product majorant.",
        H("Signed Integer Occupations"),
        Blocks(
            Theorem("sqrt-norm-majorant", "sqrt_norm_majorant", "Square-root norm majorant",
                "For every finite colour type and complex q with norm q < 1, the norm of the signed integer occupation monomial is bounded by the square root norm raised to the public odd occupation energy. The proof uses occurrence parity for the sign and oddEnergy_le_twice_integerEnergy for the exponent comparison."),
            Theorem("summable-signed-occupations", "summable_norm_signed_integer_occupations", "Absolute occupation summability",
                "The square-root majorant and the public odd occupation summability theorem give absolute summability, including q = 0 and the empty colour type."),
            Theorem("signed-occupation-product", "hasProd_signed_integer_occupations", "Signed integer occupation product",
                "The public occupation HasProd theorem is applied to z(i,k) = -q^(k+1). The product retains complex phases and occurrence parity; no energy-parity replacement is made."))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
