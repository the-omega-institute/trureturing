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
                "The public occupation HasProd theorem is applied to z(i,k) = -q^(k+1). The product retains complex phases and occurrence parity; no energy-parity replacement is made."),
            Theorem("signed-eta-normalization", "normalized_signed_integer_eq_eta", "Eta normalization",
                "For q = exp(2 pi I tau) in the unit disk, the signed occupation product is the rank-th power of the quotient of the Euler products at q and q squared. The identity (1-q^n)(1+q^n)=1-q^(2n), public eta nonvanishing, and the exact vacuum exponential give exp(-2 pi I tau r/24) times the occupation sum equal to (eta(tau)/eta(2 tau))^r, including rank zero."))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
