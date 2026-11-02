using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class OrdinaryEulerProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary partitions identify the actual reciprocal Euler product and prove strict all-degree positivity.", H("Ordinary Euler Product"), Blocks(
            Paragraph(Text("Mathlib Nat.Partition.hasProd_powerSeriesMk_card_restricted is used with predicate True under the actual discrete rational T2 topological ring structure. Its supplier is Weiyi Wang, Apache 2.0. Mathlib pentagonalSeries is the actual Euler product. These are ordinary positive parts, with no odd-part restriction.")),
            Node("0", "partitionSeries", "The complete ordinary partition count series, using the unrestricted predicate True.", DescribeRole.Definition),
            Node("1", "coeff_partitionSeries_ge_one", "For every natural degree, including zero, an ordinary partition exists, so its coefficient is at least one.", DescribeRole.Theorem),
            Node("2", "partitionSeries_mul_euler", "The ordinary partition series times the actual pentagonal Euler product equals one, by actual topological products and the geometric factor identity.", DescribeRole.Theorem),
            Node("3", "euler_constant_one", "The actual pentagonal Euler series has constant coefficient one.", DescribeRole.Theorem),
            Node("4", "partitionSeries_eq_euler_inverse", "The complete ordinary partition series equals the unit reciprocal of the actual Euler product.", DescribeRole.Theorem),
            Node("5", "coeff_mul_nonnegative", "Finite convolution preserves coefficientwise nonnegativity.", DescribeRole.Theorem),
            Node("6", "coeff_pow_nonnegative", "Every natural power of a coefficientwise nonnegative rational power series has nonnegative coefficients.", DescribeRole.Theorem),
            Node("7", "coeff_mul_ge_right", "A nonnegative series with constant coefficient one preserves a coefficientwise lower bound under complete finite convolution.", DescribeRole.Theorem),
            Node("8", "coeff_euler_inverse_pow_ge_one", "Every positive natural power of the actual reciprocal Euler series has every coefficient at least one.", DescribeRole.Theorem),
            Paragraph(Text("The finite convolution bounds include every natural degree and every positive power. They provide positive partition factors; they do not establish any signed eta-quotient pattern without the exact theta identities, proved separately in CubicThetaCoreProduct and CubicThetaIdentities."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("ordinary-euler-product-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
