using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicThuePowerIndexDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Factorization/QuadraticIdeals/GoldenCubicThuePowerIndex.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native binary Thue value calculates an actual index of integer orders.",
        H("Native Thue determinant and monogenic-order index"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-thue-signed-power-index"),
                DeclarationHandle.Create(Module + "native_power_index_det"),
                H("The marked determinant is the signed binary cubic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write tau as u alpha plus v beta. The multiplication table gives the last "
                    + "column of the change of basis from 1, alpha, beta to 1, tau, tau squared. "
                    + "Its determinant is the binary cubic itself with its original sign."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-thue-actual-power-index"),
                DeclarationHandle.Create(Module + "actual_factorization_power_index"),
                H("The native generator has exact index twice the square-role prime"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The oriented square and cube factors of the original Lucas equation select "
                    + "an integral tau in the actual splitting field. Its power triple has "
                    + "discriminant 324P to the fourth against field discriminant 81P squared. "
                    + "The additive quotient by the full monogenic order has cardinality 2P. "
                    + "The class-group and norm sieve are not asserted by this theorem."))),
                DescribeRole.Theorem))));
}
