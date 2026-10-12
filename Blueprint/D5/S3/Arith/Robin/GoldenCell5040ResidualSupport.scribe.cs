using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class GoldenCell5040ResidualSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/GoldenCell5040ResidualSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four-prime residual branch of the 5040 congruence cell is covered by the existing eight-prime Robin theorem.",
        H("The 5040 Cell and a Four-Prime Residual"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("modeq-2241-card-le-eight-of-residual-card-le-four"),
                DeclarationHandle.Create(Prefix + "modEq_2241_card_le_eight_of_residual_card_le_four"),
                H("Residual support bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The congruence cell has fixed prime support {2,3,5,7}. If the residual has at most four distinct prime factors, the union bound gives at most eight for the whole integer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("robin-of-modeq-2241-residual-card-le-four"),
                DeclarationHandle.Create(Prefix + "robin_of_modEq_2241_residual_card_le_four"),
                H("Robin on the residual branch"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing theorem for at most eight distinct prime factors proves Robin's inequality on this branch. Residuals with five or more distinct prime factors remain open."))),
                DescribeRole.Theorem))));
}
