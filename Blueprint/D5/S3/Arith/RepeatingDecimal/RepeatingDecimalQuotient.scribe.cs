using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.RepeatingDecimal;

internal sealed class RepeatingDecimalQuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-digit repeating-decimal shift and quotient certificate for one seventh.",
        H("The 142857 repeating-decimal quotient certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("repeating-decimal-142857-shift-quotient"),
                DeclarationHandle.Create(Prefix + "repeating_decimal_142857_shift_quotient"),
                H("Six-digit shift and period quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Over the rationals, shifting the generator 1/7 by six decimal places "
                        + "gives 142857 after subtracting the original generator, and dividing "
                        + "142857 by the period kernel 999999 returns 1/7. This is the exact "
                        + "arithmetic certificate used by the chapter example; it does not add "
                        + "a separate analytic definition of an infinite decimal expansion."))),
                DescribeRole.Theorem))));

}
