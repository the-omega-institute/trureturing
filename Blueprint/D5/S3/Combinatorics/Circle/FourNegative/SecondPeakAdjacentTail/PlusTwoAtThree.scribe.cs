using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail;
internal sealed class PlusTwoAtThreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact polynomial mask bounds: PlusTwoAtThree", H("Paired source arithmetic"),
        Blocks(
            Paragraph(Text("The nonnegative parameters describe an entire continuous orthant of the adjacent-tail source heads. Each inequality is proved by an exact polynomial identity with nonnegative coefficients after multiplying by a strictly positive denominator.")),
            Paragraph(Text("These inequalities bound the original mask stocks and the paired old and new residual windows. The integer selector substitutes exact dyadic quotient data into this family; no finite range of exponents is assumed."))), []));
}
