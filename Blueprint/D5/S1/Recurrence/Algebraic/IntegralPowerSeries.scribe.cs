using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;
internal sealed class IntegralPowerSeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer-image formal power series", H("Integer-image formal power series"), Blocks(
            Describe.Lean(DescribeId.Create("integralpowerseries-integralseries"),
                DeclarationHandle.Create("D5/S1/Recurrence/Algebraic/IntegralPowerSeries.IntegralSeries"), H("Integer-image formal power series"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every characteristic-zero field and every ordinary power series, each coefficient is required to lie in the canonical image of an integer. The integer may depend on the degree, with no sign or size bound. The quantifiers include degree zero and impose no common bound on the integer representatives."))), DescribeRole.Definition))));
}
