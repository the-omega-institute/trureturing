using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy.Polynomial;

internal sealed class ProductIntervalsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed product intervals.",
        H("Signed product intervals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("polynomial-productintervals-product-width"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Polynomial/ProductIntervals.product_width"),
                H("A product width estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For ordered intervals with nonnegative amplitude budgets A and B, the four-corner product interval lies in [-BA,BA] and has width at most B(d-c)+A(b-a). Comparing each pair of corners by a two-term product difference yields the width estimate."))),
                DescribeRole.Theorem)),
        []));
}
