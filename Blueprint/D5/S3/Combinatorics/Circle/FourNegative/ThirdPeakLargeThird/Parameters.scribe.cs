using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird;
internal sealed class ParametersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic parameters and full V capacity", H("Original labels and exact unbounded domain"),
        Blocks(Paragraph(Text("The original domain 2<=b<=a<d, d+3<=c yields the unbounded integer parameter inequalities and the strict or double-gap refinements. The native V-chain mass and its terminal identity bound the ceiling in the complete V stock. Conversion through Int.toNat is justified by positivity, and the exact cast equals the selected ceiling."))), []));
}
