using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH;
internal sealed class LargePContinuousDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unbounded a2 LargePContinuous", H("Unbounded a2 LargePContinuous"),
        Blocks(Paragraph(Text("For p>=64, h>=1 and q=2,4,8, the corrected lower epsilon and three exact rational chains cover every point of the unit interval. The original generic Chain, chain_hit and index bounds are reused. The new lower epsilon is 5/(8*(z+1))-1/(512*z), with z=4*q. Shifted polynomial inequalities verify the continuous parameter bounds without a finite parameter sample."))), []));
}
