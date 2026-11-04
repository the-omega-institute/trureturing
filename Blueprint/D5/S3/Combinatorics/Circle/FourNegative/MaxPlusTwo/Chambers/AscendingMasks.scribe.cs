using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers;
internal sealed class AscendingMasksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ascending physical reserve masks",
        H("Exact masks and source seams"),
        Blocks(Paragraph(Text("For a<=b<=c and a<c, the V mask is the nonnegative rounded quotient of e2-3A by 2e1. Its exact dyadic cases give e2<=S2<=2e2-A and S2<e2+2e1, including b=c and a=b,c=a+1. The W mask and low U release follow the literal constructor. Their capacity and reserve bounds retain the adjacent T=2R family, the a=2 boundaries, and the T=R equality face."))), []));
}
