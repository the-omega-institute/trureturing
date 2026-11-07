using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers;
internal sealed class DescendingMasksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical descending masks",
        H("Exact dyadic ratios"),
        Blocks(Paragraph(Text("For a>=b>=c>=2, the ratios 2R/Z and 2R/T are actual dyadic positions. Their unions with the low bit two fit the U chain and are nested. Writing R=TP and T=ZL identifies their integer values, including coincident positions. Outside Z=4, R=2T, the descending polynomial inequalities give exact reserve bounds with remaining charges A-1, A-Z-1 and A-(TZ+T+1). The baseWord is the literal four-block masked word with these U masks and no V or W reserves."))), []));
}
