using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail;
internal sealed class PhysicalWordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paired strips with literal fresh insertion", H("Paired source arithmetic"),
        Blocks(
            Paragraph(Text("The original word concatenates four positive banks and their negative terminals in U,X,W,V order. Its cut is d, immediately after the first negative terminal. Inserting the literal new label k at that cut puts its new mass A at the beginning of the second positive bank.")),
            Paragraph(Text("Native paired terminal masses give old postterminal values B-A, (v+1)B-K+mL and (v+1)B-L. The new values are SU-2A, (v+1)SU-SW+mSV and (v+1)SU-SV. Each exact window controls the corresponding monotone positive bank and terminal. Separate native zero totals close both strips."))), []));
}
