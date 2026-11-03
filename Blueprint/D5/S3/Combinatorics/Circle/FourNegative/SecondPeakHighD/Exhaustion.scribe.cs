using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD;
internal sealed class ExhaustionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exhaustion", H("Exhaustion"),
        Blocks(Paragraph(Text("The dyadic partition has no hcase: a>=5 uses the checked ceiling and parity tail, a=3,4 with H>=2 uses the checked scaled families, and H=0,1 uses the residue and fixed rows. All exponents remain unbounded."))), []));
}
