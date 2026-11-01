using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones;
internal sealed class LowBSeparatedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Low-b separated chart", H("Twelve exact shifted polynomial gates"),
        Blocks(
            Paragraph(Text("For s>=2 and 2s+2<=a, b<=3s and b>=a+2, choose u=2^(a-2s-2), v=2^(b-a-2), w=2^(3s-b). Then z=16uvw, x=1024u^3v^2w^2, y=4096u^3v^3w^2, with lambda=2v, epsilon=v and delta=0. The native X allocation is C=32u^2vw. All natural gaps are nonnegative, and every chart variable is at least 1. Charts proves the complete eleven-slot coordinate identity and transports the native allocation to row 4 of Dyadic.")),
            Paragraph(Text("For each of the first three terminal seams, this module proves four inequalities: nonnegativity of the old doubled cumulative seam, its old successor-minus-one cap gap, the new doubled cumulative seam, and its new successor-minus-one cap gap. These are twelve exact inequalities for the actual head and mask polynomials, not numerical samples.")),
            Paragraph(Text("The proof shifts u=U+1,v=V+1,w=W+1 with U,V,W>=0. Each gate is identified by ring with its complete positive-coefficient Horner expression, whose nonnegativity follows by positivity. The expression literals do not introduce an external axiom. Charts consumes these bounds on this region; Physical and Schedule separately provide the occurrence inventory and all-prefix transport."))), []));
}
