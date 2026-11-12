using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones;
internal sealed class LowBAdjacentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Low-b adjacent chart", H("Twelve exact shifted polynomial gates"),
        Blocks(
            Paragraph(Text("For s>=2 and 2s+2<=a, b<=3s and b=a+1, choose u=2^(a-2s-2), v=2^(3s-b), w=1. Then z=8uv, x=256u^3v^2, y=512u^3v^2, with lambda=1, epsilon=0 and delta=0. The native X allocation is C=16u^2v. All natural gaps are nonnegative, and every chart variable is at least 1. Charts proves the complete eleven-slot coordinate identity and transports the native allocation to row 3 of Dyadic.")),
            Paragraph(Text("For each of the first three terminal seams, this module proves four inequalities: nonnegativity of the old doubled cumulative seam, its old successor-minus-one cap gap, the new doubled cumulative seam, and its new successor-minus-one cap gap. These are twelve exact inequalities for the actual head and mask polynomials, not numerical samples.")),
            Paragraph(Text("The proof shifts u=U+1,v=V+1,w=W+1 with U,V,W>=0. Each gate is identified by ring with its complete positive-coefficient Horner expression, whose nonnegativity follows by positivity. The expression literals do not introduce an external axiom. Charts consumes these bounds on this region; Physical and Schedule separately provide the occurrence inventory and all-prefix transport."))), []));
}
