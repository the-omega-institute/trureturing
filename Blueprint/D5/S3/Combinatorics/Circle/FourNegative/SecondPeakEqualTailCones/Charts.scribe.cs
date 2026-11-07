using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones;
internal sealed class ChartsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exhaustive upper-cone chart transport", H("Natural gap cases close all twelve gates"),
        Blocks(
            Paragraph(Text("For s>=2, the two upper clauses are (2s+2<=a and a+1<=b) or (s+1<=a and max(a+1,3s+1)<=b). The first clause splits at a=3s, then at adjacency b=a+1, or at b=3s+1 when a<3s. This yields the high-adjacent, high-separated, high-b/low-a, low-b-adjacent and low-b-separated charts.")),
            Paragraph(Text("The remaining range s+1<=a<=2s+1 has b>=3s+1. It splits into a=s+1, s+2<=a<=2s, and a=2s+1. Each chart proves equality of all eleven dyadic slots and of epsilon and delta, using natural gap inequalities to prevent truncated-exponent errors. All chart variables are powers of two and hence at least 1, including endpoint equalities.")),
            Paragraph(Text("Transport then applies the corresponding twelve integer polynomial gates to the native allocation. The eight chart cases therefore supply the first three old and new seam bounds throughout the two-clause upper union. The lower cone 2<=a<s, b>=2s+1 uses the separate ceiling construction; neither this case split nor the endpoint asserts all of Circle J."))), []));
}
