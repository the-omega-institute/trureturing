using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2;
internal sealed class QTwoStructuralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second peak: unbounded q-two selector", H("QTwoStructural"),
        Blocks(Paragraph(Text("For arbitrary integers p>=8 and h>=1, put j=(32p+6) mod 9, v=(16p+3-5j)/9, m=hj and M=h(2p-1). The residue equation 9v+5j=16p+3 implies 1<=v<=2p. Substitution into the actual old and new physical endpoints proves all four windows, including the distinct third heads and the zero seam, with every stock bound. No window or feasibility certificate is assumed.")),
            Paragraph(Text("For p=2^P with P>=3 and h=2^H with unrestricted natural H, j lies below the full mask 2^(P+1)-1. Multiplication by 2^H shifts both masks without carries, preserving bit inclusion. The strict inequality m<M makes this inclusion proper. Natural and integer casts transport the arithmetic windows to Good. Finite uses this result for its six q=2 cases with p in {8,16,32} and h in {1,2}. The p=4 and q>=4 cases are outside this selector.")),
            Describe.Lean(DescribeId.Create("q-two-dyadic-good"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/QTwoStructural.q_two_dyadic_good"), H("q_two_dyadic_good"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For all natural P,H, if 3<=P, there exist natural v,m,M such that Good (2^P) 2 (2^H) v m M true. Here Good includes 1<=v, 2v<=8p, m<M, 2M<16hp, Submask m M and every exact old/new window."))), DescribeRole.Theorem)), []));
}
