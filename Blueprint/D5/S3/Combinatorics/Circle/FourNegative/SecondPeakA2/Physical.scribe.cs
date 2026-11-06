using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2;
internal sealed class PhysicalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second peak SecondPeakA2: Physical", H("Physical"),
        Blocks(Paragraph(Text("Set p=2^(d-c), q=2^(c-2), and h=1 or 2 according as b=d+1 or b=d+2. Thus z=4q, t=4pq and y=8hpq. The generic physical banks allocate every original label exactly once. The same sigma and literal fresh ear at j satisfy both complete OriginalOrder structures at the unchanged original seed. No rotation or assumed source certificate is introduced.")),
            Describe.Lean(DescribeId.Create("complete-original-orders"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Physical.complete_original_orders"), H("complete_original_orders"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("theorem complete_original_orders (b c d : \u2115) (hc : 3\u2264c) (hd : c+2\u2264d)     (hb : b=d+1 \u2228 b=d+2) :     \u2203 sigma : List (Fin (2+b+c+d)), \u2203 j : \u2115, j\u22642+b+c+d \u2227       OriginalOrder (2+b+c+d) (1+2^2+2^(2+b)+2^(2+b+c)) sigma \u2227       OriginalOrder (2+b+c+d+1) (2*(1+2^2+2^(2+b)+2^(2+b+c)))         (earWord (2+b+c+d) sigma j)"))), DescribeRole.Theorem)), []));
}
