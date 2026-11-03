using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH;
internal sealed class SmallSelectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All unbounded dyadic h and q for the four small p", H("All unbounded dyadic h and q for the four small p"),
        Blocks(
            Describe.Lean(DescribeId.Create("secondpeaka2allh-smallselection-small-q-partition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallSelection.small_q_partition"),
                H("small q partition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of all unbounded dyadic h and q for the four small p. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("secondpeaka2allh-smallselection-small-p-allh-selection"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallSelection.small_p_allh_selection"),
                H("small p allh selection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of all unbounded dyadic h and q for the four small p. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Paragraph(Text("For every natural p in {4,8,16,32}, every Q>=1 and every H>=2, small_p_allh_selection produces natural v,m,M and a Bool before with Submask m M, strict m<M, and rowBounds 4 p (2^Q) (2^H) v m M before. In particular, all three old and actual charged new endpoint bounds and the v,M stocks hold simultaneously.")),
            Paragraph(Text("The proof partitions q into q>=64 or the five values 2,4,8,16,32 without bounding Q. The first branch uses the signed-ceiling construction. For each small q the proof consumes the existing all-H structural Good construction at p=2^P with P in {2,3,4,5}. The q=2,p=4 case uses the original late boundary v=5, m=5*2^H, M=8*2^H-1. Good supplies the literal proper Submask and all four physical windows; castSucc projects the first three windows into rowBounds. Since Y=2*(4*h*p*q), the strict bound 2*M<Y gives the original integral slack 2*M<=Y-2. No fixed positive certificate or upper bound on H is used. The source input is the supplied small-p all-h construction. These results are a consumed selector component of the original a=2 all-b>d program; they do not assert a physical Circle permutation or complete the original endpoint."))), []));
}
