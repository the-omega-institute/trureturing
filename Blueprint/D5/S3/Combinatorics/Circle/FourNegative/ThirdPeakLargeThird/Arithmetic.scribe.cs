using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird;
internal sealed class ArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer ceilings and doubled terminal windows", H("Original labels and exact unbounded domain"),
        Blocks(Paragraph(Text("For x=2^a, y=2^b, z=2^c and t=2^d, use A=1+x+xy+xyz, B=1+t+xt+xyt, L=1+z+zt+xzt and K=1+y+yz+yzt. The new heads are 2A, SU=2B-1, SV=2L-1-z and SW=2K-(1+y+yz). A doubled terminal endpoint D lies in its window exactly when 0<=D<=T-1. The ceiling v=ceil((L-B)/(2B)) has remainder (2v+1)B-L in [0,2B).")),
                    Paragraph(Text("The inequalities y>=4, y<=x<=t and 8t<=z imply 4B+z<A and B<L. The strict b<a branch has 2y<=x and 2x<=t; the nonadjacent equal b=a branch has 4x<=t. Each branch proves every required old and new terminal window by exact polynomial margins."))), []));
}
