using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter;
internal sealed class ArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paired after-W windows", H("Original labels and exact unbounded domain"),
        Blocks(Paragraph(Text("For d=a put x=2^a,y=2^b,z=2^c, A=1+x+xy+xyz, B=1+x+x^2+x^2y, L=1+z+zx+x^2z and K=1+y+yz+xyz. Use SU=2B-1, SV=2L-1-z and SW=2K-(1+y+yz). Window(e,T) means 0<=2e<=T-1.")),
                    Paragraph(Text("With x=sy, s>=2,y>=4,z>=2sy, the exact slacks combine the chosen r,v with delta=rA-vB and epsilon=2rA-vSU. Only the selected residue branch must satisfy the selector premises. All eight old/new windows are preserved."))), []));
}
