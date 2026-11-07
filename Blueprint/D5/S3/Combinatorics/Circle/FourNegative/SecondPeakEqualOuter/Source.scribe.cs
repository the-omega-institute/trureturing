using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter;
internal sealed class SourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact equal-outer physical source", H("Physical construction"),
        Blocks(Paragraph(Text("For d=a the chain lengths are [a,c,b,a] and starts [0,a,a+c,a+c+b]. Set x=2^a,z=2^c,y=2^b, A=1+x+xy+xyz, B=1+x+x^2+x^2y, L=1+z+xz+x^2z, H=1+y+yz, K=H+xyz. Old heads are A,B,L,K; new heads are 2A,SU=2B-1,SV=2L-1-z,SW=2K-H. The four original terminals are a-1,a+c-1,a+c+b-1,a+b+c+a-1. PacketNormalForm.Source supplies actual values, signs and the distinct scalar totals old=0 and new-over-old-labels=-A. The sole fresh label is k=a+b+c+a with actual new value A. No centered-residue or source-total theorem is reimplemented."))), []));
}
