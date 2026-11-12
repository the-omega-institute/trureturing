using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones;
internal sealed class SourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal-tail physical source rows", H("Four labeled chains and two centered rows"),
        Blocks(
            Paragraph(Text("For natural a,b,s, put k=a+b+2s and A=1+2^a+2^(a+b)+2^(a+b+s). The physical chains U,V,W,X start at 0,s,2s,2s+b and have lengths s,s,b,a. They are occurrences in the original word, not a sorting of residue values. Write x=2^a,y=2^b,z=2^s,D=y(z+1)+1 and N=xyz^2-1. Their old heads are A=xD+1, B=xz(y+1)+z+1, L=xz^2+z^2+z+1 and M=yz^2+D. The enlarged heads are 2A, Bn=2B-1, Ln=2L-z-1 and Mn=2M-D; its modulus is Q=2N+1.")),
            Paragraph(Text("The recurrences are zA=N+B, zB=N+L, yL=N+M, xM=N+A, and z(2A)=Q+Bn, zBn=Q+Ln, yLn=Q+Mn, xMn=Q+A. With a,b,s at least 2, each nonterminal occurrence is its head times its local power of two and is positive; every terminal is negative, with doubled value equal to successor minus modulus. These facts specialize the existing physical centered-source arithmetic to the equal-tail layout.")),
            Paragraph(Text("The old complete sum is zero. The enlarged values on inherited labels sum to -A, while the actual fresh label k has value A, so its complete sum is also zero. These are the exact row formulas consumed by both schedules. Source preparation alone does not choose a permutation or prove the full Circle J statement."))), []));
}
