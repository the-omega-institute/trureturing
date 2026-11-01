using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap;
internal sealed class CeilingGatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three exact gates for the signed ceiling",
        H("The selector range and the old second seam"),
        Blocks(
            Paragraph(Text("Let t=2xR, z=2xtZ and y=2zlambda, with integer x>=4 and R,Z,lambda>=1. Set D=y(z+1)+1, A=xD+1, L=xzt+zt+z+1, M=tyz+D, N=xyzt-1 and E=2N-M-(t-1)A. The three private polynomial results establish E>=0, E<=2lambdaL(z-1) and 2lambdaL<=A-1.")),
            Paragraph(Text("For the positive denominator den=2lambdaL, Selection uses the signed integer ceiling H=-floor(-E/den). The first two gates allow its exact division argument to prove 0<=H<=z-1 before any conversion to a natural mask. That argument also proves 0<=delta<den for delta=den H-E. The third gate then supplies the old second successor cap delta<=A-1.")),
            Paragraph(Text("The gate proofs use explicit shifted polynomial identities at x=4+u, R=1+v, Z=1+w and lambda=1+q, followed by nonnegativity of every term. Integer division and the Euclidean remainder are handled in Selection; the present module supplies the polynomial inequalities they require. No real-valued relaxation replaces the ceiling or its native mask."))), []));
}
