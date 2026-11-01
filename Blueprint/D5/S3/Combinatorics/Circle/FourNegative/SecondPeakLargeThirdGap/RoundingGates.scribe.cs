using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap;
internal sealed class RoundingGatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial reserves for the exact rounded new seam",
        H("Lower and upper bounds through K and J"),
        Blocks(
            Paragraph(Text("Use the Algebra expressions with integer x>=4 and R,Z,lambda>=1, t=2xR, z=2xtZ and y=2zlambda. Thus D=y(z+1)+1, A=xD+1, L=xzt+zt+z+1, Ln=2L-z-1 and E=2(xyzt-1)-(tyz+D)-(t-1)A. The two private results prove K=L(A-D-2)-E(z+1)>=0 and J=L(A-1)-2lambdaL Ln-K>=0.")),
            Paragraph(Text("For H=ceil(E/(2lambdaL)), put delta=2lambdaLH-E and T=2delta+A-D-2lambdaH(z+1)-2. Selection proves the exact identity L T=Ln delta+K. Since L and Ln are positive and 0<=delta<2lambdaL, K>=0 gives T>=0 and J>=0 gives T<=A-1. The bounds therefore control the actual rounded second enlarged seam with successor A.")),
            Paragraph(Text("Both gate proofs give explicit polynomial equalities after shifting x,R,Z,lambda to their lower bounds and then establish termwise nonnegativity. This module supplies the reserves K and J; the signed ceiling, remainder identity and physical identification are consumed in Selection and Schedule. It asserts no independent public theorem or unrestricted joint lift."))), []));
}
