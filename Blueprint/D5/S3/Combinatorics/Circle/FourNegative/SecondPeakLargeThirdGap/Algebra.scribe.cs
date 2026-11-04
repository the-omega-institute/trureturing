using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap;
internal sealed class AlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact four-chain expressions and fourteen ordered gates",
        H("Algebra for the native ceiling selector"),
        Blocks(
            Paragraph(Text("The internal algebra uses integer variables x,y,z,t. Write D=y(z+1)+1, A=xD+1, B=xt(y+1)+t+1, L=xzt+zt+z+1, M=tyz+D and N=xyzt-1. The enlarged heads are Bn=2B-1, Ln=2L-z-1 and Mn=2M-D. The ceiling numerator is E=2N-M-(t-1)A. The two rounding polynomials are K=L(A-D-2)-E(z+1) and J=L(A-1)-2lambdaL Ln-K.")),
            Paragraph(Text("The independent parameterization sets t=2xR, z=2xtZ and y=2zlambda. In the physical application x=2^a, R=2^(d-a-1), Z=2^(c-a-d-1) and lambda=2^(b-c-1). The separated gap hypotheses give x>=4 and R,Z,lambda>=1. The algebraic gate proofs use these integer lower bounds; the conversion to actual powers and physical labels belongs to Schedule.")),
            Paragraph(Text("The fixed gate order is B+M-2A; 2B-2A+Mn-1; 2A-B-1; 2A-2B; E; 2lambdaL(z-1)-E; A-1-2lambdaL; K; J; B-lambdaL; Bn-lambdaLn; 2lambdaL-B-1; 2lambdaLn-Bn-1; N-A. Selection consumes all fourteen entries. This module supplies private expressions, while FirstSeams, CeilingGates, RoundingGates and TailGates prove their nonnegativity. The owning public result is the Endpoint joint lift on the separated gap cone; these expressions alone assert no source order."))), []));
}
