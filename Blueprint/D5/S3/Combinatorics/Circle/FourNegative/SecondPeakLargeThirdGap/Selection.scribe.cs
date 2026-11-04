using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap;
internal sealed class SelectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact signed ceiling and all paired seam bounds",
        H("From fourteen gates to a single integer selector"),
        Blocks(
            Paragraph(Text("For integer x>=4 and R,Z,lambda>=1, use t=2xR, z=2xtZ and y=2zlambda with the Algebra heads A,B,L,M and enlarged heads Bn,Ln,Mn. The module consumes all fourteen gates from FirstSeams, CeilingGates, RoundingGates and TailGates. Its signed ceiling is H=-floor(-E/(2lambdaL)), with E=2N-M-(t-1)A and delta=2lambdaLH-E.")),
            Paragraph(Text("The ceiling-range argument identifies delta with the Euclidean remainder of -E modulo the positive denominator. It proves 0<=H<=z-1 and 0<=delta<2lambdaL before Schedule converts H to a natural mask. The doubled second enlarged seam T=2delta+A-D-2lambdaH(z+1)-2 satisfies L T=Ln delta+K exactly; positivity and the K,J gates give 0<=T<=A-1.")),
            Paragraph(Text("The resulting private SeamBounds record contains both first seam ranges with successors M and Mn, both second seam ranges with successor A, and both third doubled seam ranges with successors B and Bn. It also retains the ceiling range, remainder range, rounding identity and fresh bound A<=N. Schedule applies this complete record to the same four-gap physical source; there is no independent choice of an order for each row."))), []));
}
