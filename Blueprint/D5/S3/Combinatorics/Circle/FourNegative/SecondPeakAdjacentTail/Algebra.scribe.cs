using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail;
internal sealed class AlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent-tail heads and residual windows", H("Paired source arithmetic"),
        Blocks(
            Paragraph(Text("For x=2^a, z=2^c and q=2^(b-c), define A=1+x+xqz+xqz^2, B=1+2z+2xz+2xqz^2, L=1+z+2z^2(1+x) and K=1+qz+qz^2+2qz^3. The new heads are SU=2B-1, SV=2L-1-z and SW=2K-(1+qz+qz^2). The residuals E=(v+1)B-K+mL and F=(v+1)SU-SW+mSV obey F=2E+(qz-m)(z+1)-v.")),
            Paragraph(Text("The physical terminal order is U,X,W,V. Both first windows and all later windows reduce to exact nonnegative polynomial sides together with integer mask stocks. The integer ceiling -((-D)/L) has residual between zero and L-1; a positive D bounded by stock times L gives a ceiling between one and stock."))), []));
}
