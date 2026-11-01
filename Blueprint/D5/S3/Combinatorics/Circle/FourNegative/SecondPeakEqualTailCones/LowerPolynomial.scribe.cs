using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones;
internal sealed class LowerPolynomialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Thirteen positivity gates for the lower cone", H("Exact polynomial certificates with nonnegative coordinates"),
        Blocks(
            Paragraph(Text("Write x=4+u, z=2x+v and y=2z^2+w for nonnegative integers u,v,w. With the source heads A,B,L,M and enlarged Bn,Ln,Mn, the thirteen polynomials are B+M-2A; 2A-B-1; Bn+Mn-4A; 4A-Bn-1; 2B-A-L; A-B-L; L(2Bn-3A-Ln)+Az^2; L(3A-Bn-1-Ln)-Az^2; A-2L; Az^2; L(A-1-2Ln)-Az^2; M-L; and L(y-3)-M+1.")),
            Paragraph(Text("Each polynomial is strictly positive throughout this coordinate orthant. The source contains the complete positive coefficient expressions: ring proves their equality to the defining head polynomial, then positivity uses u,v,w>=0. The boundary w=0 is included. Supplied integer coefficients are expression literals; their external generation is not used as a proof assumption.")),
            Paragraph(Text("The first eleven inequalities feed the lower seam bounds, while M-L>0 makes the ceiling numerator positive and L(y-3)-M+1>0 supplies its capacity bound. Actual dyadic parameters are connected to this orthant by LowerCeiling. These thirteen expressions are distinct from the ninety-six upper-chart seam gates."))), []));
}
