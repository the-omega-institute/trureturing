using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV;
internal sealed class ArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact unbounded quotient and simultaneous windows", H("Original labels and exact unbounded domain"),
        Blocks(Paragraph(Text("Put x=2^a, y=2^b, z=2^c, t=2^d, m=2^(c-d), w=2^(b-a-1). The original six exponent hypotheses imply x>=4, y>=2x, t>=y, t>=4x, z>=2t, 2<=m<=y/4, z=mt and y=2xw. No upper bound on any exponent is imposed.")),
                    Paragraph(Text("Let A=1+x+xy+xyz, B=1+t+xt+xyt, L=1+z+zt+xzt, K=1+y+yz+yzt and H=1+y+yz. The new heads are SU=2B-1, SV=2L-1-z and SW=2K-H. With h=floor((L-A)/(mB)), the exact Euclidean remainder R=L-A-hmB lies in [0,mB), and 0<=h<t/2. The proofs establish 2mh<=z-2m from the quotient bound.")),
                    Paragraph(Text("The old seam endpoints are E=mB-A, R, G=K-A-wL and zero. The new endpoints are Ep=2E-m, Rp=2R-z-1+mh, Gp=2G-H+w(z+1) and zero, with A added after the literal fresh insertion. Every old and selected new endpoint satisfies 0<=2e<=T-1 for its actual terminal head T. Both Gp and Gp+A satisfy their window simultaneously. The dyadic cases t=y and 2y<=t exhaust the original exponents and control the V remainder window.")),
                    Paragraph(Text("These private arithmetic lemmas are consumed by Allocation; the numerical window conditions are proved from the original hypotheses and are never substituted for them."))), []));
}
