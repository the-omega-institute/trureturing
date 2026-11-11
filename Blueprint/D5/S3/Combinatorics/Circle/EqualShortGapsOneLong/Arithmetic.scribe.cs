using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.EqualShortGapsOneLong;

internal sealed class ArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native charges and packet drift for equal short gaps",
        H("The same physical phase in both coordinates"),
        Blocks(
            Paragraph(Text("Put R=2^a, D=2^d, k=d+a(p-1), E=geom(a,p), and N=2^k-1. The native charge theorem applies because a>=2, p>=1 and d>=a imply E<=2^(k-1)-1. The finite geometric sum splits exactly as E=R^(p-1-j)*A_j+geom(a,p-1-j), with A_j=geom(a,j+1). This is an identity for unbounded parameters, with no coprimality or least-period assumption.")),
            Paragraph(Text("The dyadic action x maps to 2x. Grouping a successive actions gives x maps to R*x. The long positive labels i<d-1 have charge zero. At negative label d-1+a*j the quotient is the odd integer A_j and twice the charge is A_j+1. At positive packet label d+a*j+u, with u<a-1 and j+1<p, the quotient is 2^(u+1)*A_j and the charge is 2^u*A_j. These are the original physical exponents, rather than labels selected by equality of values.")),
            Paragraph(Text("Writing P_j=A_j+D*R^j*geom(a,p-1-j), the positive packet values are exactly 2^u*P_j in the old source and 2^u*(2P_j-A_j) in the doubled-seed source. Both packet bases are strictly positive. The shared native digit identity gives g_i=2f_i-c_i, while the new physical last label has value E. The packet drift identities are 2*(f_(d-1+a*j)+(2^(a-1)-1)*P_j)=R^j*(R-D) and (2^(a-1)-1)*P_j+f_(d-1+a*(j+1))=R^j*(R-D). Their signs control every consecutive peak and valley. All quotient bounds use the explicit nonnegative geometric remainder; finite controls are not used as proof.")),
            Paragraph(Text("These internal arithmetic lemmas are consumed by the literal physical joint-order construction. The mathematical derivation follows the approved symbolic proof for this component and reuses PeriodicShorteningArithmetic.digit_data, charge_sum and geom lemmas. No literature novelty or general aperiodic completion is asserted."))), []));
}
