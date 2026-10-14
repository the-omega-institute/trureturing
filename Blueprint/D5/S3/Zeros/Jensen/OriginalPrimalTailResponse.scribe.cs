using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class OriginalPrimalTailResponseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete original theta-tail response.",
        H("The complete original theta-tail response"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-primal-tail-response"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Jensen/OriginalPrimalTailResponse.original_primal_tail_response"),
                H("A relative rational response and the original source-node debits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The original polynomial is B_(n,t)(x)=sum from j=0 to n of " +
                        "(-1)^j*(n)_j*t^j*x^(2*j)/(n^j*(2*j)!). Put alpha=t/(2*n), " +
                        "A=pi*(N+1)^2, Q_N=sum over m>N of q_m, and H_N=sum over " +
                        "1<=m<=N of q_m, with q_m and the full cubic origin flux kappa_N " +
                        "as in the original primal tail. The denominator is exactly " +
                        "Z=Re xi(1/2), which is positive unconditionally. The density has " +
                        "total mass one. For every n>=1, the full-density expectation " +
                        "J_n(t) is the real source polynomial at -t, its complex coercion " +
                        "is the canonical complex Jensen evaluation, and " +
                        "J_n(t)=(2/Z)*(integral B*H_N+integral B*Q_N). The complex " +
                        "polynomial uses shift zero and scale 1/n, including n=1.")),
                    Paragraph(Text(
                        "There is an absolute K>0, chosen before a,N,n,t. For every a>0, " +
                        "one C_W(a)>0 works for all N,n>=1 and t>0 with alpha<=a. " +
                        "All full-density and half-line integrals in the formula are " +
                        "integrable. If I=integral over x>0 of B*Q_N, the original " +
                        "bound is |t*I/kappa_N-1|<=C_W(a)*(N+1)^4/t for every N>=1. " +
                        "At t>=2*C_W(a)*(N+1)^4, every real or canonical complex source " +
                        "node has (2/Z)*integral B*H_N<=-kappa_N/(Z*t).")),
                    Paragraph(Text(
                        "For A>=max(12,a), the sharper relative response is " +
                        "|(t+4*A^2)*I/kappa_N-1|<=K/A. If also A>=2*K, then " +
                        "I>=kappa_N/(2*(t+4*A^2))>0. Every actual real or complex source " +
                        "node consequently has (2/Z)*integral B*H_N " +
                        "<=-kappa_N/(Z*(t+4*A^2))<0. No positive lower bound on alpha, " +
                        "rescaled t, or degree is required. Common and multiple nodes " +
                        "are retained; no derivative or cofactor denominator occurs.")),
                    Paragraph(Text(
                        "The small residual keeps 4*A^2*Q_N-Q_N'' grouped. With " +
                        "s=pi*m^2 and z=s*exp(2*x), its leading polynomial difference " +
                        "is bounded by 16*z^2*(z^2-A^2)+151*z^3. The leading term " +
                        "splits into s^4*exp(4*x)*(exp(4*x)-1) and " +
                        "(s^2-A^2)*s^2*exp(4*x). The first has the essential x factor " +
                        "after exp(4*x)-1<=4*x*exp(4*x); the second vanishes exactly " +
                        "at the first omitted mode. Weighted mode integration gives " +
                        "230*s^2*exp(-s)+16*(s^2-A^2)*s*exp(-s). All later modes " +
                        "are summed with their scale gaps. If S_k=shiftedBudget(k)-1, " +
                        "L=230*(1+S_2)+(8/pi)*S_3 and K=(2/11)*L. The entire " +
                        "weighted residual is at most L*A^2*exp(-A), whereas the " +
                        "literal full flux is at least (11/2)*A^3*exp(-A).")),
                    Paragraph(Text(
                        "The literal finite coefficient recurrence proves " +
                        "B''-alpha*x*B'+t*B=0, B(0)=1 and B'(0)=0. The derivative " +
                        "of exp(-alpha*x^2)*(B^2+B'^2/t) is " +
                        "-2*alpha*x*exp(-alpha*x^2)*B^2, giving " +
                        "|B|<=exp(alpha*x^2/2). The full Green bracket " +
                        "B*F'-B'*F+alpha*x*B*F has derivative B*A_alpha(F)+t*B*F. " +
                        "Polynomial weighted jet bounds pay each infinity product " +
                        "for both F=Q_N and F=A_alpha(Q_N); both origin terms remain. " +
                        "The second Green application and the original full-tail " +
                        "budget give the all-cutoff P bound with the same C_W(a). " +
                        "The first Green application and the grouped residual give " +
                        "the relative response. Exact raw moments and the complete " +
                        "series split supply the source correspondence and node debits. " +
                        "These conclusions assert no node existence, cofactor sign, " +
                        "full source coupling, or Riemann hypothesis."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Zeros/Jensen/OriginalPrimalTailProjection")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Zeros/Jensen/SourceJensenIntegralExtension")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Analytic/Fourier/XiThetaTransform"))
        ]));
}
