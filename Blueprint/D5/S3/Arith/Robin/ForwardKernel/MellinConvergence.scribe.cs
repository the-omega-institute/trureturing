using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MellinConvergenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MellinConvergence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The continuous kernel mass.",
        H("The continuous kernel mass"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("error-power-bound"),
                DeclarationHandle.Create(Prefix + "error_power_bound"),
                H("Extending an eventual power bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let alpha>=0. If |psi(t)-t|<=C*t^alpha for every t>=t0, there is D>=0 such that |psi(t)-t|<=D*t^alpha for every t>=2. On the compact initial interval use monotonicity and nonnegativity of psi; outside it use the given estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forwardresponse-power-bound"),
                DeclarationHandle.Create(Prefix + "forwardResponse_power_bound"),
                H("Power growth of the complete response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let E(t)=psi(t)-t, H(x)=x^(4/5), and T(x)=sqrt(x)/H(x)^2 times the integral from 0 to H(x) of (E(x+u)-E(x))*w(x+u)/w(x). If alpha>=0, C>=0 and |E(t)|<=C*t^alpha for t>=2, then |T(x)|<=2*C*2^alpha*x^(alpha-3/10) for x>=3. The window lies in [x,2*x], and its positive decreasing weight ratio is at most one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forwardmellin-integrable"),
                DeclarationHandle.Create(Prefix + "forwardMellin_integrable"),
                H("Absolute convergence of the Mellin integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An eventual error bound |psi(t)-t|<=C*t^alpha with alpha>=0 implies absolute integrability of T(x)*x^(-s-1) on (x0,infinity) whenever x0>=3 and Re(s)>alpha-3/10. The response is measurable by a joint indicator representation of its variable interval integral. The majorant is a constant times x^(alpha-3/10-Re(s)-1)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-mellin-majorant-integrable"),
                DeclarationHandle.Create(Prefix + "kernel_mellin_majorant_integrable"),
                H("The continuous kernel mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For x0>=4 and Re(s)>1/2, the function |x^(-s-1)|*moment(x,0) is integrable on [x0,infinity). The zero-exponent moment is exactly the original kernel row volume and is bounded in absolute value by (5/2)*sqrt(x). This estimate is independent of any Chebyshev error hypothesis."))),
                DescribeRole.Theorem))));
}
