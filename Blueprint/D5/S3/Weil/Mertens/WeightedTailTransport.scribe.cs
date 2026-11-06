using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class WeightedTailTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact weighted-tail Fubini transport",
        H("Exact weighted-tail Fubini transport"),
        Blocks(
            Paragraph(Text("For any real L1 kernel K on (t,infinity), t>=2, set r(t)=(1+log(t))/log(t)^2, density(t)=(log(t)+2)/(t*log(t)^3), Q_K(t)=integral K and I_K(t)=integral K*r. Nonnegative density has total mass r(t). Absolute Fubini on the triangle z<u proves integrability of both weighted kernels and r(t)*Q_K(t)-I_K(t)=integral density(z)*Q_K(z). No differentiability of K or extra weighted-integrability premise is assumed.")),
            Paragraph(Text("Under t=exp(y), the exponential Jacobian cancels exactly the single 1/t in density. The canonical CountableResolvent owns R(y)=(y+1)/y^2 and W(y)=(y+2)/y^3; they are reused here. There is no additional exp(-y) on Q_K(exp(y)). All assertions quantify over analytic families and are not finite computations. The proof uses Mathlib absolute Fubini, improper FTC and exponential substitution; no literature-priority claim is made.")),
            Describe.Lean(
                DescribeId.Create("weightedtailtransport-transport"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/WeightedTailTransport.transport"),
                H("Exact weighted-tail Fubini transport"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The generic L1 triangular exchange and both derived integrability claims."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weightedtailtransport-transport-exp"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/WeightedTailTransport.transport_exp"),
                H("Exact weighted-tail Fubini transport"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At this identical y, R(y)*(Q_K(exp(y))-I_K(exp(y))/r(exp(y))) equals integral_(y,infinity) W(v)*Q_K(exp(v)). This identity is consumed by OriginalLocalA; transport_log is not separately exported."))),
                DescribeRole.Theorem))));
}
