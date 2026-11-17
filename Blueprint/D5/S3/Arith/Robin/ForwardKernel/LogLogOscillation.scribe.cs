using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class LogLogOscillationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/LogLogOscillation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The forward response has two-sided logarithmic logarithmic excursions.",
        H("Logarithmic logarithmic oscillation of the forward response"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-kernel-omega-pm-loglog"),
                DeclarationHandle.Create(Prefix + "forward_kernel_omega_pm_loglog"),
                H("Two-sided log-log excursions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume the Riemann hypothesis, the von Koch bound, and the paired xi expansion. Then some positive constant c gives arbitrarily large x with forwardResponse(x)<=-c*log(log x), and arbitrarily large x with c*log(log x)<=forwardResponse(x), while x>exp(1). The result follows by transferring the paired Laplace excursions in y and taking x=exp(y)."))),
                DescribeRole.Theorem))));
}
