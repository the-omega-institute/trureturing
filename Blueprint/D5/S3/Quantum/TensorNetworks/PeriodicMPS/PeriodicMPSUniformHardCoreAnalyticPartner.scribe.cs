using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreAnalyticPartnerDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticPartner";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic partner paths for normalized hard-core observations",
        H("Analytic partner paths for normalized hard-core observations"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcoreanalyticpartner-exists-second-curve"),
                DeclarationHandle.Create(Module + ".exists_second_curve"),
                H("Exact matching from a leading-system certificate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The hard-core chart parameters are weighted by the path parameter in their imaginary parts and by its square in their real corrections. Cross-multiplying by the trace masses converts equality of seven normalized regular readouts and the real 00,01 coherence into polynomial equations. A certificate at the leading system gives an even analytic parameter solution and exact matching of those eight physical readouts near zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcoreanalyticpartner-chart-taylor-four"),
                DeclarationHandle.Create(Module + ".chart_taylor_four"),
                H("Parity of the actual chart coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The even analytic parameter curve gives linear and cubic terms in each imaginary coordinate and a constant, quadratic and quartic term in each real coordinate. The corresponding remainders are bounded by the fifth and sixth powers of the real path parameter."))),
                DescribeRole.Theorem))));
}
