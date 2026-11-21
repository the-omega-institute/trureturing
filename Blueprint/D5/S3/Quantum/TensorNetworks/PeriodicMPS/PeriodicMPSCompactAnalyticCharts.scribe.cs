using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSCompactAnalyticChartsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSCompactAnalyticCharts";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic charts on a compact fiber",
        H("Analytic charts on a compact fiber"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpscompactanalyticcharts-result"),
            DeclarationHandle.Create(Module + ".exists_fiber_graphs"),
            H("Analytic charts on a compact fiber"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "A compact fiber with injective differentials admits finitely many analytic graph charts over a common projection."))),
            DescribeRole.Theorem))));
}
