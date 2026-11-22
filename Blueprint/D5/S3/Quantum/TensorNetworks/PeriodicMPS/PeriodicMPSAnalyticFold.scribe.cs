using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSAnalyticFoldDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticFold";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic separation for an analytic fold",
        H("Generic separation for an analytic fold"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsanalyticfold-exists-generic-singleton-fibers"),
                DeclarationHandle.Create(Module + ".exists_generic_singleton_fibers"),
                H("Singleton fibers after adding a residual readout"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Consider a real-analytic observation with horizontal coordinates and one vertical variable. If the first vertical derivative of a scalar readout vanishes and its second vertical derivative is nonzero, it has a strict fold after shrinking the chart. Suppose there are pairs arbitrarily near the base point that share the horizontal and fold values and differ in a further analytic readout. The analytic identity principle confines branch coincidence to a nowhere dense set. On a smaller open source neighborhood, an open dense set of targets has singleton fibers within that neighborhood for the augmented observation."))),
                DescribeRole.Theorem))));
}
