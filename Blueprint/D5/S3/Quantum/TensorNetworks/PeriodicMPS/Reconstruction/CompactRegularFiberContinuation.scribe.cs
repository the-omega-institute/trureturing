using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class CompactRegularFiberContinuationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/CompactRegularFiberContinuation";
    private const string Title = "Generic singleton fibers on a compact source";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("compactregularfibercontinuation-result"),
            DeclarationHandle.Create(Module + ".compact_generic_recovery_of_dimH_bad"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("A Lipschitz observation on a compact metric source has an open dense singleton-fiber locus under the stated chart and seed hypotheses. The connected dense ordinary locus is covered by charts with Lipschitz inverses. Away from the compact exceptional set, the chart observation is a real-analytic immersion into a space of dimension one higher than the chart.")),
                Paragraph(Text("The exceptional set has Hausdorff dimension at most the chart dimension minus two. The argument removes every fiber meeting that set and proves that the remaining locus is open, dense and path connected. One singleton in the remaining locus supplies the seed for analytic continuation. Each fiber in the conclusion is taken over the full compact source."))),
            DescribeRole.Theorem))));
}
