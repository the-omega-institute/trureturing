using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteGraphContinuationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphContinuation";
    private const string Title = "Continuation from the hard-core fiber to actual seven-site states";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("sevensitegraphcontinuation-result"),
            DeclarationHandle.Create(Module + ".exists_open_dense_actual_state_recovery"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Assume a compact subset of the seven-site trace graph has Hausdorff dimension at most six, contains the chart boundary and leaves an injective real derivative of the observation at each ordinary chart point outside it. The compact state source then has a relatively open dense set consisting of actual projectors, each identified by its adjacent two-site marginal against every projector in the compact closure.")),
                Paragraph(Text("Over a neighborhood of the hard-core state, the full projector determines its graph lift. The nearby unique marginal fibers supply a nonempty open set of singleton graph fibers. This set meets the dense region left after discarding the observation values of the exceptional set. Continuation applies in the eight-real-dimensional chart with nine real readings."))),
            DescribeRole.Theorem))));
}
