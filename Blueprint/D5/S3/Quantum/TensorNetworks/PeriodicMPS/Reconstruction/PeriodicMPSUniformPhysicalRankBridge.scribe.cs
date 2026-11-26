using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformPhysicalRankBridgeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalRankBridge";
    private const string Title = "Criticality of the actual normalized two-site observation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformphysicalrankbridge-mem-criticalcoordinates-iff-native-minors"),
                DeclarationHandle.Create(Module + ".mem_criticalCoordinates_iff_native_minors"),
                H("Criticality of the actual normalized two-site observation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the trace chart with nonzero aligned mixed trace, criticality of the normalized two-site observation is equivalent to vanishing of all ten native maximal minors."))),
                DescribeRole.Theorem))));
}
