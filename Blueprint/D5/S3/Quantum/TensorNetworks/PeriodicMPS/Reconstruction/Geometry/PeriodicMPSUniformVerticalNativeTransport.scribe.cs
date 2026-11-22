using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformVerticalNativeTransportDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalNativeTransport";
    private const string Title = "Rank transport from native to paired section minors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformverticalnativetransport"),
                DeclarationHandle.Create(Module + ".sectionRankImplication_of_nativeCriticalMatrix"),
                H("Native rank deficiency implies section rank deficiency"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An injective scalar extension and factorizations through the evaluated native matrix give the section rank implication from vanishing of the native maximal minors on each admissible pairing."))),
                DescribeRole.Theorem))));
}
