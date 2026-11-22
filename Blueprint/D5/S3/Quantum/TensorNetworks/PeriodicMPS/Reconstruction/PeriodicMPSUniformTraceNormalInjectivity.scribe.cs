using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformTraceNormalInjectivityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTraceNormalInjectivity";
    private const string Title = "Injectivity of the proportional normal amplitude";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsuniformtracenormalinjectivity-result"),
            DeclarationHandle.Create(Module + ".proportional_normal_injective"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("At every proportional trace-one base point indexed by a root of the length-n power polynomial, n ≥ 2, the first variation of the full amplitude is injective on the three determinant and mixed-trace normal coordinates."))),
            DescribeRole.Theorem))));
}
