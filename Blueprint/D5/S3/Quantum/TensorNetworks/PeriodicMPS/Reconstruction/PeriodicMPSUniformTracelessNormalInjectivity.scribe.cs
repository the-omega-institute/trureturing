using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformTracelessNormalInjectivityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTracelessNormalInjectivity";
    private const string Title = "Injectivity of the traceless normal amplitude";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsuniformtracelessnormalinjectivity-result"),
            DeclarationHandle.Create(Module + ".traceless_normal_injective"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("At an odd period, a traceless base point with nonzero quadratic-invariant vector has an injective first-variation map on its two trace coordinates."))),
            DescribeRole.Theorem))));
}
