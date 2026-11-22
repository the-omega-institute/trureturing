using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformTracePowerSimpleRootsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTracePowerSimpleRoots";
    private const string Title = "Simple roots of the trace-one power polynomial";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsuniformtracepowersimpleroots-result"),
            DeclarationHandle.Create(Module + ".rootMultiplicity_normalizedTracePower"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For n ≥ 2 each complex root of the trace-one power polynomial has multiplicity one. This supplies the nonzero determinant derivative used in the proportional boundary charts."))),
            DescribeRole.Theorem))));
}
