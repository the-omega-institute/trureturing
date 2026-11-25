using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformSpecialSpectralDomainsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpecialSpectralDomains";
    private const string Title = "The generic point of each special chart";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformspecialspectraldomains-determinantgenericpoint-injective"),
                DeclarationHandle.Create(Module + ".determinantGenericPoint_injective"),
                H("The generic point of each special chart"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Injectivity of the determinant-chart map permits nonvanishing to be tested in the generic radical algebra."))),
                DescribeRole.Theorem))));
}
