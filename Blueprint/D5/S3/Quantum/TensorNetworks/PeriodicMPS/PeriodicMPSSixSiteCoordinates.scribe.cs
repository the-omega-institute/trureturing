using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCoordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-site necklace coordinates",
        H("Six-site necklace coordinates"),
        Blocks(
            Claim("trace_word_necklaces", "Cubic trace coordinates",
                "Fourteen cyclic word amplitudes are cubic polynomials in the squared trace covector and determinant pencil."),
            Claim("chart_eq_zero_iff", "Base conics",
                "On the chart with first trace one, three trace words detect the vanishing of the full amplitude and force the determinant pencil to be proportional to the squared trace covector."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpssixsitecoordinates-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
