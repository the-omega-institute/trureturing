using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteTraceChartDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteTraceChart";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-site trace charts at the base conics",
        H("Six-site trace charts at the base conics"),
        Blocks(
            Claim("shear_aligned", "Physical shear of the pencil",
                "A shear of the physical basis transports the trace-aligned amplitude and the determinant pencil by the same change of coordinates."),
            Claim("lift_coordinates", "Linear factorization in normal coordinates",
                "All fourteen amplitudes factor through the three normal coordinates, with a coefficient matrix that varies polynomially along the ordinary chart."),
            Claim("lift_ne_zero_of_vacuum", "Nonvanishing over each base point",
                "At a vacuum root the linear factorization maps every nonzero normal vector to a nonzero amplitude."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpssixsitetracechart-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
