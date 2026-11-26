using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFourSiteResidualSystemDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSystem";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eliminating the projective partner in the four-site marginal",
        H("Eliminating the projective partner in the four-site marginal"),
        Blocks(
            Claim("residualEquations_degree", "The degrees of the three eliminated equations",
                "The left product constraint has degree three, the left conic has degree two, and the right conic pulled back by the adjugate has degree four."),
            Claim("triplets_proportional", "Compatible invertible triplets are proportional under the rank bound",
                "Both factors satisfy the triplet sextic. The shared forward and reverse products put every competitor in the same power pencil. The adjugate partner and the singlet product supply three residual equations. The degree-eight quotient bound then identifies the projective left factor."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-four-site-residualsystem-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
