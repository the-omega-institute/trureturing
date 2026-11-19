using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFourSiteResidueLiftDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidueLift";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact coefficient certificate at a physical four-site tensor",
        H("An exact coefficient certificate at a physical four-site tensor"),
        Blocks(
            Claim("quotient_finrank_le_of_residualMinor", "The selected 44 by 44 coefficient minor",
                "Selected monomial multiples of the cubic, conic and quartic lie in the degree-eight kernel. Their coefficient minor gives the quotient dimension bound in every field where it is nonzero."),
            Claim("physical_certificate_nonzero", "A Gaussian-integer witness",
                "The two mod-five tensor pairs come from one Gaussian-integer tensor and its conjugate. The Lean kernel checks a right inverse of the specialized minor and the remaining nonzero factors. The nonzero product transfers to the complex tensor through the Gaussian-integer embedding."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-four-site-residuelift-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
