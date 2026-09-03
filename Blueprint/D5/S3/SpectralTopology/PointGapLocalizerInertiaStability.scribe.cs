using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class PointGapLocalizerInertiaStabilityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative Weyl certificates keep point-gap localizer inertia "
            + "constant along an admissible radial path.",
        H("Point-Gap Localizer Inertia Stability"),
        Blocks(
            Definition("position-perturbation", "localizerPositionPerturbation",
                "Localizer position perturbation",
                "The real position scale multiplies the Hermitian "
                    + "block-diagonal position direction."),
            Definition("localizer-certificate", "HasLocalizerWeylCertificate",
                "Localizer Weyl certificate",
                "A one-scale certificate combines the zero-scale threshold "
                    + "gap with a perturbation radius bound."),
            Definition("uniform-certificate", "HasUniformRadialLocalizerWeylCertificate",
                "Uniform radial Weyl certificate",
                "The threshold gap is fixed at zero scale while the perturbation "
                    + "radius is certified along the unit segment."),
            Definition("radial-signature", "radialLocalizerSignature",
                "Radial localizer signature",
                "The finite localizer signature is evaluated at the contracted "
                    + "scale along the radial path."),
            Theorem(
                "perturbation-hermitian",
                "localizer_position_perturbation_isHermitian",
                "Hermitian localizer perturbation",
                "A real scale and Hermitian position observable give a "
                    + "Hermitian position perturbation."),
            Theorem(
                "endpoint-inertia-transport",
                "finite_localizer_inertia_eq_zero_scale_of_weyl_certificate",
                "Endpoint inertia transport",
                "An admissible scale and localizer Weyl certificate identify "
                    + "finite-scale inertia with zero-scale inertia."),
            Theorem(
                "endpoint-exact-inertia",
                "finite_localizer_exact_inertia_of_weyl_certificate",
                "Exact finite-scale inertia",
                "A point gap upgrades the transported endpoint inertia to exact "
                    + "half-dimensional positive and negative counts."),
            Theorem(
                "endpoint-signature",
                "finite_localizer_signature_eq_zero_of_weyl_certificate",
                "Finite-scale signature vanishing",
                "The finite localizer signature vanishes under the same "
                    + "quantitative Weyl certificate."),
            Theorem(
                "radial-exact-inertia",
                "radial_localizer_exact_inertia_of_uniform_weyl_certificate",
                "Uniform radial inertia",
                "A uniform radial certificate gives exact inertia at every "
                    + "point of the admissible unit segment."),
            Theorem(
                "radial-signature-zero",
                "radial_localizer_signature_eq_zero_of_uniform_weyl_certificate",
                "Uniform radial signature vanishing",
                "A uniform radial certificate makes the finite localizer "
                    + "signature zero throughout the path.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/SpectralTopology/PointGapRadialGapPath")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/SpectralTopology/FiniteHermitianInertiaStability")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/SpectralTopology/PointGapExactInertia")),
        ]));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Theorem);
}
