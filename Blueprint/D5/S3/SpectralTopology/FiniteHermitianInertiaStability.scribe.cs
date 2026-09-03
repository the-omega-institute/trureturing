using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class FiniteHermitianInertiaStabilityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/SpectralTopology/FiniteHermitianInertiaStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-sided Weyl certificates preserve finite Hermitian inertia "
            + "across an invertible perturbation.",
        H("Finite Hermitian Inertia Stability"),
        Blocks(
            Definition("radius-bound", "HasEigenvalueRadiusBound",
                "Eigenvalue radius bound",
                "Every eigenvalue of a Hermitian perturbation lies in a prescribed closed radius."),
            Definition("two-sided-radius", "HasTwoSidedEigenvalueRadiusBound",
                "Two-sided perturbation radius",
                "The perturbation and its negative receive separate radius "
                    + "certificates, independent of eigenvalue enumeration."),
            Definition("positive-threshold-gap", "HasPositiveThresholdGap",
                "Positive threshold gap",
                "Raising the counting threshold from zero removes no positive eigenvalues."),
            Definition("two-sided-threshold-gap", "HasTwoSidedThresholdGap",
                "Two-sided threshold gap",
                "The matrix and its negative have no counted eigenvalue in "
                    + "the threshold strip next to zero."),
            Theorem("positive-monotone", "posIndex_le_add_of_threshold_gap",
                "Positive-index lower stability",
                "A threshold gap and a reverse perturbation bound prevent "
                    + "the positive index from decreasing."),
            Theorem("negative-monotone", "negIndex_le_add_of_threshold_gap",
                "Negative-index lower stability",
                "A threshold gap for the negated base and a perturbation "
                    + "bound prevent the negative index from decreasing."),
            Theorem("inertia-stable", "inertia_eq_of_two_sided_weyl_certificate",
                "Two-sided inertia stability",
                "Two-sided Weyl certificates and invertible endpoints force "
                    + "equality of both inertia counts."),
            Theorem("signature-stable", "hermitianSignature_add_eq_of_two_sided_weyl_certificate",
                "Hermitian-signature stability",
                "The same certificate preserves the repository's existing "
                    + "Hermitian signature coordinate.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/ZetaLinear/Weyl")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/SpectralTopology/PointGapExactInertia")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/SpectralTopology/FiniteSpectralLocalizer")),
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
