using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class FiniteHermitianLocalizerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/SpectralTopology/FiniteHermitianLocalizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite operator and position matrix determine a Hermitian block localizer with an exact zero-scale square.",
        H("Finite Hermitian Spectral Localizer"),
        Blocks(
            Entry("centered-operator", "centeredOperator", "Centred operator", "The spectral point is subtracted from a finite complex operator.", DescribeRole.Definition),
            Entry("centered-position", "centeredPosition", "Centred position matrix", "A real spatial centre is subtracted from a finite Hermitian position matrix.", DescribeRole.Definition),
            Entry("localizer", "finiteHermitianLocalizer", "Finite Hermitian block localizer", "The position defect and spectral defect form a doubled Hermitian block matrix.", DescribeRole.Definition),
            Entry("hermitian", "finiteHermitianLocalizer_isHermitian", "Hermitianity", "Hermitian position data make the complete finite block localizer Hermitian.", DescribeRole.Theorem),
            Entry("zero-scale", "finiteHermitianLocalizer_zero_scale", "Zero-scale form", "At zero localization scale only the spectral defect and its adjoint remain.", DescribeRole.Theorem),
            Entry("square", "finiteHermitianLocalizer_zero_scale_sq", "Zero-scale square", "Squaring the zero-scale localizer produces the direct sum of the two singular Gram matrices.", DescribeRole.Theorem),
            Entry("zero", "finiteHermitianLocalizer_zero_scale_eq_zero_iff", "Zero localizer criterion", "The zero-scale localizer vanishes exactly when the centred operator vanishes.", DescribeRole.Theorem),
            Entry("negative-index", "localizerNegativeIndex", "Finite negative inertia", "The Hermitian localizer carries a finite negative-eigenvalue count.", DescribeRole.Definition)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaLinear/PosIndex"))
        ]));

    private static DocumentBlock.Describe Entry(string id, string declaration, string heading, string paragraph, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(paragraph))), role);
}
