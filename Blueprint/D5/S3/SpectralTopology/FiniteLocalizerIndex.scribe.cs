using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class FiniteLocalizerIndexDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/SpectralTopology/FiniteLocalizerIndex.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Hermitian localizers carry proof-independent positive and negative inertia counts with explicit dimension bounds.",
        H("Finite Localizer Inertia Index"),
        Blocks(
            Entry("positive", "localizerPositiveIndex", "Positive localizer inertia", "The positive eigenvalues of the finite Hermitian localizer are counted with multiplicity.", DescribeRole.Definition),
            Entry("signature", "finiteLocalizerSignature", "Finite localizer signature", "The integer signature is the positive inertia minus the negative inertia.", DescribeRole.Definition),
            Entry("profile", "FiniteLocalizerInertia", "Finite inertia profile", "Positive count, negative count, and integer signature are packaged with their defining relation.", DescribeRole.Definition),
            Entry("positive-proof", "localizerPositiveIndex_proof_irrel", "Positive inertia is proof independent", "Changing the proof that the position matrix is Hermitian does not change the count.", DescribeRole.Theorem),
            Entry("negative-proof", "localizerNegativeIndex_proof_irrel", "Negative inertia is proof independent", "Changing the Hermitianity proof does not change negative inertia.", DescribeRole.Theorem),
            Entry("positive-bound", "localizerPositiveIndex_le_dimension", "Positive dimension bound", "Positive inertia is bounded by the doubled finite dimension.", DescribeRole.Theorem),
            Entry("negative-bound", "localizerNegativeIndex_le_dimension", "Negative dimension bound", "Negative inertia is bounded by the doubled finite dimension.", DescribeRole.Theorem),
            Entry("point-gap", "pointGap_has_invertible_localizer_inertia", "Point-gap inertia locus", "A point-gap certificate places the zero-scale localizer in the invertible Hermitian locus with bounded inertia.", DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/SpectralTopology/FinitePointGapLocalizer"))
        ]));

    private static DocumentBlock.Describe Entry(string id, string declaration, string heading, string paragraph, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(paragraph))), role);
}
