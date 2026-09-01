using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class FinitePointGapLocalizerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/SpectralTopology/FinitePointGapLocalizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite point-gap certificate gives an explicit two-sided inverse for the zero-scale Hermitian localizer.",
        H("Finite Point-Gap Localizer"),
        Blocks(
            Entry("certificate", "PointGapCertificate", "Point-gap certificate", "A centred finite operator is supplied with an explicit two-sided matrix inverse.", DescribeRole.Definition),
            Entry("has-gap", "HasPointGap", "Finite point gap", "A point gap exists when its explicit inverse certificate is inhabited.", DescribeRole.Definition),
            Entry("unit-equivalence", "hasPointGap_iff_isUnit", "Point gap equals matrix invertibility", "The explicit point-gap certificate is equivalent to the centred operator being a unit.", DescribeRole.Theorem),
            Entry("inverse", "zeroScaleLocalizerInverse", "Explicit localizer inverse", "The operator inverse and its conjugate transpose occupy the opposite off-diagonal blocks.", DescribeRole.Definition),
            Entry("right", "zeroScaleLocalizer_mul_inverse", "Right inverse law", "The zero-scale localizer times the explicit block inverse is the identity.", DescribeRole.Theorem),
            Entry("left", "inverse_mul_zeroScaleLocalizer", "Left inverse law", "The explicit block inverse times the zero-scale localizer is the identity.", DescribeRole.Theorem),
            Entry("unit", "zeroScaleLocalizer_isUnit_of_hasPointGap", "Point gap opens the Hermitian localizer", "Every finite non-Hermitian point gap becomes invertibility of the doubled Hermitian localizer.", DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/SpectralTopology/FiniteHermitianLocalizer"))
        ]));

    private static DocumentBlock.Describe Entry(string id, string declaration, string heading, string paragraph, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(paragraph))), role);
}
