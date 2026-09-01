using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class FinitePointGapLocalizerDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/SpectralTopology/FinitePointGapLocalizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite point-gap unit gives an explicit inverse for the zero-scale Hermitian localizer.",
        H("Finite Point-Gap Localizer"),
        Blocks(
            Def("point-gap", "HasFinitePointGap", "Finite point gap",
                "The shifted finite operator is required to be a unit in its matrix ring."),
            Def("off-diagonal", "offDiagonalLocalizer", "Off-diagonal point-gap localizer",
                "A matrix block and its conjugate transpose form a Hermitian doubled localizer."),
            Def("inverse", "offDiagonalLocalizerInverse", "Explicit localizer inverse",
                "The two off-diagonal blocks are formed from the inverse point-gap unit and its conjugate transpose."),
            Thm("right-inverse", "offDiagonalLocalizer_mul_inverse", "Explicit right inverse",
                "The off-diagonal localizer multiplied by its proposed inverse is the identity."),
            Thm("left-inverse", "offDiagonalLocalizer_inverse_mul", "Explicit left inverse",
                "The proposed inverse multiplied by the off-diagonal localizer is the identity."),
            Thm("point-gap-unit", "zero_scale_localizer_isUnit_of_pointGap", "Point gap opens the localizer gap",
                "Every finite matrix point gap makes the zero-position-scale Hermitian localizer invertible."),
            Thm("formula", "zero_scale_localizer_explicit_inverse", "Zero-scale inverse formula",
                "The inverse localizer is exactly the off-diagonal matrix built from the inverse shifted operator."),
            Thm("identity", "identity_hasFinitePointGap_zero", "Identity has a zero-centered point gap",
                "The identity finite operator provides an inhabited point-gap witness.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/SpectralTopology/FiniteHermitianLocalizer")),
        ]));

    private static DocumentBlock.Describe Def(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
