using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class FiniteHermitianLocalizerDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/SpectralTopology/FiniteHermitianLocalizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite block localizer is Hermitian and its zero-position-scale square splits into the two singular Gram blocks.",
        H("Finite Hermitian Spectral Localizer"),
        Blocks(
            Def("position", "positionBlock", "Localized position block",
                "The centered Hermitian position matrix is scaled by the real localization parameter."),
            Def("point-gap", "pointGapBlock", "Point-gap block",
                "The spectral operator is shifted by the selected complex reference point."),
            Def("localizer", "finiteHermitianLocalizer", "Finite Hermitian localizer",
                "The position and point-gap blocks form a doubled Hermitian block matrix."),
            Thm("position-hermitian", "positionBlock_isHermitian", "Position block is Hermitian",
                "Hermiticity of the position matrix is preserved by real centering and scaling."),
            Thm("localizer-hermitian", "finiteHermitianLocalizer_isHermitian", "The localizer is Hermitian",
                "Conjugate off-diagonal blocks and opposite Hermitian diagonal blocks make the finite localizer Hermitian."),
            Thm("zero-scale", "finiteHermitianLocalizer_zero_scale", "Zero position scale leaves the point gap",
                "At zero localization scale both spatial diagonal blocks vanish."),
            Thm("square", "finiteHermitianLocalizer_zero_scale_sq", "Zero-scale square gives singular Gram blocks",
                "Squaring the off-diagonal localizer produces the left and right point-gap Gram matrices on the diagonal."),
            Thm("zero", "finiteHermitianLocalizer_zero_scale_eq_zero_iff", "Zero localizer detects a zero point-gap block",
                "At zero spatial scale the block localizer vanishes exactly when the shifted operator vanishes.")),
        []));

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
