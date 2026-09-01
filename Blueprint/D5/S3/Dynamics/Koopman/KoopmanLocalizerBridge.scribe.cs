using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Dynamics.Koopman;

internal sealed class KoopmanLocalizerBridgeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite permutation Koopman pullback has an explicit unit matrix and therefore opens a zero-centered point-gap localizer.",
        H("Finite Koopman-Localizer Bridge"),
        Blocks(
            Def("matrix", "finiteKoopmanMatrix", "Finite Koopman matrix",
                "Each row selects the observable coordinate reached by the finite permutation update."),
            Def("unit", "finiteKoopmanMatrixUnit", "Koopman matrix unit",
                "The matrix of the inverse permutation is packaged as the explicit two-sided inverse."),
            Thm("action", "finiteKoopmanMatrix_mulVec", "Matrix action is Koopman pullback",
                "Multiplying an observable column by the finite Koopman matrix evaluates it after the state update."),
            Thm("right", "finiteKoopmanMatrix_mul_inverse", "Inverse matrix cancels on the right",
                "The update matrix multiplied by the inverse-permutation matrix is the identity."),
            Thm("left", "finiteKoopmanMatrix_inverse_mul", "Inverse matrix cancels on the left",
                "The inverse-permutation matrix multiplied by the update matrix is the identity."),
            Thm("gap", "finiteKoopmanMatrix_has_pointGap_zero", "Zero is a Koopman point gap",
                "Every finite permutation Koopman matrix is a unit and therefore excludes zero from its point spectrum."),
            Thm("localizer", "finiteKoopmanLocalizer_isUnit", "Koopman point gap opens the localizer",
                "The zero-scale Hermitian localizer built from a finite permutation Koopman matrix is invertible."),
            Thm("inverse", "finiteKoopmanLocalizer_explicit_inverse", "Explicit Koopman localizer inverse",
                "The point-gap construction gives both inverse equations for the Koopman localizer.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Dynamics/Koopman/FiniteKoopmanUnitary")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/SpectralTopology/FinitePointGapLocalizer")),
        ]));

    private static DocumentBlock.Describe Def(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
