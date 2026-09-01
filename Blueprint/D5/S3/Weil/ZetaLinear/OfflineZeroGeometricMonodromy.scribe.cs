using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class OfflineZeroGeometricMonodromyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaLinear/OfflineZeroGeometricMonodromy."
            + "offline_zero_geometric_definition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden-period sampling turns an offline-zero character into reciprocal "
            + "real monodromy branches, hyperbolic exactly off the unitary boundary.",
        H("Offline-Zero Golden-Period Monodromy"),
        Blocks(Describe.Lean(
            DescribeId.Create("offline-zero-geometric-monodromy"),
            DeclarationHandle.Create(Declaration),
            H("The golden-period monodromy realizes the offline-zero geometry"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The normalized Mellin mode is reused from OfflineZeroCharacter. "
                        + "Sampling its two reciprocal radial branches at twice the "
                        + "logarithm of the golden ratio gives a real diagonal two-by-two "
                        + "monodromy with determinant one.")),
                Paragraph(Text(
                    "Its trace discriminant is four times the square of the hyperbolic "
                        + "sine of the radial displacement. Consequently the monodromy "
                        + "is hyperbolic exactly when the character lies off the unitary "
                        + "boundary.")),
                Paragraph(Text(
                    "The definition is realized nonvacuously by the existing nonunitary "
                        + "offline-zero witness. The source's closing Solenoid language is "
                        + "not promoted to an unsupported uniqueness or maximality claim."))),
            DescribeRole.Definition))));
}
