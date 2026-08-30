using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta.GoldenSpectrum;

internal sealed class GoldenCriticalCoordinateDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Zeta/GoldenSpectrum/GoldenCriticalCoordinate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden exponential coordinates turn the critical line into a unit circle.",
        H("Golden Critical Coordinate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-critical-line-unit-circle"),
                DeclarationHandle.Create(
                    Prefix + "norm_golden_critical_coordinate_eq_one_iff"),
                H("Critical line equals unit golden radius"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The coordinate exponentiates the centered spectral variable using the "
                            + "positive length two times log phi.")),
                    Paragraph(Text(
                        "Its norm is the real exponential of the centered real part. Injectivity "
                            + "of the real exponential makes unit norm equivalent to real part "
                            + "one half.")),
                    Paragraph(Text(
                        "This is an exact coordinate theorem. It supplies no independent zero "
                            + "location or positivity statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-reflection-reciprocal-conjugation"),
                DeclarationHandle.Create(
                    Prefix + "golden_critical_coordinate_reflection"),
                H("Completed reflection becomes reciprocal conjugation"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Reflection across the critical line negates the conjugate centered "
                            + "coordinate.")),
                    Paragraph(Text(
                        "Complex exponentiation sends this operation to reciprocal conjugation, "
                            + "while radial charges become reciprocal positive real numbers."))),
                DescribeRole.Theorem))));
}
