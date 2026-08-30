using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeObserver.GoldenScale;

internal sealed class GoldenLogScaleCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeObserver/GoldenScale/GoldenLogScaleCharacter.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive multiplication becomes addition in golden-cycle units.",
        H("Golden Logarithmic Scale Character"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-log-scale-multiplicative-additive"),
                DeclarationHandle.Create(Prefix + "golden_log_scale_mul"),
                H("Golden scale sends multiplication to addition"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The readout divides the ordinary logarithm by the positive cycle length "
                            + "two times log phi.")),
                    Paragraph(Text(
                        "The logarithm product law then makes every positive multiplicative step "
                            + "an additive observer displacement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-square-is-one-period"),
                DeclarationHandle.Create(Prefix + "golden_log_scale_golden_ratio_sq"),
                H("Phi squared is one full golden period"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The golden ratio itself occupies one half of the orientation-preserving "
                            + "cycle, so its square advances the coordinate by one.")),
                    Paragraph(Text(
                        "This owner remains on the real logarithmic cover. Circle quotient and "
                            + "density claims require separate formalization."))),
                DescribeRole.Theorem))));
}
