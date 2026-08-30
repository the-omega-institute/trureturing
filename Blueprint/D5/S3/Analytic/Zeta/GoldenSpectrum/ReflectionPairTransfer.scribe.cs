using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta.GoldenSpectrum;

internal sealed class ReflectionPairTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Zeta/GoldenSpectrum/ReflectionPairTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal reflection pairs separate determinant balance from isometry.",
        H("Reflection-Pair Transfer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reciprocal-pair-determinant-one"),
                DeclarationHandle.Create(Prefix + "reflection_pair_determinant_one"),
                H("Reciprocal pairs have determinant one"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two diagonal channels carry reciprocal nonzero charges.")),
                    Paragraph(Text(
                        "Their determinant is one, expressing pairwise volume balance without "
                            + "asserting metric preservation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-pair-isometry-iff-neutral"),
                DeclarationHandle.Create(Prefix + "reflection_pair_isometry_iff"),
                H("Positive pair isometry is pointwise neutrality"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Testing the first coordinate basis forces the positive radial charge to "
                            + "have square one.")),
                    Paragraph(Text(
                        "Positivity selects charge one. The converse follows by direct "
                            + "substitution.")),
                    Paragraph(Text(
                        "The explicit charge-two witness records that determinant balance alone "
                            + "does not imply isometry."))),
                DescribeRole.Theorem))));
}
