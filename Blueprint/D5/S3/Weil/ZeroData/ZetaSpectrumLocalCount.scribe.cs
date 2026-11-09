using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ZetaSpectrumLocalCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZeroData/ZetaSpectrumLocalCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical local counts for the positive zeta spectrum.",
        H("Unit windows of positive zeta zeros"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeta-spectrum-local-count"),
                DeclarationHandle.Create(Prefix + "zetaSpectrum_localCount"),
                H("The positive-spectrum local count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the Riemann hypothesis, the positive zeta spectrum satisfies the local "
                    + "counting estimate with no further assumption. The local_count field of the "
                    + "unconditional canonical Riemann-von Mangoldt theorem bounds the canonical "
                    + "window (t,t+1]. The identity for zetaSpectrum_N and additivity of canonical "
                    + "window counts identify its multiplicity with N(t+1)-N(t), including exactly "
                    + "the upper endpoint and excluding exactly the lower endpoint."))),
                DescribeRole.Theorem))));
}
