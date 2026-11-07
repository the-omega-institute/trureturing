using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class PositiveOrdinateSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under RH, positive zeta zeros give a locally finite spectrum with faithful multiplicities.",
        H("The positive zeta ordinate spectrum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeta-spectrum"),
                DeclarationHandle.Create(Prefix + "zetaSpectrum"),
                H("Spectrum from positive nontrivial zeta zeros"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The indices are the distinct nontrivial complex zeta zeros "
                    + "with positive imaginary part. Each ordinate is the imaginary part, and "
                    + "each multiplicity is the canonical analytic zero multiplicity. RH puts "
                    + "every zero on the critical line, so equal ordinates imply equal indices. "
                    + "Canonical local finiteness gives finite upper cutoffs."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeta-spectrum-count"),
                DeclarationHandle.Create(Prefix + "zetaSpectrum_N"),
                H("Exact identification of cutoff counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real T the spectrum count is exactly the "
                    + "canonical count in the window (0,T]. The bijection sends each subtype "
                    + "index to its underlying complex zero and preserves multiplicity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zeta-spectrum-count-asymptotic"),
                DeclarationHandle.Create(Prefix + "zetaSpectrum_countAsymptotic"),
                H("Classical logarithmic spectrum count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under RH, the spectrum count divided by T log T tends "
                    + "to 1/(2 pi). The cumulative counting theorem uses the unconditional "
                    + "Riemann-von Mangoldt source; RH is used to construct an injective "
                    + "ordinate spectrum."))),
                DescribeRole.Theorem))));
}
