using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class CompoundPoissonEdgeworthCutoffDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthCutoff.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/statlean2026fourier");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Irrational jump ratios give annular damping and decay of the full moving-cutoff Fourier error.",
        H("The moving-cutoff estimate for irrational Poisson jumps"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("moving-cutoff-poisson-error"),
                DeclarationHandle.Create(Prefix + "symmetric_cutoff_vanishes"),
                H("The full moving-cutoff Fourier error vanishes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Assume p and q are positive, b is nonzero, and a divided by b is irrational. For every fixed positive C, w times the characteristic-function error integral over the symmetric interval from minus Cw to Cw tends to zero. The comparison uses variance V and the raw third jump moment.")),
                    Paragraph(Text("Irrationality prevents both cosine terms from attaining one at a nonzero frequency. Compactness therefore gives a positive damping gap on each fixed annulus. The low-frequency Gaussian estimate, this annular gap, and an integrable Gaussian correction tail control the whole interval."))),
                DescribeRole.Theorem))));
}
