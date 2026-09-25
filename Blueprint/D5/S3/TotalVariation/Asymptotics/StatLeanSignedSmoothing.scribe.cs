using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class StatLeanSignedSmoothingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/Asymptotics/StatLeanSignedSmoothing.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/statlean2026fourier");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ramp approximation bounds probability distribution functions against signed densities through their Fourier difference.",
        H("Fourier comparison with a signed density"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-fourier-cdf-bound"),
                DeclarationHandle.Create(Prefix + "abs_measure_Iic_sub_densityCDF_le_charFun"),
                H("A Fourier bound for a signed comparison density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Compare the distribution function of a probability measure with the integral of an integrable real function. The comparison function may have either sign. A bound on its absolute integral over intervals controls the ramp approximation error; a weighted characteristic-function difference controls the smoothed error."))),
                DescribeRole.Theorem))));
}
