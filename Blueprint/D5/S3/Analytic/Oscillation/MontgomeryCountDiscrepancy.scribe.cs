using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class MontgomeryCountDiscrepancyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unbounded count discrepancy from the Montgomery unit band",
        H("The counting obstruction from a uniform Montgomery profile"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("montgomery-unit-band-unbounded-discrepancy"),
                DeclarationHandle.Create("D5/S3/Analytic/Oscillation/MontgomeryCountDiscrepancy.unit_band_profile_forces_unbounded_count_discrepancy"),
                H("Unbounded count discrepancy from the Montgomery unit band"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any positive locally finite spectrum with positive integer multiplicities, use the inclusive count and the Lorentz-weighted Montgomery cosine sum normalized by two pi over H log H. Assume its profile for all frequencies of absolute value at most one is a central exponential peak with coefficient tending to one plus the absolute frequency, with a uniform error tending to zero.")),
                    Paragraph(Text("For every real threshold H0 and every real D there exists H at least H0 at which the absolute difference between the inclusive count and the two-term logarithmic main term exceeds D.")),
                    Paragraph(Text("Under bounded discrepancy, compare the smoothed count to the truncated reference density and bound its centered variance by the common derivative bound for the test family. The autocorrelation limit identifies that variance with the weighted Fourier energy for each fixed test. The spatial mass outside the interval tends to zero after averaging, including the square needed for the variance. Increasing the window width forces the Fourier energy past the common bound. The height limit precedes the window-width choice in this comparison."))),
                DescribeRole.Theorem))));
}
