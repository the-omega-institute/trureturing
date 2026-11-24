using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class HarmonicThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/HarmonicThreshold.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The score is four minus four times the harmonic deficit when each of the two laws has mass two.",
        H("Harmonic overlap from finite threshold masks"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-fourier-score"),
                DeclarationHandle.Create(Prefix + "score"), H("Triangular discrimination on a finite table"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each row contributes its squared mass difference divided by its total mass. A common zero row contributes zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-fourier-spectralmaskgaps"),
                DeclarationHandle.Create(Prefix + "SpectralMaskGaps"), H("The two mass gaps"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A mask larger than half the table has mass at least A. A mask of exactly half the table has mass at least E."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-fourier-overlap-lower-bound-of-mask-gaps"),
                DeclarationHandle.Create(Prefix + "overlap_lower_bound_of_mask_gaps"), H("The harmonic deficit bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The row score minimizing the quadratic loss is q/(p+q). Integrating over threshold masks gives a density bounded below by the minimum of 2At, 2E, and 2A(1-t). Integrating this minimum gives 2E − 2E²/A."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-fourier-score-upper-bound-of-mask-gaps"),
                DeclarationHandle.Create(Prefix + "score_upper_bound_of_mask_gaps"), H("The score bound for two normalized laws"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The score is four minus four times the harmonic deficit when each of the two laws has mass two."))), DescribeRole.Theorem)),
        []));
}
