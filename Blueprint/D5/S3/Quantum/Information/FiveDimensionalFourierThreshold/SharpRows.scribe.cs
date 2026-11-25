using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class SharpRowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/SharpRows.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The row residual is controlled by a weighted amplitude energy. Centered spectral estimates give the posterior cap on six rows, and the scalar energy budget suffices for the sharp score bound.",
        H("Row residuals and the critical-mask energy budget"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-sharp-measuredamplitude"),
                DeclarationHandle.Create(Prefix + "measuredAmplitude"), H("The actual measurement amplitudes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An amplitude is an inner product with a computational or Fourier basis vector. Squared moduli give the two Born tables."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-sharp-rowresidual"),
                DeclarationHandle.Create(Prefix + "rowResidual"), H("The squared row residual"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For row masses p and q ordered by the selected mask, the residual is ((1−c)p−(1+c)q)²/(p+q). Here c is the critical singular value. A common zero row contributes zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-sharp-criticalenergydata"),
                DeclarationHandle.Create(Prefix + "CriticalEnergyData"), H("Weighted energy data"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The data contain the even and odd deficits, even leakage, aligned overlaps, the posterior caps outside the four light rows, and the weighted energy estimate with its two odd sectors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-sharp-centered-overlap-bounds"),
                DeclarationHandle.Create(Prefix + "centered_overlap_bounds"), H("Centered reference overlap bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For unit vectors at centered deficit below 0.075, total leakage is below 0.173. Each reference overlap is at least 0.909, and their sum is at least 1.9."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-centered-heavy-posterior"),
                DeclarationHandle.Create(Prefix + "centered_heavy_posterior"), H("The posterior cap on six heavy rows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For aligned unit vectors at centered deficit below 0.075, a row outside the light set has minority mass at most 0.3 times its total mass. The light set consists of indices 1 and 4 in both bases. The estimate uses the row leverage and reference amplitude margin."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-score-le-of-energy-data"),
                DeclarationHandle.Create(Prefix + "score_le_of_energy_data"), H("The score bound from the energy data"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two unit vectors and a compatible sign mask, CriticalEnergyData supplies the residual estimate needed to bound the score by the exact cutoff (14 + 2√5)/5. The proof uses the common-zero convention and charges the even overlap mismatch to the positive odd sector and the even deficit."))), DescribeRole.Theorem)),
        []));
}
