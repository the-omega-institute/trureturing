using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class FourierGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact principal-ray measurements on the centered masks give individual row estimates. Every critical pair of differences is reached through an affine state isometry.",
        H("Centered Fourier row masses and critical mask orbit"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-sharp-geometry-fourier-pair-mass"),
                DeclarationHandle.Create(Prefix + "centeredRay_fourier_pair_mass"), H("Fourier pair row masses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a principal ray of overlap r and sign s = ±1, each of its two selected Fourier pair rows carries the probability (1 + s r)/4, in either centered mask rank."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-standard-pair-mass"),
                DeclarationHandle.Create(Prefix + "centeredRankFive_ray_standard_pair_mass"), H("Omitted computational pair row masses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the rank-five mask the computational pair is omitted. Each of its two rows carries probability (1 − s r)/4 for the principal ray with overlap r and sign s."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-odd-zero"),
                DeclarationHandle.Create(Prefix + "centeredRay_odd_zero"), H("Odd principal rays at the central row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In either rank, both odd principal rays have zero amplitude in computational row zero and Fourier row zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-even-zero-mass"),
                DeclarationHandle.Create(Prefix + "centeredRankFive_ray_zero_mass"), H("Rank-five even principal masses at row zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let Z = (7 − √5)/11 and c = √((7 + √5)/10). On the even principal ray with sign s, the zero rows carry masses (1 + s c)Z/2 in the computational basis and (1 − s c)Z/2 in the Fourier basis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-middle-zero-mass"),
                DeclarationHandle.Create(Prefix + "centeredRankFive_middle_zero_mass"), H("The middle eigenvector's central mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the rank-five mask the eigenvector of eigenvalue one carries central row mass 1 − Z in each basis, as the other four eigenvectors account for the remaining contribution."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-middle-pair-mass"),
                DeclarationHandle.Create(Prefix + "centeredRankFive_middle_pair_mass"), H("The middle eigenvector vanishes on the centered pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The middle eigenvector of the rank-five mask has zero probability on both pair rows in each of the computational and Fourier bases."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-weighted-amplitude"),
                DeclarationHandle.Create(Prefix + "geometryAmplitude_sq_le_weighted"), H("Weighted estimate for a single measured row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite sum of vectors with complex coefficients and positive weights g, the squared amplitude on a fixed row is at most the sum of vector row masses divided by g, multiplied by the sum of squared coefficient moduli weighted by g. This retains complex vector amplitudes and allows the weights to be the exact spectral gaps."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-mask-orbit"),
                DeclarationHandle.Create(Prefix + "criticalMasks_affine"), H("Affine orbit of the critical masks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the product of the two ordered pair differences in Z/5Z is ±1, a single dilation, standard shift and Fourier modulation transports the centered pairs {2,3} to those pairs. The same transformation transports the centered four-row mask and the centered five-row mask, along with the complementary five-row orientation."))), DescribeRole.Theorem)),
        []));
}
