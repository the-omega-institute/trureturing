using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FiveDimensionalFourierThreshold;

internal sealed class FourierGeometryCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierGeometryCore.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-basis mask projection has an explicit spectrum on the centered critical representatives. Affine changes of residue labels preserve the measured amplitudes up to a shared unit phase.",
        H("Centered Fourier mask spectrum and covariance"),
        Blocks(
            Describe.Lean(DescribeId.Create("five-sharp-geometry-amplitude"),
                DeclarationHandle.Create(Prefix + "geometryAmplitude"), H("Complex two-basis amplitudes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The computational amplitude is the corresponding input coordinate. The Fourier amplitude is the normalized inverse QFT coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-covariance"),
                DeclarationHandle.Create(Prefix + "geometryAmplitude_affine"), H("Affine amplitude covariance"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A unit residue dilation followed by a computational shift and modulation induces the reciprocal dilation in the Fourier labels. The transported amplitude differs by a unimodular scalar depending only on its row, so the same phase transports both input states."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-mask"),
                DeclarationHandle.Create(Prefix + "geometryMask"), H("The two-basis mask operator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mask operator sums the rank-one orthogonal projections onto the selected basis columns."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-mask-inner"),
                DeclarationHandle.Create(Prefix + "inner_geometryMask"), H("Mask quadratic and mixed forms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Its inner product with two states is the sum of the conjugate of the first measured amplitude times the second measured amplitude on the selected rows."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-mask-affine"),
                DeclarationHandle.Create(Prefix + "geometryMask_affine"), H("Mask isometry covariance"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The state isometry interchanges the original mask projection sum and the projection sum onto the permuted rows."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-centered-ray"),
                DeclarationHandle.Create(Prefix + "centeredRay"), H("Normalized principal rays"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each even or odd principal channel, the two extremal combinations are the sum and difference of positively phased unit principal vectors, divided by the square root of twice one plus or minus their overlap."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-projection-difference"),
                DeclarationHandle.Create(Prefix + "centeredProjectionDifference_ray"), H("Complementary principal overlap"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The difference of the two selected projections maps each principal ray onto the opposite-sign ray multiplied by the nonnegative complementary overlap."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-eigenbasis"),
                DeclarationHandle.Create(Prefix + "centeredEigenbasis_apply"), H("Exact centered mask spectra"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Set c = √((7 + √5)/10), h = √((5 − √5)/10), σ = √((5 + √5)/10) and b = √((3 − √5)/10). The mask selecting the pair {2,3} in both bases has an orthonormal eigenbasis with eigenvalues 0, 1 ± b and 1 ± σ. Complementing the computational pair gives the rank-five mask with eigenvalues 1, 1 ± c and 1 ± h. The even principal channel corresponds to b in the first mask and c in the second."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-affine-eigenbasis"),
                DeclarationHandle.Create(Prefix + "affine_centeredEigenbasis_apply"), H("Spectrum transported to affine masks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Applying the affine state isometry to each centered eigenvector gives an eigenvector with the same eigenvalue for the corresponding transported mask."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-complement-eigenbasis"),
                DeclarationHandle.Create(Prefix + "affine_centeredEigenbasis_compl_apply"), H("Complement mask spectrum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full two-basis mask is twice the identity. The complement mask retains the transported eigenvectors and replaces each eigenvalue λ by 2 − λ."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-sharp-geometry-mass-spectral"),
                DeclarationHandle.Create(Prefix + "centeredMask_mass_spectral"), H("The Born mass in spectral coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum of the selected computational and Fourier Born probabilities is the sum of the squared eigenbasis coordinates weighted by the corresponding eigenvalues."))), DescribeRole.Theorem)),
        []));
}
