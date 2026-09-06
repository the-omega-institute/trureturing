using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class GaussianDisplacementOverlapDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/WeylChronology/GaussianDisplacementOverlap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian endpoint closure connects actual displacement integrals to the existing Ramsey and finite-shot interfaces.",
        H("GaussianDisplacementOverlap"),
        Blocks(
            Paragraph(Text("The source is a candidate proof. Exact statements and kernel status belong to the Lean producer. No hardware experiment or metrological advantage is asserted.")),
            Describe.Lean(
                DescribeId.Create("gaussianseed"),
                DeclarationHandle.Create(Prefix + "gaussianSeed"),
                H("gaussianSeed"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real seed exp(-s q squared) represents a centered axis-aligned pure Gaussian. Normalization is handled by its actual squared-norm integral."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gaussianmass"),
                DeclarationHandle.Create(Prefix + "gaussianMass"),
                H("gaussianMass"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the Bochner integral of the seed times its complex conjugate. It is not a chosen normalization constant."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gaussianoverlap"),
                DeclarationHandle.Create(Prefix + "gaussianOverlap"),
                H("gaussianOverlap"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displacement expectation is defined as an actual integral divided by the same seed norm. Its denominator is proved nonzero on the positive-width domain."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("displacementcost"),
                DeclarationHandle.Create(Prefix + "displacementCost"),
                H("displacementCost"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cost is (s x squared + y squared divided by s)/2 in the inherited dimensionless quadrature convention."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gaussian-intensity-integrable"),
                DeclarationHandle.Create(Prefix + "gaussian_intensity_integrable"),
                H("gaussian intensity integrable"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive s the squared magnitude is integrable. This prevents interpreting an undefined integral as a physical normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-mass-value"),
                DeclarationHandle.Create(Prefix + "gaussian_mass_value"),
                H("gaussian mass value"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Mathlib Gaussian integration evaluates the squared-norm integral as the real square root of pi divided by 2s."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-mass-ne-zero"),
                DeclarationHandle.Create(Prefix + "gaussian_mass_ne_zero"),
                H("gaussian mass ne zero"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive width makes the actual normalization strictly nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-overlap-integrable"),
                DeclarationHandle.Create(Prefix + "gaussian_overlap_integrable"),
                H("gaussian overlap integrable"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displaced overlap is a convergent complex quadratic-Gaussian integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-overlap-exact"),
                DeclarationHandle.Create(Prefix + "gaussian_overlap_exact"),
                H("gaussian overlap exact"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized integral is exp(-(s x squared + y squared divided by s)/2). This is the centered specialization of equation (5) of Fluehmann and Home, PRL 125, 043602 (2020), with s=exp(2r). Mathlib integral_cexp_quadratic performs the analytic integration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("displacement-cost-nonneg"),
                DeclarationHandle.Create(Prefix + "displacement_cost_nonneg"),
                H("displacement cost nonneg"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive-width domain makes the attenuation cost nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-overlap-norm-le-one"),
                DeclarationHandle.Create(Prefix + "gaussian_overlap_norm_le_one"),
                H("gaussian overlap norm le one"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Contractivity follows from the evaluated Gaussian integral; it is no longer an assumed overlap premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-overlap-defect-le-cost"),
                DeclarationHandle.Create(Prefix + "gaussian_overlap_defect_le_cost"),
                H("gaussian overlap defect le cost"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The overlap defect is bounded by the anisotropic quadratic displacement cost. The constant is in the existing Q,P convention."))),
                DescribeRole.Theorem))));
}
