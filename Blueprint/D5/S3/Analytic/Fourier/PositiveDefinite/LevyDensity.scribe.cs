using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier.PositiveDefinite;

internal sealed class LevyDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Fourier/PositiveDefinite/LevyDensity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive definite functions and their integral representations.",
        H("LevyDensity"), Blocks(
            Describe.Lean(DescribeId.Create("pd-levydensity-finite-density"),
                DeclarationHandle.Create(Prefix + "finite_density"), H("Compound Poisson positivity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an integrable nonnegative real density against a positive measure and a nonnegative rate, the exponential of minus the rate times its integrated cosine deficit is positive definite. A nonnegative cosine mixture, the pointwise exponential series and a positive constant factor establish every finite Gram inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-levydensity-of-truncations"),
                DeclarationHandle.Create(Prefix + "of_truncations"), H("Exhaustion by integrable densities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume nonnegative density almost everywhere, measurable truncations which eventually contain almost every point, integrability of the density on every truncation, and integrability of each full cosine deficit. Dominated convergence takes the compound Poisson kernels to the full exponential."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pd-levydensity-positivedefinite"),
                DeclarationHandle.Create(Prefix + "positiveDefinite"), H("Positive half line density criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a density D nonnegative on the positive half line, assume D(s)/s is integrable on each interval from 1/(n+1) to n+1 and every cosine deficit times D(s)/s is integrable on the positive half line. For each strictly positive real r, exp of minus 2r times the deficit integral is positive definite. This local integrability formulation specifies exactly the conditions used in truncation and dominated convergence."))), DescribeRole.Theorem))));
}
