using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ReflectingHeatQuantileGramianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quantile multiplier and the finite Blaschke estimate bound the inverse diagonal on each positive reflecting mode.",
        H("Mode-uniform physical Gramian estimate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflecting-heat-quantile-gramian-upper"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.inverse_diagonal_upper_bound_of_quantiles"),
                H("Physical upper bound from the quantile multiplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real-axis envelope cancels the exterior Joukowski radius in the Chebyshev interpolation bound. The imaginary-axis error bounds the multiplier value at the Fourier node −iq_j from below. Its radial exponential width gives the centered support, which becomes the physical interval of length a/n. The normalization retains the first-cell weight b_j and the nodal derivative combines with it to give q_j b_j."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflecting-heat-quantile-gramian-lower"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.inverse_diagonal_lower_bound_at_saddle"),
                H("Finite Blaschke lower bound and angular quadrature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The logarithm of the sum of two saddle radii increases along the angular grid. The right-endpoint sum bounds its angular average from above. Removing the endpoint at π and the selected positive mode costs at most twice the terminal logarithm. The resulting bound retains the exact factor q_j b_j and the time factor sqrt(na)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflecting-heat-quantile-gramian-saddle-radius"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.existsUnique_saddle_radius"),
                H("Unique positive saddle radius"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The angular average of the reciprocal saddle radius is continuous and strictly decreasing on the positive half-line. The polynomial bounds at small and large radii bracket half the window parameter, so the intermediate value theorem gives the unique radius used by the physical estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflecting-heat-quantile-gramian-log-loss"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatQuantileGramian.physical_log_inverse_diagonal_error"),
                H("Uniform logarithmic loss at the continuum saddle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the unique positive saddle, the zero density yields continuous, strictly increasing cumulative mass and a uniform density cap. Differentiating the imaginary potential gives an integral of the weighted resolvent. Its evaluation gives the multiplier normalization and radial upper type. The angular logarithmic integral equals the logarithm of the exterior Joukowski radius by the Mahler measure of a quadratic. The real boundary evaluation of the potential remains a hypothesis. It gives the required real-axis cancellation, and the two physical estimates bound the absolute logarithmic error by 20(1+log n+|log(nT)|) for every positive mode."))),
                DescribeRole.Theorem))));
}
