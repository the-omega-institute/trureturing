using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace.QuantitativeFejerBoundary;

internal sealed class BoundaryEstimateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/BoundaryEstimate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Piecewise affine Fourier weights bound the oscillatory integral of the regular part.",
        H("Quantitative boundary estimates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boundary-regular-integral-bound"),
                DeclarationHandle.Create(Prefix + "boundary_regular_integral_bound"),
                H("A uniform bound for the regular boundary integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a spectrum with logarithmic counting asymptotics and paired Laplace data of growth degree k, there is a positive A such that every admissible kernel of positive bandwidth b, M at least one and y at least one has regular boundary integral of norm at most A*(1+b)*M^(max(k,1))/y. The constant is independent of the kernel, bandwidth, cutoff and translation."))),
                DescribeRole.Theorem))));
}
