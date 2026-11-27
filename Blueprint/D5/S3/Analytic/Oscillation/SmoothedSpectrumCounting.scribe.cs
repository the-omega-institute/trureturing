using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class SmoothedSpectrumCountingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Variance cap from bounded counting discrepancy",
        H("Smoothed counts of a spectrum with bounded discrepancy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("smoothed-spectrum-counting-cap"),
                DeclarationHandle.Create("D5/S3/Analytic/Oscillation/SmoothedSpectrumCounting.normalized_variance_upper"),
                H("Variance cap from bounded counting discrepancy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let N(H) be the inclusive finite count of a positive locally finite spectrum, counting every integer multiplicity. Suppose N(T) differs from the two-term logarithmic main term by at most E for T at least two pi. Smooth the atoms through H against a real Schwartz function at scale log H divided by two pi and center by the integral of that function.")),
                    Paragraph(Text("If the spatial average of the centered square on the interval from zero to H converges to V, then V is bounded above by the square of the product of the cumulative discrepancy bound and the integral of the absolute derivative of the test function. The cumulative bound is the maximum of N at two pi and E plus the absolute value of the main term at two pi.")),
                    Paragraph(Text("The truncated reference density is the logarithm of the ordinate divided by two pi inside the logarithm and has the prefactor one over two pi. It is supported between two pi and H. Its cumulative integral equals a difference of two main term values. Integration against the derivative of the test function transfers the cumulative discrepancy bound to the smoothed count. After scaling the spatial interval to unit length, the normalized reference tends to the constant integral of the test function in mean square."))),
                DescribeRole.Theorem))));
}
