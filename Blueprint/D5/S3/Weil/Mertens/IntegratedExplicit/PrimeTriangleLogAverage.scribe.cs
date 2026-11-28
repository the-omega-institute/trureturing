using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeTriangleLogAverageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower bound on unit logarithmic windows of the ordinary-prime triangle characterizes RH.",
        H("Logarithmic averages of the ordinary-prime triangle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-triangle-log-window-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleLogAverage.rh_iff_eventual_prime_triangle_log_average"),
                H("RH and a unit-window average of the centered prime triangle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordinary-prime triangle is centered by its linear main term and "
                    + "the square-root term from prime squares. RH implies an eventual lower "
                    + "bound of minus one twelfth for the integral of the normalized expression "
                    + "over every unit interval in logarithmic coordinates. The reverse "
                    + "implication uses the dyadic recurrence for the smoothed Mangoldt ramp "
                    + "and telescopes its unit increments to an affine bound for the signed "
                    + "ordinary-prime primitive anchored at 5040."))),
                DescribeRole.Theorem))));
}
