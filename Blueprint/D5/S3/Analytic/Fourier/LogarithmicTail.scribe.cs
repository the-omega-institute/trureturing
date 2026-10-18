using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class LogarithmicTailDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Fourier/LogarithmicTail.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual shifted-logarithmic Fourier tail has an exact improper integral and a uniform positive-cutoff budget.",
        H("The logarithmic Fourier tail"),
        Blocks(
            Paragraph(Text(
                "For a real cutoff R>0 integrate (1+log(1+t))/t^2 on the full half-line t>R. "
                + "The shift inside the logarithm is retained. This is the scalar high-frequency "
                + "integral in the same-window logarithmic Fourier approximation, independently "
                + "of a test function, numerical trial, or arithmetic form.")),
            Describe.Lean(
                DescribeId.Create("positive-cutoff-integrability"),
                DeclarationHandle.Create(Owner + "integrableOn_logarithmic_tail"),
                H("Every positive-cutoff tail is integrable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The nonnegative actual integrand is integrable on (R,infinity) for every R>0. "
                    + "An explicit primitive is -(1+log(1+t))/t-(log(1+t)-log(t)). "
                    + "Its derivative and limit zero at infinity are proved before the improper "
                    + "fundamental theorem is applied. No integrability or endpoint value is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-logarithmic-tail"),
                DeclarationHandle.Create(Owner + "integral_logarithmic_tail"),
                H("The exact tail includes its endpoint logarithm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integral equals (1+log(1+R))/R+log(1+1/R). "
                    + "The logarithmic difference in the primitive is converted to log(1+1/R) "
                    + "using the positive ratio (1+R)/R. Dropping this correction would give "
                    + "an incorrect exact identity. The unshifted log(t) tail already in "
                    + "QuotientIntegralBudget is a distinct integrand; that arithmetic module "
                    + "is not imported or re-proved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("explicit-logarithmic-tail-budget"),
                DeclarationHandle.Create(Owner + "integral_logarithmic_tail_le"),
                H("One explicit budget covers every positive cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same integral is at most (2+log(1+R))/R. The elementary bound "
                    + "log(1+1/R)<=1/R pays the endpoint correction. This holds for all R>0, "
                    + "including the R>=1 range used in a Fourier split. It does not supply "
                    + "the Fourier integration-by-parts estimate, a form-domain identification, "
                    + "an actual signed Weil trial, or a Riemann-hypothesis conclusion."))),
                DescribeRole.Theorem))));
}
