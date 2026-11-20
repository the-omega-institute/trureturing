using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class PetzCothStripModeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compensated lower Poisson mode is integrable and has an explicit hyperbolic cotangent integral.",
        H("The compensated lower Poisson mode"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petz-compensated-lower-mode"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzCothStripMode.integral_lowerMode"),
                H("Whole-line lower boundary integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real frequency omega, the lower Poisson weight pi/(cosh(2 pi s) - 1) multiplied by the cosine deficit 1 - cos(omega s) is Lebesgue integrable. Its integral is zero at frequency zero. At nonzero frequency, put x = omega/2. The integral is x coth(x) - 1.")),
                    Paragraph(Text("Yang's width-one-half strip Poisson formula supplies the weight. On the positive ray it expands into exponential terms with rate and prefactor 2 pi n for n starting at one. The compensated Laplace integral of each term is omega squared divided by the sum of omega squared and the squared rate. Summability justifies termwise integration. Reflection doubles the positive-ray integral, which the frozen coth partial fraction evaluates at x = abs(omega)/2."))),
                DescribeRole.Theorem))));
}
