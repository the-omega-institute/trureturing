using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class QuantitativeFejerBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/QuantitativeFejerBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-sided logarithmic envelope forces absolute Laplace convergence at every positive real parameter.",
        H("Laplace convergence from a logarithmic envelope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("laplace-converges-of-log-envelope"),
                DeclarationHandle.Create(Prefix + "laplace_converges_of_log_envelope"),
                H("Absolute convergence on the positive real ray"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a locally finite positive spectrum have positive integral multiplicities "
                    + "and counting function asymptotic to T log(T)/(2 pi). Suppose a measurable, "
                    + "locally bounded real function has an absolutely convergent Laplace transform "
                    + "for real parts greater than one half, agreeing between one half and one "
                    + "with minus one half of the paired pole sum plus a holomorphic remainder. "
                    + "Assume that either the function or its negative is bounded above on the "
                    + "nonnegative real axis by kappa log(exp(1)+u)+C, for nonnegative kappa and C. "
                    + "Then the absolute Laplace integral converges at every positive real parameter. "
                    + "An affine majorant of the logarithmic envelope gives a nonnegative difference. "
                    + "The paired inverse-square tail estimate continues its transform along the "
                    + "positive real axis. Landau's singularity theorem excludes a positive "
                    + "convergence boundary; subtracting the majorant recovers absolute convergence "
                    + "of the original function."))),
                DescribeRole.Theorem))));
}
