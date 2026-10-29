using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class NonnegativeContinuationDocument : IScribeDocumentDefinition
{
    // Proposed nonbinding construction: identify the full-ball Taylor coefficients
    // with t^n/n! times the original weighted moments, then use positivity and
    // Tonelli to obtain finite exponential integral at the new real parameter.
    // The finite integral is derived, not assumed.
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Holomorphic extension of a nonnegative Laplace germ forces convergence across its original margin.",
        H("Nonnegative Laplace Continuation"),
        Blocks(Describe.Lean(
            DescribeId.Create("nonnegative-laplace-local-extension"),
            DeclarationHandle.Create("D5/S3/Analytic/Laplace/NonnegativeContinuation.integrable_exp_of_laplace_extension"),
            H("Convergence throughout the real radius of a holomorphic extension"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let mu be any measure and X a real function which is nonnegative almost everywhere. Suppose -a lies in the interior of the exponential integrability set. Let H be complex differentiable on the open ball with real center a and radius R, and agree in a complex neighborhood of a with the original Laplace transform z ↦ complexMGF X mu (-z). For every 0<t<R the function exp((t-a)X) is integrable, and H(a-t) is its real integral embedded in the complex numbers. No upper bound on t from the old convergence margin is imposed.")),
                Paragraph(Text("Reflecting the variable reduces to the moment-generating convention. Germ equality identifies all derivatives at the center with the weighted moments supplied by Mathlib. The Taylor theorem on the entire extension ball gives convergence of the series with coefficients t^n/n! integral X^n exp(-aX). Positivity turns that convergence into finiteness of the integral of the exponential series by Tonelli. Interchanging the convergent integral series identifies the value of the same extension H.")),
                Paragraph(Text("This is a generic local analytic supplier. It makes no claim that the complete notRH, Robin, or 5040 supplier is formalized. The global abscissa argument, the original psi-clock construction, its error costs and the ODE boundary terms remain separate obligations. The argument is classical; no literature originality is claimed."))),
            DescribeRole.Theorem))));
}
