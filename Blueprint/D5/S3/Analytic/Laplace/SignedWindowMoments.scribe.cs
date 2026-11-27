using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class SignedWindowMomentsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Laplace/SignedWindowMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-sided window controls all complex Laplace moments at one common order",
        H("Signed moments on long upper windows"),
        Blocks(
            Paragraph(Text("Let g be a measurable real function with absolute value at most "
                + "M exp(2u) for nonnegative u. Fix a nonnegative exponent theta, a real constant "
                + "C, and a width b greater than one. Suppose g(u) is at most C exp(theta u) "
                + "on the interval from U to bU. The transform integrates g(u) exp(-zu) over "
                + "the nonnegative axis.")),
            Describe.Lean(DescribeId.Create("growth-gives-convergence"),
                DeclarationHandle.Create(Module + "growth_convergence"),
                H("The global growth bound supplies absolute convergence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real sigma greater than two, the weighted "
                    + "integral of g(u) exp(-sigma u) is absolutely convergent. The product "
                    + "of the growth envelope and the damping factor is an integrable "
                    + "exponential with rate sigma minus two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("single-window-moment-estimate"),
                DeclarationHandle.Create(Module + "moment_bound_on_window"),
                H("The interior gamma mass and the two exterior tails"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose a shape h strictly between one and b, and a "
                    + "real sigma greater than theta. Require the two gamma "
                    + "tail rates to be nonnegative and sigma times (1-h/b) to exceed two. "
                    + "This last condition also implies sigma greater than two. "
                    + "For the order k equal to floor(sigma h U), the norm of the derivative "
                    + "of order k at any z with real part sigma, plus the real signed moment "
                    + "at sigma, divided by k factorial, is at most K times (sigma-theta) "
                    + "to the power minus k. Here K is twice the sum of absolute(C) divided "
                    + "by (sigma-theta) and M times (1/sigma+b/(h sigma)).")),
                    Paragraph(Text("The norm of the complex moment plus the real signed "
                        + "moment is bounded by twice the positive-part moment. On the "
                        + "window, its density is bounded by the exponential upper envelope, "
                        + "whose complete gamma integral is explicit. Outside the window, "
                        + "the absolute growth envelope and the adjustable gamma estimate "
                        + "control both tails at the same order."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fixed-center-for-all-upper-windows"),
                DeclarationHandle.Create(Module + "long_window_moment_bound"),
                H("A fixed center works for every sufficiently distant window"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every fixed width b greater than one there are "
                    + "a real sigma greater than both two and theta and a nonnegative K "
                    + "with the following property. For every U at least one satisfying "
                    + "the stated window upper bound, set k to floor(sigma (1+b) U/2). "
                    + "Then k is at least U, and the preceding estimate holds at every "
                    + "complex center with real part sigma. The constants do not depend "
                    + "on U or on the imaginary part of the center. No exponential loss "
                    + "in U is needed for a pointwise window upper bound."))),
                DescribeRole.Theorem))));
}
