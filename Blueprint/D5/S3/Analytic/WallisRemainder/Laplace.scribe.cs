using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.WallisRemainder;

internal sealed class LaplaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive Laplace representation for the logarithmic Wallis remainder.",
        H("The hyperbolic Laplace kernel"), Blocks(
            Entry("wallis-laplace-integrable", "integrableOn_laplaceKernel", "Absolute convergence",
                "For positive x, the function exp(-xt) tanh(t/4)/(2t) is integrable over positive t. The hyperbolic sine bound gives an upper bound exp(-xt)/8; positivity uses the shared tanh interval theorem."),
            Entry("wallis-laplace-representation", "r_eq_laplace", "The integral representation",
                "For every positive x, minus log B(x) equals the integral of exp(-xt) tanh(t/4)/(2t) over positive t. Gamma recurrence gives a half-step equation, and log convexity gives a nonnegative remainder tending to zero. The exponential case of Frullani's integral evaluates the corresponding difference integral. The shared hyperbolic bias ratio identity gives the kernel half-step equation. The proposed integral obeys the same half-step equation and tends to zero; their difference is periodic with period one, so the difference vanishes."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/WallisRemainder/Laplace." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
