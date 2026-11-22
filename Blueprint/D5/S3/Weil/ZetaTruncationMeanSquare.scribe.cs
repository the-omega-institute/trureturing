using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class ZetaTruncationMeanSquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mean-square error for a Dirichlet truncation of zeta",
        H("Mean-square error on dyadic height intervals"),
        Blocks(Describe.Lean(
            DescribeId.Create("dyadic-truncation-mean-square"),
            DeclarationHandle.Create(
                "D5/S3/Weil/ZetaTruncationMeanSquare.dyadic_truncation_mean_square"),
            H("Uniform error to the right of the critical line"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For real a, b, u and T with 1/2 < a ≤ u ≤ b and T ≥ 2, the bound uses "
                    + "the sum of n^(−s) for 1 ≤ n ≤ ceil(T), evaluated at s = u + it. "
                    + "Integrate the squared error over T − 1 ≤ |t| ≤ 2T + 1. "
                    + "The squared error is integrable there, and its integral is bounded by "
                    + "(250 + 2(b+3)^2 π/(4a)) times T^(2−2a).")),
                Paragraph(Text(
                    "The exact Euler–Maclaurin identity separates the explicit correction "
                    + "and its Bernoulli integral. Substituting x = exp(v) in that integral "
                    + "gives an angular Fourier transform of a bounded sawtooth times exp(−uv), "
                    + "restricted to v > log(ceil(T)). Plancherel bounds the squared integral of "
                    + "the transform on the real line. On the indicated height band, the remaining "
                    + "factor |s|² costs at most a constant times T²."))),
            DescribeRole.Theorem))));
}
