using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class KarpQuadraticTruncationsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two quadratic truncations of the Karp-Zhang series have nonnegative generalized "
            + "Turan coefficients for every nonnegative real pair of shifts.",
        H("Karp-Zhang Quadratic Truncations"),
        Blocks(
            Paragraph(Text(
                "The targets are r2 and r3 of issue #5969, from Dmitrii Karp and Yi Zhang, "
                    + "Log-concavity and log-convexity of series containing multiple Pochhammer "
                    + "symbols, Fractional Calculus and Applied Analysis 27 (2024), 458-486, "
                    + "DOI 10.1007/s13540-023-00238-0. The results concern only the specified "
                    + "truncations of Conjectures 1 and 2, not either full series conjecture.")),
            Describe.Lean(
                DescribeId.Create("r2-polynomial"),
                DeclarationHandle.Create(Prefix + "r2Polynomial"),
                H("The two-term r = 3 polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The rising factorial is Mathlib's ascending Pochhammer polynomial evaluated "
                        + "at t. Only indices 1 and 2 are retained, with denominators 2! and 5!. "
                        + "The two weights can be any nonnegative real numbers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("r3-polynomial"),
                DeclarationHandle.Create(Prefix + "r3Polynomial"),
                H("The truncation at k = 2"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constant, linear and quadratic coefficients are respectively h0, h1*t "
                        + "and h2*t*(t+3)/2. The last expression is the k=2 Pochhammer quotient "
                        + "in the source series; no integer restriction is placed on t."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("r2-all-coefficients"),
                DeclarationHandle.Create(Prefix + "r2_coeff_nonneg"),
                H("Conjecture 1 for the two-term truncation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonnegative weights c1,c2, positive mu and arbitrary nonnegative real "
                        + "alpha and beta, every "
                        + "coefficient of F(mu+alpha)*F(mu+beta)-F(mu)*F(mu+alpha+beta) is "
                        + "nonnegative. The equal-index terms follow by factorwise comparison. "
                        + "The mixed (3,6) term is alpha*beta*(alpha+beta+2*mu+8) times a "
                        + "polynomial with positive coefficients in mu, alpha+beta, alpha*beta "
                        + "and (alpha-beta)^2; the identity is checked by the Lean kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("r3-real-shifts"),
                DeclarationHandle.Create(Prefix + "r3_coeff_nonneg"),
                H("Conjecture 2 for three terms and real shifts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume h0,h1,h2 are nonnegative, h1^2 >= h0*h2, and mu is positive. "
                        + "For arbitrary nonnegative real alpha and beta, the degree-two "
                        + "Turan coefficient is alpha*beta*(h1^2-h0*h2). The degree-three "
                        + "coefficient is h1*h2*alpha*beta*(alpha+beta+2*mu+6)/2. The "
                        + "degree-four coefficient is h2^2*alpha*beta/4 times a polynomial "
                        + "with positive coefficients. All other coefficients vanish. The "
                        + "shifts are arbitrary nonnegative reals, extending the integer-shift "
                        + "scope of the paper's Theorem 3 for this truncation."))),
                DescribeRole.Theorem))));
}
