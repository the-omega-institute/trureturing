using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ExponentialSum;

internal sealed class DescartesRuleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generalized Descartes rule for real exponential sums, including strict sign reversals at a saturated set of zeros.",
        H("Descartes rule for exponential sums"), Blocks(
            Paragraph(Text("Let N be any natural number, let a and mu be real families indexed by Fin N, and assume that mu is strictly decreasing. Write F(t) for the sum of a(i) exp(mu(i)t), and V for List.signVariations of List.ofFn a. This variation count removes all zero coefficients before counting adjacent opposite signs. All exponents and arguments are real.")),
            Describe.Lean(DescribeId.Create("exponential-descartes-zero-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/ExponentialSum/DescartesRule.zero_bound"),
                H("Distinct zeros"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If at least one coefficient is nonzero, every finite set Z consisting of zeros of F has cardinality at most V. The bound holds for arbitrary real exponents; no integral or rational spacing assumption is imposed.")),
                    Paragraph(Text("After removing zero terms, choose a constant c strictly between the exponents at a coefficient sign reversal. Multiplication by exp(-ct) preserves zeros. Its derivative has coefficients a(i)(mu(i)-c), whose variation count is exactly V-1. Induction on V and Rolle's theorem give the bound. When V is zero, all terms have the same strict sign."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exponential-descartes-crossing-bound"),
                DeclarationHandle.Create("D5/S3/Analytic/ExponentialSum/DescartesRule.sign_crossing_bound"),
                H("Zeros without a sign reversal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same assumptions, add to the cardinality of Z the number of its points where F fails ChangesSign. The result is still at most V. Here ChangesSign F z means that some epsilon greater than zero makes F(t)F(s) strictly negative for every t between z-epsilon and z and every s between z and z+epsilon.")),
                    Paragraph(Text("The proof first establishes the stronger bound that charges each stationary zero one additional unit. The normalized derivative has a zero between consecutive prescribed zeros and at every prescribed stationary zero. These sets are disjoint. A nonzero derivative at a zero forces a uniform strict sign reversal, giving the stated conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exponential-descartes-exact-sign"),
                DeclarationHandle.Create("D5/S3/Analytic/ExponentialSum/DescartesRule.exact_sign"),
                H("Exact signs at saturation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose some coefficient a(i) is strictly positive and all coefficients at earlier indices vanish. If Z is a finite set of zeros with cardinality exactly V, then at every real t the SignType sign of F(t) equals that of the product over z in Z of t-z. The conclusion includes the value zero at the prescribed points and the empty product when V is zero.")),
                    Paragraph(Text("Saturation excludes every additional zero and every stationary prescribed zero. Normalization by the largest exponent with a nonzero coefficient tends to its positive coefficient, so F is eventually positive. Removing each simple zero with the continuous divided slope leaves a continuous function with exactly the remaining simple zeros. Induction gives the monic product's sign. This is a form of the classical generalized Descartes principle; the proof supplies an interface for real exponential sums."))),
                DescribeRole.Theorem))));
}
