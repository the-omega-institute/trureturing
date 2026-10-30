using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class ScalarOverlapObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Self-consistent scalar overlap constraints fail to enforce the incidence benchmark.",
        H("A common-array realization obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scalar-overlap-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Probability/ScalarOverlapObstruction.complete_theorem"),
                H("The rational family and its native incidence bridge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite joint law of (K,U), the integer K lies between one and s, " +
                        "its mean is q and the mean of U is s. Each m(k) is the expectation " +
                        "of min(k,K) under this same law. The scalar constraints require U " +
                        "to be at least both K and K squared divided by m(K).")),
                    Paragraph(Text(
                        "For every integer a at least sixteen, put s=a+2, q=a and " +
                        "M=5a squared minus a plus one. Cardinalities 1, a and a+1 have " +
                        "masses 1/(5a), 4/5 and (a-1)/(5a). Their U values are " +
                        "(41a to the fourth plus 13a squared plus one)/(aM), 5a cubed/M " +
                        "and (a+1) squared/a. All masses are positive, both means are exact " +
                        "and m on the support is 1, M/(5a) and a.")),
                    Paragraph(Text(
                        "The objective V is the expectation of K times U squared. Its " +
                        "difference from a(a+1) squared is minus P(a)/(5a squared M squared). " +
                        "The coefficients of P in descending powers eight through zero are " +
                        "110, -1697, 58, -949, 56, -211, 24, -18 and 2. Its sign is " +
                        "strictly positive throughout the unbounded range a at least sixteen.")),
                    Paragraph(Text(
                        "A native array assigns a nonnegative normalized mass to every " +
                        "nonempty subset of the s hubs, allowing zero type masses. Its " +
                        "positive marginals determine U as the reciprocal marginal sum on " +
                        "each type. The same array determines the cardinality mean, the " +
                        "quadratic incidence weights and 2J. Equality of joint induced laws " +
                        "means equality of expectations for every real test of both K and U.")),
                    Paragraph(Text(
                        "Finite incidence summation gives both exact means. The overlap " +
                        "budget is at most the truncated cardinality mean of that same " +
                        "array. Finset.sq_sum_div_le_sum_sq_div supplies the within-type " +
                        "reciprocal bound. A second Cauchy-Schwarz inequality gives V at " +
                        "most 2J. Every native array therefore supplies a relaxed law.")),
                    Paragraph(Text(
                        "When s=a+2, every type of size a+1 omits a hub with positive " +
                        "marginal. Its marginal sum is strictly smaller than q=a, so its " +
                        "U is strictly greater than (a+1) squared/a. Positive mass at the " +
                        "displayed joint value is impossible. Disconnected support and " +
                        "arbitrarily small positive marginals are included.")),
                    Paragraph(Text(
                        "The adjacent-cardinality benchmark is F(q)=(a+1) squared times " +
                        "((3a squared+3a+1)q-a(a+1)(2a+1))/(2q squared). At q=a its " +
                        "double is a(a+1) squared. The scalar obstruction does not refute " +
                        "the actual-array or graph comparison.")),
                    Paragraph(Text(
                        "At a=16 the masses are 1/80, 4/5 and 3/16, U is 538061/4048, " +
                        "4096/253 and 289/16, and m is 1, 253/16 and 16. The objective is " +
                        "37817565947/8193152, the double benchmark is 4624 and the gap is " +
                        "-67568901/8193152."))))));
}
