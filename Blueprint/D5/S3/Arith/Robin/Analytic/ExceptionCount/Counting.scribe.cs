using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.ExceptionCount;

internal sealed class CountingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Small fixed relaxations of the distinct-prime threshold preserve the sharp exponential counting rate, and dyadic intervals cover an arbitrary exception set.",
        H("Distinct-prime tails and dyadic covers"),
        Blocks(
            Describe.Lean(DescribeId.Create("relaxed-tail"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/Counting.relaxed_tail_upper"),
                H("Stability under threshold relaxation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive epsilon there is a positive eta for which tailCount(-eta,x) is eventually at most exp((C0+epsilon)*scale(x)). At the existing saddle s, the rate changes from C0 to C0+s*eta. Choosing eta=epsilon/(2*s) leaves half the exponent budget for the existing Rankin upper bound. This is a counting statement about distinct prime factors; it does not identify Robin exceptions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dyadic-cover"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/Counting.dyadic_cover_count"),
                H("Exact finite cover by prime-factor tails"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary decidable predicate E, a natural cutoff N and an initial dyadic index J, suppose each E-member of (2^(j-1),2^j] above the initial segment has more distinct prime factors than threshold(lambda,2^j). Then the number of E-members in [1,N] is at most 2^J plus the sum of tailCount(lambda,2^j) over J<j<=clog(2,N). Each positive integer is assigned its natural upper logarithm. The finite-union bound preserves all small exceptions in the initial segment."))), DescribeRole.Theorem))));
}
