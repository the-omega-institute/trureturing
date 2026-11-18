using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.ExceptionCount;

internal sealed class CountingTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A local exclusion by slightly relaxed distinct-prime thresholds gives a sharp global exponential upper bound.",
        H("Transfer from local exclusion to global counting"),
        Blocks(
            Describe.Lean(DescribeId.Create("global-transfer"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ExceptionCount/CountingTransfer.count_from_local_exclusion"),
                H("The sharp global exponent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let E be any decidable predicate on natural integers. Suppose that for every eta>0, all sufficiently large dyadic intervals (t/2,t] have each E-member above threshold(-eta,t) in distinct prime factors. Then, for every epsilon>0, the count of E-members up to x is eventually bounded by exp((C0+epsilon)*scale(x)). The existing saddle gives a tail bound with exponent C0+epsilon/4. A fixed initial segment and a logarithmic number of intervals introduce only a prefactor whose logarithm is negligible compared with scale(x); scale(2*x)/scale(x) tends to one. This theorem transfers a proved local exclusion. It does not supply that exclusion for Robin or real-power divisor inequalities."))), DescribeRole.Theorem))));
}
