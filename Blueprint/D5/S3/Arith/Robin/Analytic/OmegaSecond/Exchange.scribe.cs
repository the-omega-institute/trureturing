using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSecond;

internal sealed class ExchangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal-cardinality prime exchanges with a uniform logarithmic budget.",
        H("Budget-feasible prime exchanges"),
        Blocks(
            Paragraph(Text("The exchange method follows the primorial-side equal-count exchanges and partition-constant mechanism of Erdős–Nicolas 1981, Section 1. The finite system here permits a trimmed prime base. Its negative bins lie inside the base; its positive bins lie outside. Both bin families are pairwise disjoint, and all inserted elements are primes.")),
            Describe.Lean(DescribeId.Create("exchange-system"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Exchange.ExchangeSystem"),
                H("Prime base and disjoint exchange bins"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The system records the actual finite prime sets, their containment and separation properties."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exchange-value-injective"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Exchange.exchange_value_injective"),
                H("Every choice is recoverable"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Unique prime factorization recovers the exchanged support. Membership inside the base recovers the removed union; membership outside recovers the inserted union. Intersecting these unions with their disjoint bins recovers each individual choice, proving injectivity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("omega-exchange-value"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Exchange.omega_exchange_value"),
                H("The distinct-prime count is preserved"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equal numbers of removed and inserted primes make omega of every exchanged product exactly the cardinality of the base."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("card-exchange-choices"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Exchange.card_exchange_choices"),
                H("Exact independent-choice count"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite choice type has cardinality the product over bins of choose(card(negative bin),h) times choose(card(positive bin),h). An overfull request has zero choices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("log-exchange-value-le"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Exchange.log_exchange_value_le"),
                H("Worst-endpoint logarithmic cost"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the base costs at most P-D, each removed prime costs at least log(P)-t_i/s, and each inserted prime at most log(P)+t_i/s, then every exchanged product has logarithm at most P-D+(2/s) sum_i t_i h_i. The factor two accounts for both endpoints of every pair."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("balanced-exchange-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Exchange.balanced_exchange_bound"),
                H("A feasible family in the strict tail"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When the exchange cost is at most D, P is at most log(x), x is positive, and the base cardinality strictly exceeds the original threshold, the product of binomial choice counts is a lower bound for the original tailCount(lambda,x). This is a deterministic budget for every choice, with the strict threshold unchanged."))), DescribeRole.Theorem))));
}
