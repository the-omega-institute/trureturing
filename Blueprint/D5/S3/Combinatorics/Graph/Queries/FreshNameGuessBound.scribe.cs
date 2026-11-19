using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class FreshNameGuessBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite adaptive query bound for uniformly named graphs.",
        H("Avoiding a hit at an unknown name"),
        Blocks(Describe.Lean(
            DescribeId.Create("fresh-name-guess-survival"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/Queries/FreshNameGuessBound.fresh_guess_survival_ge"),
            H("Hypergeometric bound for a finite query budget"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Fix a finite simple graph, a finite name space and an injective reference naming. "
                + "The initial names are a subset of the range of the reference naming. "
                + "Choose uniformly from the injections that preserve the assignments of those "
                + "initial names. A deterministic strategy queries one name at a time and receives "
                + "either all neighbor names or a miss marker. Run the strategy for at most the "
                + "given query budget. In each successful reply, the queried name and all returned "
                + "names join the known set. The probability that every successful query uses a "
                + "name already known when it is queried is at least the ratio of the binomial "
                + "coefficient for the invalid names to the coefficient for all initially available "
                + "names. In both coefficients the lower argument is the smaller of the query "
                + "budget and the number of initially available names.")),
                Paragraph(Text(
                    "Partition the surviving namings by their query transcripts. The next query "
                    + "is fixed within each part. If it uses a fresh name, the conditional hit "
                    + "probability is the ratio of the remaining hidden vertices to the fresh "
                    + "names. Revealing additional valid names cannot increase the baseline hit bound, "
                    + "and the number of distinct failed names is at most the number of preceding "
                    + "queries. Summing over transcripts bounds the decrease in survival at each "
                    + "step. The product of the corresponding miss probabilities reduces to the "
                    + "stated binomial ratio."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fresh-name-guess-attainment"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/FreshNameGuessBound.exists_strategy_attaining_guess_survival"),
                H("Distinct guesses attain the bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the same finite graph, initial naming and uniform distribution as in the "
                    + "preceding bound. There exists a deterministic strategy with depth at most the "
                    + "query budget whose probability of avoiding an unknown-name hit is exactly "
                    + "the binomial ratio. Fix a list of distinct initially unknown names with "
                    + "length equal to the smaller of the budget and the number of such names. "
                    + "Query in that order until the first hit or the end of the list. The run "
                    + "avoids an unknown-name hit precisely when the naming omits every listed "
                    + "name. Restricting to the unnamed vertices counts the surviving injections "
                    + "by a falling factorial. Dividing by the count of all compatible injections "
                    + "gives the stated ratio."))),
                DescribeRole.Theorem))));
}
