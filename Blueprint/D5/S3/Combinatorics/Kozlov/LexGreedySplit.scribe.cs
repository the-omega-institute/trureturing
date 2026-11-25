using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Kozlov;

internal sealed class LexGreedySplitDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Convexity/snellman2026kozlov");
    private const string Prefix = "D5/S3/Combinatorics/Kozlov/LexGreedySplit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exchange inequality reduces the minimization over component sizes to filling the components from left to right.",
        H("Greedy placement minimizes upper-shadow cost"),
        Blocks(
            Node("greedy", "greedy", "Greedy allocation", DescribeRole.Definition,
                "Give each component the lesser of its capacity and the available mass, then recurse on what remains."),
            Node("cost", "cost", "Total component cost", DescribeRole.Definition,
                "Apply the component cost to each degree and its allocated size and sum over the paired lists."),
            Node("feasible", "Feasible", "Capacity constraints on allocations", DescribeRole.Definition,
                "Pair each component with one size and bound that size by its capacity."),
            Node("exchange", "Exchange", "Two-component cost comparison", DescribeRole.Definition,
                "For an ordered pair, fill the first component as far as possible with the two masses. The resulting combined cost is at most the initial combined cost."),
            Node("cost-nil", "cost_nil", "Cost with no components", DescribeRole.Lemma,
                "Pairing an empty degree list gives an empty sum."),
            Node("cost-cons", "cost_cons", "Remove the first cost term", DescribeRole.Lemma,
                "The cost of paired nonempty lists is the first component cost plus the remaining cost."),
            Node("greedy-feasible", "greedy_feasible", "Greedy sizes respect all capacities", DescribeRole.Lemma,
                "Each recursive head is bounded by its capacity and the tails have matched lengths."),
            Node("greedy-sum", "greedy_sum", "Total greedy allocation", DescribeRole.Lemma,
                "The assigned mass is the lesser of the requested mass and the total capacity."),
            Node("absorb", "absorb", "Absorb tail mass into the first component", DescribeRole.Lemma,
                "Apply the exchange to move mass from successive tail positions into the first component until it is full or the tail is exhausted."),
            Node("greedy-le-of-exchange", "greedy_le_of_exchange", "Greedy allocation minimizes cost", DescribeRole.Theorem,
                "Absorb as much tail mass as possible into the first component. Induct on the remaining list at its unchanged residual total."),
            Node("capz", "capZ", "Capacity in an integer degree", DescribeRole.Definition,
                "Use the binomial capacity at nonnegative degrees and zero at negative degrees."),
            Node("costz", "costZ", "Shadow cost in an integer degree", DescribeRole.Definition,
                "Use the recursive shadow count at nonnegative degrees and zero at negative degrees."),
            Node("exchange-sig", "exchange_sig", "Upper-shadow cost admits the block exchange", DescribeRole.Lemma,
                "Apply the two numerical inequalities on either side of the first capacity. Negative degrees have zero admissible mass."),
            Node("prop-greedy", "prop_greedy", "Minimum shadow cost for ordered degrees", DescribeRole.Theorem,
                "Apply the greedy exchange principle to binomial capacities and upper-shadow costs with the degrees in nonincreasing order."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("kozlov-lex-greedy-split-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
