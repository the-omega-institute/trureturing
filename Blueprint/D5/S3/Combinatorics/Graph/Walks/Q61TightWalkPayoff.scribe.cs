using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class Q61TightWalkPayoffDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/Walks/Q61TightWalkPayoff.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero-start free-endpoint payoff lower bound from tight min-plus walks.",
        H("Zero-start payoff from a tight walk"),
        Blocks(
            Paragraph(Text("In the complete-Bob model of Meyerovitch–Young Question 6.1, fix a legal Alice walk of length n from s to t. Bob has m states, with m positive. The payoff of this word is the least terminal score from the all-zero initial vector. This minimizes Bob's cost over walks with arbitrary initial and terminal states. https://arxiv.org/html/2603.21449v1#S4.E6")),
            Describe.Lean(
                DescribeId.Create("matrix-minimum-from-assignment-slack"),
                DeclarationHandle.Create(Prefix + "matrixMinimum_ge_of_assignmentSlack"),
                H("A payoff lower bound with the actual slack"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let x be an auxiliary input anchored at zero with spread at most B, and let y be the terminal score vector from x. Assume that on each edge every ordered difference between entries in the same row is at most B. Then y also has spread at most B. Subtract the maximum of x from every coordinate of x. The translated vector lies coordinatewise below the all-zero vector. Min-plus updates preserve coordinatewise order and commute with common translations, so the physical payoff is at least the minimum of y minus the maximum of x.")),
                    Paragraph(Text("The average score gain from x to y equals this comparison value plus two average deviations. These are the input deficits below the maximum and the output excesses above the minimum. In each sum at least one term vanishes and every term is at most B, so each average is at most (1 − 1/m)B.")),
                    Paragraph(Text("With rate r, total-score potential H and actual assignment slack Δ at x, the average gain is nr + (H(s) − H(t) − Δ)/m. The zero-start payoff with a free terminal state is therefore at least nr + (H(s) − H(t) − Δ)/m − 2(1 − 1/m)B."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrix-minimum-from-tight-walk"),
                DeclarationHandle.Create(Prefix + "matrixMinimum_ge_of_tight_walk"),
                H("The lower bound for a walk tight from an anchored input"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose the chosen permutation on each edge has cost at most mr plus the source potential minus the target potential. If the walk is tight from some anchored input of spread at most B, each edge attains this cap and its assignment guards hold at the scores produced from that input by the preceding prefix. The assignment certificate then gives Δ = 0.")),
                    Paragraph(Text("Under the same within-row spread bound, the very same word has physical zero-start, free-terminal payoff at least nr + (H(s) − H(t))/m − 2(1 − 1/m)B. The spread term is independent of the walk length and vanishes for a single Bob state."))),
                DescribeRole.Theorem))));
}
