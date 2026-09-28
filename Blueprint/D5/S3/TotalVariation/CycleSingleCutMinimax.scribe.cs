using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class CycleSingleCutMinimaxDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Single-cut couplings give the exact error budgets and attained minimax value for a finite permutation cycle.",
        H("Sharp coupling budgets on a permutation cycle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cycle-single-cut-minimax"),
                DeclarationHandle.Create("D5/S3/TotalVariation/CycleSingleCutMinimax.cycle_single_cut_minimax"),
                H("Single cuts, nonnegative budgets, and attainment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let B be a finite nonempty set, let g be a permutation of B, and let mu be a "
                        + "nonnegative probability table invariant under g. There are N = n + 1 nodes, "
                        + "for any natural n; in particular this includes every N at least three. "
                        + "Every node of a competing joint law has marginal mu. "
                        + "Internal edges require equal consecutive labels; the closing edge requires "
                        + "the first label to be g of the last. Each edge error is the total variation "
                        + "between its actual pair marginal and the ideal graph coupling. Put a equal "
                        + "to the mu mass of the labels moved by g. Zero entries of mu are allowed.")),
                    Paragraph(Text(
                        "For each edge k, send x to the tuple whose coordinates through k equal x "
                        + "and whose later coordinates equal the inverse of g applied to x. The "
                        + "pushforward P(k) has all node marginals mu and error a on edge k, zero "
                        + "on the other edges. For any nonnegative cut weights pi summing to one, "
                        + "the mixture of the P(k) has error a times pi(i) on edge i.")),
                    Paragraph(Text(
                        "For every competing joint law, graph total variation equals the probability "
                        + "that the corresponding edge relation fails. A tuple whose first label is "
                        + "moved by g cannot satisfy all the cycle relations: propagation along the "
                        + "internal edges and the closing edge would make that label fixed. Therefore "
                        + "the sum of the errors is at least a. Mixture errors above follow from "
                        + "linearity of event probabilities; total variation need not be linear on "
                        + "arbitrary mixtures.")),
                    Paragraph(Text(
                        "For every finite real vector epsilon with nonnegative entries, a joint law "
                        + "with error at most epsilon(i) on each edge exists exactly when the sum "
                        + "of epsilon is at least a. The minimum of the largest edge error is attained "
                        + "and equals a divided by N. Uniform cut weights attain it. When a is "
                        + "positive and the sum of epsilon is at least a, normalizing epsilon by its "
                        + "sum gives a feasible cut mixture, "
                        + "and a zero budget coordinate has zero cut weight. All zero budgets are "
                        + "feasible exactly when a is zero; this case does not require division by a.")),
                    Paragraph(Text(
                        "The same budget equivalence and attained minimum hold in any convex class "
                        + "of real joint tables containing every single-cut law. Such a class contains "
                        + "all their probability mixtures. Full tuple support and convexity alone do "
                        + "not suffice: for the binary flip triangle, the singleton class containing "
                        + "the independent uniform joint law is convex and assigns positive mass to "
                        + "every tuple. Its node marginals are uniform, a equals one, and every edge "
                        + "error equals one half. Thus budgets of one third on each edge are "
                        + "infeasible in that class, even though their sum equals a."))),
                DescribeRole.Theorem))));
}
