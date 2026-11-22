using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class MeyerovitchYoungQ61SubcriticalDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61Subcritical.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact free-endpoint payoff recursion and a finite reachable state set at subcritical tolls.",
        H("Free-Endpoint Scores for a Two-Mode Switching Game"),
        Blocks(
            Paragraph(Text(
                "This family specializes the value in equations (5) and (6) of Meyerovitch and "
                + "Young, Rationality and computability of the covering radius for sofic shifts. "
                + "Alice has one vertex and two loops with increments 1 and minus the square root "
                + "of 2. Bob has two vertices with signs minus and plus and an edge for each "
                + "ordered pair. The payoff is the source sign times half the increment plus the "
                + "toll c on edges that switch mode. https://arxiv.org/html/2603.21449v1#S4.Ex38")),
            Describe.Lean(
                DescribeId.Create("free-edge-minimum"),
                DeclarationHandle.Create(Owner + "freeMinimum_edge_spec"),
                H("Both Bob endpoints are free"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each real toll, positive horizon and Alice word, the free minimum is "
                    + "the least element of the payoffs of compatible Bob edge walks. A Boolean "
                    + "vertex response determines exactly one such walk, and each walk determines "
                    + "its response with both endpoints included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("minimum-from-overshoots"),
                DeclarationHandle.Create(Owner + "freeMinimum_eq_overshoot"),
                H("Exact finite-horizon payoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every nonnegative toll and every Alice word prefix, the translated "
                    + "difference of the two terminal scores starts at c "
                    + "and follows the clipped update on [0, 2c]. Each overshoot reduces their "
                    + "average by half its size. Taking the lesser terminal score subtracts "
                    + "half the final absolute deviation from c."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-pell-hitting"),
                DeclarationHandle.Create(Owner + "uniformForbiddenHit_pell"),
                H("Uniform hitting of the open forbidden arc"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If twice the toll is below the circumference, a common finite bound works "
                    + "for every phase in the allowed interval. Both increments advance by one "
                    + "modulo the circumference. A positive Pell return with sufficiently small "
                    + "displacement can be repeated to hit the strict interior of the forbidden "
                    + "arc at a positive time within that bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-reachable-scores"),
                DeclarationHandle.Create(Owner + "reachable_finset_of_hit"),
                H("Finite set of actual reachable scores"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonnegative subcritical toll and any uniform hitting bound, each "
                    + "reachable state is determined by its last reset seed and an age strictly "
                    + "below the uniform hitting bound. The possible seeds are 0, c, and 2c. "
                    + "The allowed real interval injects into the circle, so there are at most "
                    + "three times the hitting bound many distinct reachable real scores."))),
                DescribeRole.Theorem))));
}
