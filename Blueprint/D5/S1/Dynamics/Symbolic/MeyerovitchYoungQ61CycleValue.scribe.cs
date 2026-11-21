using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class MeyerovitchYoungQ61CycleValueDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ61CycleValue.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A maximum reachable cycle mean gives the original free-endpoint value in this family.",
        H("The Subcritical Two-Mode Value"),
        Blocks(
            Paragraph(Text(
                "The vertices are the reachable real scores, starting at c. Each Alice loop "
                + "gives a labelled edge to the next clipped score. Its weight is the exact change "
                + "in the minimum payoff over all compatible Bob walks with free endpoints.")),
            Describe.Lean(
                DescribeId.Create("bounded-horizon-error"),
                DeclarationHandle.Create(Owner + "maximin_cycle_estimate_of_hit"),
                H("Bounded error at finite horizons"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonnegative subcritical toll and any uniform hitting bound, a "
                    + "reachable simple cycle attains a mean that bounds the average weight "
                    + "of every positive-length closed walk. For all sufficiently large "
                    + "horizons, the difference between the maximin and the horizon times that "
                    + "mean is bounded above and below by constants. A potential gives the "
                    + "upper bound. For the lower bound, reach the cycle from c, repeat it, "
                    + "and pad to the prescribed horizon."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("subcritical-cycle-value"),
                DeclarationHandle.Create(Owner + "maximin_tendsto_cycleMean_subcritical"),
                H("The original value is attained as a simple cycle mean"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every real toll satisfying 0 ≤ 2c < 1 + √2 admits a uniform Pell "
                    + "hitting bound. Dividing the finite-horizon estimate by the horizon "
                    + "gives convergence to the mean of a reachable simple cycle, and every "
                    + "reachable closed walk satisfies the corresponding upper bound."))),
                DescribeRole.Theorem))));
}
