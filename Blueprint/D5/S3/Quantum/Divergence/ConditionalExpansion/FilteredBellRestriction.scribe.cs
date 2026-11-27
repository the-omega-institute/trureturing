using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.ConditionalExpansion;

internal sealed class FilteredBellRestrictionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Input compression gives a filtered channel whose full Bell bound is strict.",
        H("Filtered channel restriction and a strict Bell bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-by-two-strict-bell-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellRestriction."
                    + "threeByTwo_strict_bell_bound"),
                H("Three-dimensional counterexample"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The normalized diagonal filter has three input levels and two environment "
                    + "levels. Its rows are (1/2, 3/2), (3/2, 1/2), and (1, 1). Its "
                    + "conditional trace-distance expansion is 3/4, while the Bell upper "
                    + "bound computed on the full input is 9/11. The inverse input marginal "
                    + "gives the lower bound. Compressing to the first two levels gives the "
                    + "matching upper bound because the compressed channel's admissible "
                    + "ratios also occur for the original channel."))),
                DescribeRole.Theorem))));
}
