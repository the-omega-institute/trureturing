using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder.PriceCoordinates;

internal sealed class ThresholdAccessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A restricted threshold family is constant above a floor exactly when all admissible charges lie below it.",
        H("Threshold Access"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("threshold-family-constancy"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/PriceCoordinates/ThresholdAccess.threshold_sets_constant_iff"),
                H("Exact boundary of threshold independence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix an admissible set, a charge for each item, and a floor in any linearly ordered level type. "
                        + "Every budget above the floor gives the same access set precisely when every admissible "
                        + "item has charge at most the floor. Testing the maximum of the floor and an item's charge "
                        + "establishes necessity. Mathlib's set-separation extensionality establishes sufficiency.")),
                    Paragraph(Text(
                        "For money, nonmonetary eligibility belongs to the admissible set and payment is a separate "
                        + "input. For scheduling, charges can instead be job durations and the budget a deadline. "
                        + "The theorem assumes no production technology, ownership regime, welfare ordering, or equilibrium."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("threshold-strict-growth"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/PriceCoordinates/ThresholdAccess.threshold_set_strict_of_witness"),
                H("A priced witness strictly enlarges access"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An admissible item whose charge is strictly above the lower budget and at most the upper "
                    + "budget witnesses strict inclusion between the two access sets. This concerns the entire "
                    + "set of accessible choices, not a person's preference or the item's production cost."))),
                DescribeRole.Theorem))));
}
