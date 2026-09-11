using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder.PriceCoordinates;

internal sealed class AbundanceAccessBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary reproducible output and self-supplied operating energy do not determine whether money controls access.",
        H("Abundance and Monetary Access"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("abundance-access-countermodel"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.abundance_preserves_paid_access_difference"),
                H("Abundant goods can coexist with paid scarce access"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The model admits every natural quantity of the first good, balances harvested energy against "
                    + "its operating requirement, and allows at most one reservation of a second good. Charging one "
                    + "unit for the reservation gives strictly more access at wealth one than at wealth zero. "
                    + "This is an inhabited logical countermodel, not an engineering construction of autonomous "
                    + "AI or a prediction of future prices. Arbitrarily large finite output is not actual infinite "
                    + "output at a finite time."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("abundance-inference-refuted"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.not_abundance_makes_wealth_irrelevant"),
                H("Productive abundance alone does not erase monetary access"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The countermodel refutes the universal inference from energy adequacy and arbitrary "
                    + "reproducible output to wealth-independent access under an otherwise unconstrained price rule. "
                    + "It does not establish that money must survive, or that monetary allocation is desirable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("free-access-boundary"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.free_access_ignores_wealth"),
                H("Free admissible choices are independent of wealth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If every admissible choice actually has zero required payment, every nonnegative wealth "
                    + "gives exactly that admissible set. Universal satisfaction additionally requires all "
                    + "jointly feasible desired choices to be in the set. This does not model taxes, outstanding "
                    + "debts, accounting, status, personal meaning, or who controls eligibility."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("free-capacity-boundary"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/PriceCoordinates/AbundanceAccessBoundary.free_rationing_retains_capacity_bound"),
                H("A nonmonetary capacity rule still restricts choices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With zero charges and any natural capacity, every nonnegative wealth gives the same "
                    + "capacity-limited set. Demand exceeding capacity remains unavailable. Scarcity is thus "
                    + "compatible with nonmonetary limits. Selecting between competing people's claims requires "
                    + "an additional social rule, which this single-person menu does not determine."))),
                DescribeRole.Theorem))));
}
