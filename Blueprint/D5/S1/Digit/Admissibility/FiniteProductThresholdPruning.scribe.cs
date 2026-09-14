using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class FiniteProductThresholdPruningDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Product Threshold Pruning.",
        H("Finite Product Threshold Pruning"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finiteproductthresholdpruning-exists-threshold-pruning"),
                DeclarationHandle.Create("D5/S1/Digit/Admissibility/FiniteProductThresholdPruning.exists_threshold_pruning"),
                H("Simultaneous bounds for a feasible reduction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let q be a natural number at least two and let A be any finite vector of natural "
                    + "capacities with product of A(i) + 1 at least q. There exists a vector a with "
                    + "a(i) at most A(i) for every coordinate and product of a(i) + 1 still at least q. "
                    + "Every entry of a is at most q minus one, the number of its positive entries is "
                    + "at most the least h with q at most two to the power h, and its product is "
                    + "strictly less than twice q. Choose a feasible vector minimizing the sum of its "
                    + "capacities. Lowering any positive capacity then makes the product less than q. "
                    + "Truncating an oversized entry and deleting a positive coordinate give the "
                    + "entry and support bounds; lowering a positive entry by one gives the product bound."))),
                DescribeRole.Theorem))));
}
