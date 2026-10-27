using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraFiberInverseExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraFiberInverseExpansion.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual reduction paths read complete indexed lengths.", H("Actual reduction paths read complete indexed lengths"),
        Blocks(
            Describe.Lean(DescribeId.Create("miurafiberinverseexpansion-0"),
                DeclarationHandle.Create(Prefix + "reduction_indexed_active"), H("Every actual source has supported weights"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every legal joint reduction from an actual residual array g to an actual height array h supplies supported nonnegative weights on both axes of h. The source dimensions are the core dimensions plus the respective complete weight sums. The occupied positions of g are exactly the cumulative weighted positions of the occupied lines of h. To undo a deletion, locate its surviving inactive position between cumulative core coordinates. The least core coordinate at or beyond that position is frozen, so its weight can be incremented. The exact contraction maps transport all occupied positions; transposition supplies the corresponding row step. The construction follows the actual reduction path and applies to all individual source height functions."))), DescribeRole.Theorem))));
}
