using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ThreeSmallGapPlacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact placement of three same-sign SMALL gap blocks",
        H("Three-small block placement in the sixfold normalization"),
        Blocks(
            Describe.Lean(DescribeId.Create("three-small-one-block"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/ThreeSmallGapPlacement.one_block"),
                H("The one-block schedule"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For one nonempty LARGE gap, the explicit schedule places the three distinguished positions and every consecutive pair. The pair valleys and peaks stay within the scaled strip, the total is zero, and deleting the three SMALL positions leaves the forward LARGE range."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("three-small-two-blocks"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/ThreeSmallGapPlacement.two_blocks"),
                H("The two-block insertion schedules"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two nonempty LARGE gaps, the cut selected from the two endpoint deficits gives a complete permutation with zero total and every prefix in the scaled strip. The proof covers both orderings of the two deficits, including the corrected intermediate peak bound, and deletes exactly the three SMALL positions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("three-small-three-blocks"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/ThreeSmallGapPlacement.three_blocks"),
                H("The three-block insertion schedule"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For three nonempty LARGE gaps, the least admissible Y cut and the aligned Z cut place the three SMALL positions between complete pair blocks. The geometric valley and peak inequalities certify every prefix, endpoint equations certify zero total, and the deleted LARGE arcs remain in forward order."))),
                DescribeRole.Theorem),
            Paragraph(Text("These placement lemmas are consumed by the native exactly-three same-sign SMALL completion. They retain physical labels, so repeated numerical values, nonunits and proper numerical periods remain within the stated hypotheses."))), []));
}
