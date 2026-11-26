using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Finite;

internal sealed class EffectiveRobinTangentRowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two exact tangent-price rows extend the original finite Robin margin through log height 101.",
        H("Effective Robin tangent rows"),
        Blocks(
            Paragraph(Text("The row 02 price is 9793/2000000 with literal optimizer 37188534050951960476800 and layer cutoffs 51,9,4,3,2,2,2. Its strict endpoint margins cover 36<=log n<=70.")),
            Paragraph(Text("The row 03 price is 54619/25000000 with literal optimizer 46015447651610234928592313897306120347488000 and layer cutoffs 99,12,5,3,3,2,2,2,2. Its strict endpoint margins cover 70<=log n<=101.")),
            Paragraph(Text("The original Row 01 result covers the lower segment. Concavity of the Robin threshold and exact rational endpoint gaps transfer each fixed-price optimizer certificate to every natural integer in its interval.")),
            Describe.Lean(DescribeId.Create("row02-price"), DeclarationHandle.Create(Prefix + "row02Price"), H("Row 02 price"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact row 02 price is 9793/2000000."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("row02-integer"), DeclarationHandle.Create(Prefix + "row02Integer"), H("Row 02 optimizer"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact row 02 optimizer is 37188534050951960476800."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("row02-optimal"), DeclarationHandle.Create(Prefix + "row02_optimal"), H("Row 02 optimality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The literal row 02 integer is a Golden Resource optimizer at the row 02 price."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("row02-margin"), DeclarationHandle.Create(Prefix + "row02_margin"), H("Row 02 margin"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every positive natural integer with log height in [36,70] has positive original Robin log margin."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("row03-price"), DeclarationHandle.Create(Prefix + "row03Price"), H("Row 03 price"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact row 03 price is 54619/25000000."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("row03-integer"), DeclarationHandle.Create(Prefix + "row03Integer"), H("Row 03 optimizer"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact row 03 optimizer is 46015447651610234928592313897306120347488000."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("row03-optimal"), DeclarationHandle.Create(Prefix + "row03_optimal"), H("Row 03 optimality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The literal row 03 integer is a Golden Resource optimizer at the row 03 price."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("row03-margin"), DeclarationHandle.Create(Prefix + "row03_margin"), H("Row 03 margin"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every positive natural integer with log height in [70,101] has positive original Robin log margin."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("height-101"), DeclarationHandle.Create(Prefix + "robin_margin_through_height_101"), H("Finite margin through height 101"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The existing Row 01 and the two exact tangent rows imply positive original Robin log margin for every natural n>5040 with log n<=101."))), DescribeRole.Theorem)
        )));
}
