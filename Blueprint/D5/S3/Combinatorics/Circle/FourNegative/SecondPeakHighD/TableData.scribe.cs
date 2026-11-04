using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD;
internal sealed class TableDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "TableData", H("TableData"),
        Blocks(Paragraph(Text("The literal 24 mod-72 residue rows cover h=1,2 and p=4,8. The late fresh ear occurs exactly for p=4,h=1,r=56; all other rows insert at cut zero. The paired rowBounds retain the common physical interpretation used by the unbounded selectors.")),
            Describe.Lean(DescribeId.Create("highd-tabledata-residue-fresh-exact"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/TableData.residue_fresh_exact"), H("residue_fresh_exact"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Consumed by the full HighD construction with the exact Lean telescope."))), DescribeRole.Theorem)), []));
}
