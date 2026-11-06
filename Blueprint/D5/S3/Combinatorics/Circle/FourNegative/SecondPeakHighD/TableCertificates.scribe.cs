using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD;
internal sealed class TableCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "TableCertificates", H("TableCertificates"),
        Blocks(Paragraph(Text("The 24 residue families supply exact paired windows, stock limits and actual natural submasks. These rows are consumed by the unrestricted HighD selector.")),
            Describe.Lean(DescribeId.Create("highd-tablecertificates-residue-bounds"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/TableCertificates.residue_bounds"), H("residue_bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Consumed by the full HighD construction with the exact Lean telescope."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("highd-tablecertificates-residue-submask"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/TableCertificates.residue_submask"), H("residue_submask"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Consumed by the full HighD construction with the exact Lean telescope."))), DescribeRole.Theorem)), []));
}
