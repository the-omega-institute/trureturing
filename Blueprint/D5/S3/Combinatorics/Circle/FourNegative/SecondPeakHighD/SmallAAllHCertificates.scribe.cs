using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD;
internal sealed class SmallAAllHCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal positive polynomial windows", H("Universal positive polynomial windows"),
        Blocks(
            Paragraph(Text("For each of twelve residue families, R and U range over all nonnegative integers; for each of eight boundary families, U ranges over all nonnegative integers. Ring proves 340 exact identities. Nonnegative coefficients prove the twelve old/new window inequalities, the v and M stocks, and strict mask separation. These identities use the actual HighD rowBounds, including the fresh charge, and contain no exponent cutoff or finite-grid inference.")),
            Describe.Lean(DescribeId.Create("highd-smallaallhcertificates-residue-bounds"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/SmallAAllHCertificates.residue_bounds"), H("residue_bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Consumed in the construction described here, with the exact telescope supplied by Lean."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("highd-smallaallhcertificates-fixed-bounds"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/SmallAAllHCertificates.fixed_bounds"), H("fixed_bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Consumed in the construction described here, with the exact telescope supplied by Lean."))), DescribeRole.Theorem)), []));
}
