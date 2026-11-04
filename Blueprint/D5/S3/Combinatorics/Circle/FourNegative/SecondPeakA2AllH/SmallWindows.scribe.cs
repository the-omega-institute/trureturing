using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH;
internal sealed class SmallWindowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Corrected simultaneous window closure", H("Corrected simultaneous window closure"),
        Blocks(
            Describe.Lean(DescribeId.Create("secondpeaka2allh-smallwindows-small-proper-predecessor"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallWindows.small_proper_predecessor"),
                H("small proper predecessor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of corrected simultaneous window closure. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("secondpeaka2allh-smallwindows-finish-small-bounds"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2AllH/SmallWindows.finish_small_bounds"),
                H("finish small bounds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of corrected simultaneous window closure. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Paragraph(Text("For x=4 define Delta=5M-(y-8hp). The sufficient interval is 4h<=Delta<=4hp, with p>=4, q>=2 and h>=4. Together with the four first-window slacks and 1<=v, 2v<=t, finish_small_bounds proves all three old and enlarged window bounds and both M stocks. The lower bound is 4h; no arbitrary-h bound 2h is asserted.")),
            Paragraph(Text("The common second endpoint is governed by r=B-K+ML. Exact polynomial identities show r>=0 and B-1-2r-(y-M)(z+1)>=0. The enlarged second endpoint is 4r+2(y-M)(z+1). The third caps factor through z-8>=0. The integer stock follows from 2M<y and even y. Proper submasks use the predecessor low block with multiplier at least two."))), []));
}
