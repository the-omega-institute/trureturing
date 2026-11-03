using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2;
internal sealed class SmallDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second peak SecondPeakA2: Small", H("Small"),
        Blocks(Paragraph(Text("The unbounded small-p sectors use q=64+u polynomial certificates. The exceptional sector uses q=4u and the high/low mask. These branches preserve the same Good predicate and both possible locations of the literal fresh insertion.")),
            Describe.Lean(DescribeId.Create("small-exists"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Small.small_exists"), H("small_exists"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("theorem small_exists (p s h : \u2115)     (hp : p=4 \u2228 p=8 \u2228 p=16 \u2228 p=32) (hq : 64\u22642^s) (hh : h=1 \u2228 h=2) :     \u2203 v m M : \u2115, \u2203 before : Bool, Good p (2^s) h v m M before"))), DescribeRole.Theorem)), []));
}
