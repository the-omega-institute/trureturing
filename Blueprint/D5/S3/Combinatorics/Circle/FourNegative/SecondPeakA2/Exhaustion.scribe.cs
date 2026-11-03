using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2;
internal sealed class ExhaustionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second peak SecondPeakA2: Exhaustion", H("Exhaustion"),
        Blocks(Paragraph(Text("Every independent dyadic p=2^u>=4, q=2^s>=2, and h in {1,2} enters either the large-p branch, the small-p infinite-q branch or the forty-row remainder. The resulting Good witness has no feasibility assumption.")),
            Describe.Lean(DescribeId.Create("dyadic-exists"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Exhaustion.dyadic_exists"), H("dyadic_exists"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("theorem dyadic_exists (u s h : \u2115) (hu : 2\u2264u) (hs : 1\u2264s) (hh : h=1 \u2228 h=2) :     \u2203 v m M : \u2115, \u2203 before : Bool, Good (2^u) (2^s) h v m M before"))), DescribeRole.Theorem)), []));
}
