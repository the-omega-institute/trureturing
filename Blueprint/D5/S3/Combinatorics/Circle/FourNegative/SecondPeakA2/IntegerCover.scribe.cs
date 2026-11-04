using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2;
internal sealed class IntegerCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second peak SecondPeakA2: IntegerCover", H("IntegerCover"),
        Blocks(Paragraph(Text("The eight translated integer intervals overlap under 16e<=D and 13D<=A. Euclidean division by 8A transports their chain to every integer X, without a cutoff on X, A or the quotient. The resulting j is between 0 and 15.")),
            Describe.Lean(DescribeId.Create("sixteen-step-cover"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/IntegerCover.sixteen_step_cover"), H("sixteen_step_cover"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("theorem sixteen_step_cover (A D e X : \u2124)     (hD : 0 < D) (he : 0 \u2264 e) (heD : 16*e \u2264 D) (hDA : 13*D \u2264 A) :     \u2203 j v : \u2124, 0 \u2264 j \u2227 j \u2264 15 \u2227       ((e \u2264 X+j*(5*A-D)+8*v*A \u2227 X+j*(5*A-D)+8*v*A \u2264 A-e) \u2228        (3*A+e \u2264 X+j*(5*A-D)+8*v*A \u2227 X+j*(5*A-D)+8*v*A \u2264 4*A-e))"))), DescribeRole.Theorem)), []));
}
