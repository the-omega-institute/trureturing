using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails;
internal sealed class C2GatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal doubled gates for the c=2 residual cone", H("Universal doubled gates for the c=2 residual cone"),
        Blocks(
            Describe.Lean(DescribeId.Create("c2-scalar-drops"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C2Gates.c2_scalar_drops"),
                H("c2_scalar_drops"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For e>=1 and ell>=0, the original five symbolic bank charts establish every old lower seam and new upper peak. The exceptional e=4 uses terminal order [2,3,0,1]; the other charts retain their actual c2Order. The high tail retains its 4t correction. New successors finish at OLD A. Scalar gates acquire their physical meaning only through C2Endpoint. Coefficients and chart selection are attributed to uxwv-c2-a3-full-tail-20261102.py and the supplied universal-gates construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("c2-doubled-gates"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C2Gates.c2_doubled_gates"),
                H("c2_doubled_gates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For e>=1 and ell>=0, the original five symbolic bank charts establish every old lower seam and new upper peak. The exceptional e=4 uses terminal order [2,3,0,1]; the other charts retain their actual c2Order. The high tail retains its 4t correction. New successors finish at OLD A. Scalar gates acquire their physical meaning only through C2Endpoint. Coefficients and chart selection are attributed to uxwv-c2-a3-full-tail-20261102.py and the supplied universal-gates construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("c2-fresh-bounds"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C2Gates.c2_fresh_bounds"),
                H("c2_fresh_bounds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For e>=1 and ell>=0, the original five symbolic bank charts establish every old lower seam and new upper peak. The exceptional e=4 uses terminal order [2,3,0,1]; the other charts retain their actual c2Order. The high tail retains its 4t correction. New successors finish at OLD A. Scalar gates acquire their physical meaning only through C2Endpoint. Coefficients and chart selection are attributed to uxwv-c2-a3-full-tail-20261102.py and the supplied universal-gates construction."))),
                DescribeRole.Theorem)), []));
}
