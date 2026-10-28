using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class RationalRowSumDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/KyFanGap/RationalRowSum.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational constant weighted row sums.",
        H("Rational constant weighted row sums"), Blocks(
            Describe.Lean(DescribeId.Create("kyfan-rational-row-sum"),
                DeclarationHandle.Create(Owner + "rational_row_sum"),
                H("Rationality from symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let S be a symmetric rational matrix of any finite order R, p a real vector with coordinate sum one, and c a nonzero real number. If S p = c times the all-ones vector, then c is the real image of a rational number. A rational-linear retraction of the real field onto the rationals turns p/c into a rational solution w of S w = 1. Symmetry gives c times the coordinate sum of w equal to one, so c is the reciprocal of a nonzero rational number. No positivity or invertibility assumption is required."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kyfan-nonsquare-row-sum"),
                DeclarationHandle.Create(Owner + "nonsquare_row_sum_ne"),
                H("Nonsquare obstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural number k that is not a square, no symmetric rational matrix and real vector with coordinate sum one satisfy S p = (1/sqrt(k)) times the all-ones vector. The reciprocal square root is irrational, whereas the preceding theorem forces it to be rational. This includes symmetric matrices whose entries are minus one or one."))),
                DescribeRole.Theorem))));
}
