using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCanonicalColumnsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact signed column deletion identities.", H("Exact signed column deletion identities"),
        Blocks(
Describe.Lean(DescribeId.Create("miuracanonicalcolumns-0"),
                DeclarationHandle.Create(Prefix + "frozen_after_left_deletion"), H("A frozen column after a deletion to its left"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an actual unit-edge integer height function, a nonempty row axis, frozen columns j and k, and j<k, deleting j leaves column k-1 frozen in the actual contracted array. The uniform signed edge equations also cover consecutive j and k."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracanonicalcolumns-1"),
                DeclarationHandle.Create(Prefix + "frozen_after_right_deletion"), H("A frozen column after a deletion to its right"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same height and nonempty-row hypotheses, if k<j, deleting frozen column j leaves frozen column k at its original index. At the seam, the height correction equals the genuine uniform slope."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracanonicalcolumns-2"),
                DeclarationHandle.Create(Prefix + "adjacent_deletions_equal"), H("Overlapping deletions give equal functions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an actual unit-edge height function with at least one row, if j and k are frozen and j+1=k, contracting at j and contracting at k give equal functions on the same rectangle with one fewer column. Their signed slopes agree; every height, including the unchanged origin height, agrees."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracanonicalcolumns-3"),
                DeclarationHandle.Create(Prefix + "separated_deletions_commute"), H("Two signed deletions commute with index transport"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For frozen j<k in an actual unit-edge array with a nonempty row axis, contracting j and then k-1 equals contracting k and then j. Each second frozen equation is supplied by the survival identities. The equality concerns all integer values, including both signed corrections, on the rectangle with two fewer columns."))), DescribeRole.Theorem))));
}
