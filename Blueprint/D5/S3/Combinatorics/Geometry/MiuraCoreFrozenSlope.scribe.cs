using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreFrozenSlopeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreFrozenSlope.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miuradegrees");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite signed contraction on the actual rectangular height grid.", H("One slope for the whole column"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracorefrozenslope-0"),
                DeclarationHandle.Create(Prefix + "inactive_imp_frozenColumn"), H("Extremum-free columns are symmetric"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For an integer unit-edge height function on a nonempty row axis, every unoccupied interior column has symmetric horizontal neighbours at every row."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorefrozenslope-1"),
                DeclarationHandle.Create(Prefix + "frozenColumn_iff_inactive"), H("Frozen classification"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("An interior column is symmetric exactly when it has no strict local extremum, using all existing ambient neighbours."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorefrozenslope-2"),
                DeclarationHandle.Create(Prefix + "frozenColumn_dL_const_adjacent"), H("Adjacent rows have the same slope"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a frozen column in an actual unit-edge height function, its left horizontal height difference agrees between adjacent rows."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracorefrozenslope-3"),
                DeclarationHandle.Create(Prefix + "frozenColumn_dL_eq_row0"), H("One slope for the whole column"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("On a nonempty row axis, induction along adjacent rows identifies every left horizontal difference with its value at row zero."))), DescribeRole.Theorem))));
}
