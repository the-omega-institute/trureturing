using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraFiberIndexedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraFiberIndexed.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Indexed actual frozen-line expansion.", H("All prescribed frozen-line insertions in one actual array"),
        Blocks(
            Describe.Lean(DescribeId.Create("miurafiberindexed-0"),
                DeclarationHandle.Create(Prefix + "columnPosition"), H("Cumulative surviving coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An original column j has final coordinate j plus the sum of all prescribed extra copies at original columns k at or before j. This is a natural coordinate in the expanded rectangle."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miurafiberindexed-1"),
                DeclarationHandle.Create(Prefix + "ColumnExtremaExpansion"), H("Exact individual extremum transport"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each actual cell of the expanded function, being a strict full-neighbour minimum is equivalent to coming from an original minimum with unchanged row and the cumulative column coordinate. The same equivalence holds separately for every maximum. The predicates concern actual integer height functions on the two rectangles."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miurafiberindexed-2"),
                DeclarationHandle.Create(Prefix + "indexed_column_expansion"), H("Simultaneous realization of every finite insertion vector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given an actual normalized residual array with a nonempty row axis, prescribe a natural number of extra copies at each original column, supported only on genuinely frozen columns. A single actual normalized unit-edge array exists at width n plus the sum of all those coordinates. It has the same exact minimum and maximum counts and original common-side exclusion, reduces to the original function through legal frozen-pair deletions, and satisfies both exact individual extremum transport equivalences. Induction on the total number of insertions preserves the ordered coordinates and proves frozen availability at every prescribed original line. This result does not identify every array in a joint core fiber with such a vector."))), DescribeRole.Theorem))));
}
