using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraSlabRunBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraSlabRunBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sum of actual frozen run counts is bounded by the number of individual extrema.", H("The geometric frozen-run bound"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuraslabrunbound-slabs"),
                DeclarationHandle.Create(Prefix + "actual_slab_bound"), H("The actual slab count"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer unit-edge array with at least two rows and two columns, if both axes have an unoccupied row in their respective orientation, the sum of the actual row and column occupied slab counts is at most its number of individual extrema plus two. The proof combines the exhaustive actual slab partition, existence of both nonneutral types, and the individual-extremum charging theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraslabrunbound-start"),
                DeclarationHandle.Create(Prefix + "FrozenRowRunStart"), H("Actual frozen run starts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual frozen run starts at an unoccupied row that is either the physical first row or immediately follows an occupied row. Thus each maximal consecutive unoccupied interval has one start."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraslabrunbound-relation"),
                DeclarationHandle.Create(Prefix + "slab_card_eq_frozen_runs_add_one"), H("Exact slab and run count relation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every unit-edge array with at least two rows and one column, the number of actual occupied row slabs is exactly one more than the number of frozen row runs. Each nonterminal occupied slab is paired bijectively with the immediately following frozen run start; physical boundary occupancy supplies the unique terminal slab."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraslabrunbound-equality"),
                DeclarationHandle.Create(Prefix + "frozen_run_equality_incidence"), H("The incidence consequences of run equality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When an actual array has as many individual extrema as frozen runs on both axes together, the neutral row and column extremum supports coincide and their slab counts agree. The product of the minimum row slab count minus one with the minimum column slab count minus one vanishes, as does the corresponding maximum product. These consequences use saturation of the full individual-extremum charge; the common-side or four-extremum classification remains a further geometric statement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraslabrunbound-extrema"),
                DeclarationHandle.Create(Prefix + "frozen_runs_le_extrema"), H("The uniform geometric run bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge array with at least two rows and two columns and with a frozen row and a frozen column, the sum of its frozen row run count and frozen column run count is at most the number of its individual ambient extrema. Normalization and any comparison between its minimum and maximum counts are unnecessary. This bound does not classify its equality cases."))), DescribeRole.Theorem))));
}
