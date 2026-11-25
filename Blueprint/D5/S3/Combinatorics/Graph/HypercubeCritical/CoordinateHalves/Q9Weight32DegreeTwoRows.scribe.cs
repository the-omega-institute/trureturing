using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9Weight32DegreeTwoRowsDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32DegreeTwoRows";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A 32-site support of the eight-cube whose row degrees are zero, two, or four has at least eighteen degree-two rows.",
        H("At least eighteen rows see exactly two support sites"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-degree-two-rows"),
                DeclarationHandle.Create(Module + ".degreeTwoRows_add_four_at_site"),
                H("Each support site gives a local inequality on degree-two rows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a 32-site support with row degrees zero, two, or four, let n₂ count all degree-two rows and let a count those adjacent to a chosen support site. Then n₂ + 4a is at least 22. Translate the chosen site to zero and count pairs of weight-two support sites through their common rows in layers one and three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("degree-two-rows-lower-bound"),
                DeclarationHandle.Create(Module + ".eighteen_le_degreeTwoRows"),
                H("At least eighteen rows see exactly two support sites"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With the same support and row-degree hypotheses, sum the translated local inequality over all thirty-two sites. Each degree-two row contributes once at each of its two support neighbors."))),
                DescribeRole.Theorem)),
        []));
}
