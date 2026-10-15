using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeBoundaryRoutePositionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeBoundaryRoutePositions.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Locate the Actual Zero Left Port in Native Routes.",
        H("Locate the Actual Zero Left Port in Native Routes"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-boundary-route-positions-native-even-left-zero-piece-position"), DeclarationHandle.Create(Prefix + "native_even_left_zero_piece_position"),
                H("The Even Route Has Its Zero Left Port at the Exact Index"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For actual ordered special-child pieces whose finishes follow the even native route at order 2s+2, native port injectivity identifies the unique piece finishing at the zero left port. Its index is exactly s+1, so it comes after the first rooted boundary piece."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-boundary-route-positions-native-odd-left-zero-piece-position"), DeclarationHandle.Create(Prefix + "native_odd_left_zero_piece_position"),
                H("The Odd Route Includes the Empty Ladder Case"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For actual ordered special-child pieces whose finishes follow the odd native route at order 2s+3, the zero left port occurs precisely at index s+1. This exact statement includes order three and supplies the later-cut position used by literal Q slicing."))), DescribeRole.Theorem))));
}
