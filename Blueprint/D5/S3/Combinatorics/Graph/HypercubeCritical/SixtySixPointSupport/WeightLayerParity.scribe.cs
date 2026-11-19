using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport;

internal sealed class WeightLayerParityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "WeightLayerParity", H("Parity of Boolean weight layers"),
        Blocks(
            Paragraph(Text("The parity of the selected degree at any cube vertex equals its membership indicator. Summing this relation over an odd weight layer pairs that layer with the preceding even layer. At order 66, the odd layers total 33 vertices, so the total Boolean weight is congruent to one modulo four. The coordinate half sizes then force an even total deficit. This constrains the 66-vertex case of Hong–Wu–Xia Section 7 Problem 2.")),
            Describe.Lean(
                DescribeId.Create("q9-weight-layer-pair-parity"),
                DeclarationHandle.Create(Prefix + "balanced_cube_even_adjacent_layers"),
                H("Consecutive layers have equal parity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every even weight from zero through eight, the combined size of that layer and its successor is even in a Huang-balanced induced cubic support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-sixty-six-even-total-deficit"),
                DeclarationHandle.Create(Prefix + "balanced_sixty_six_even_total_deficit"),
                H("The total deficit is even"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a 66-vertex Huang-balanced induced cubic support, write each coordinate true-half size as thirty-three minus twice its deficit. The sum of the nine deficits is even."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary"))
        ]));
}
