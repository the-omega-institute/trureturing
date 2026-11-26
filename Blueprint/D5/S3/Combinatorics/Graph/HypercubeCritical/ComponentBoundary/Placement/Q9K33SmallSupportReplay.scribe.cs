using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9K33SmallSupportReplayDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-axis contact rectangles force a component smaller than sixty.",
        H("The six-axis nine-mask case in a 258-point candidate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-nine-masks-on-six-axes-in-actual-pair"),
                DeclarationHandle.Create(Owner + "no_nine_masks_on_six_axes_in_actual_pair"),
                H("The six-axis nine-mask case is impossible"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized rectangles and the local degree and parity equations constrain the two actual components. Two-coordinate spectral saturation supplies the corner witnesses. The refutation uses seven clauses requiring an occupied vertex outside specified supports of size fifty-four. Each clause follows from the ambient bound of sixty. Lean checks the clause meanings and replays the resolution certificate. This removes the six-axis branch of Hong–Wu–Xia Problem 2."))), DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33NormalizedRectangle")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33SmallSupportClauses")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33CompletionInputs")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactGeometryReplay"))
        ]));
}
