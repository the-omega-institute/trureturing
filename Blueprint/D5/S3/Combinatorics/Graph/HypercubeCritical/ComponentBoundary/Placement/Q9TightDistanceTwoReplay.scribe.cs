using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9TightDistanceTwoReplayDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9TightDistanceTwoReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel-checked opposing-star refutations exclude six distance-two masks.",
        H("Six distance-two masks are impossible"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minimum-displacements-card-ne-six"),
                DeclarationHandle.Create(Owner + "minimum_displacements_card_ne_six"),
                H("Six distance-two masks are impossible"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each of the two missing-axis orbits, the normalized supports satisfy every clause used in the corresponding tracked certificate. Mathlib replays the LRAT derivation of the empty clause in Lean. The two refutations exclude equality in the six-mask lower bound for connected balanced cubic supports with universally singular signed defects."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9TightDistanceTwoCNF")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9SharedContactGeometryReplay"))
        ]));
}
