using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9SharedContactGeometryReplayDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9SharedContactGeometryReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel-checked refutations exclude all three normalized shared distance-three contacts.",
        H("Replay the three shared-contact refutations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-shared-distance-three"),
                DeclarationHandle.Create(Owner + "no_shared_distance_three"),
                H("Distance-three contacts have disjoint occupied directions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Normalize the shared contact using its overlap size. For every input clause in the "
                    + "corresponding tracked JSON certificate, Lean checks that the local rules imply the exact clause "
                    + "appearing in the formula. Mathlib's LRAT proof replays the derivation of the empty "
                    + "clause under that valuation. The three certificates cover overlap sizes one, two and "
                    + "three."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9SharedContactCNF"))
        ]));
}
