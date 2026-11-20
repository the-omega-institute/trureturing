using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9CommonBoundaryCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four parallel covers force a negative signed walk",
        H("Four parallel covers force a negative signed walk"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-common-boundary-cover"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CommonBoundaryCover.cover_card_le_three"),
                H("An edge of the common exterior boundary has at most three covers per component"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Consider disjoint separated Huang-balanced cubic supports C and D. If both endpoints of an exterior edge have neighbors in both supports, then at most three edges of C can cover it by a parallel one-coordinate translation. Exchanging C and D gives the same bound on the other side.")),
                    Paragraph(Text("Four parallel C-edges would leave too few distinct directions for a parallel D-edge. If the D-neighbor directions at the two exterior endpoints are disjoint, cubicity forces a closed D-walk with coordinate word ℓ,k,i,j,k,ℓ,i,j.")),
                    Paragraph(Text("Distinct signed coordinate flips anticommute. The word acts as minus the identity, which contradicts switching balance along a closed walk. The obstruction constrains self-collisions and mixed collisions for arbitrary pairs in the 258-vertex problem."))),
                DescribeRole.Theorem)),
        []));
}
