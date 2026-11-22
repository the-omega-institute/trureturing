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
                H("A common exterior boundary edge in Q9 has at most three parallel covers per support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Consider disjoint separated Huang-balanced cubic supports C and D in the nine-cube. If both endpoints of an exterior edge have neighbors in both supports, then at most three edges of C can cover it by a parallel one-coordinate translation. Exchanging C and D gives the same bound on the other side.")),
                    Paragraph(Text("Four parallel C-edges would leave too few distinct directions for a parallel D-edge. If the D-neighbor directions at the two exterior endpoints are disjoint, cubicity forces a closed D-walk with coordinate word ℓ,k,i,j,k,ℓ,i,j.")),
                    Paragraph(Text("Distinct signed coordinate flips anticommute. The word acts as minus the identity, which contradicts switching balance along a closed walk. This gives a local obstruction to self-collisions and mixed collisions in the 258-vertex setting of Hong–Wu–Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1 §7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2)."))),
                DescribeRole.Theorem)),
        []));
}
