using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class GeodesicsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/fresanfigueroa2026mutualvisibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original-host mutual visibility and the auxiliary geometry of the full mixed reconfiguration graph.",
        H("Rooted original-geodesic geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("visible-comparability-triangle"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics.visible_comparability_triangle"),
                H("A visible set has no comparability triangle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Three selected labels of one mutually visible set cannot be pairwise comparable under strict mandatory ancestry towards a common root."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-neighbor-height"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics.common_neighbor_height"),
                H("Height of an actual common neighbor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If u strictly dominates v towards w and y is adjacent to both u and v, the root distance of y equals the root distance of u plus one."))),
                DescribeRole.Theorem),

            Describe.Lean(
                DescribeId.Create("mandatory"),
                DeclarationHandle.Create(Prefix + "Mandatory"),
                H("Mandatory original geodesics"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A vertex is mandatory between two endpoints when every original-host walk attaining their distance contains it. This universal relation is used only as auxiliary geometry; source visibility remains existential."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dominates"),
                DeclarationHandle.Create(Prefix + "Dominates"),
                H("Strict ancestry towards one root"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The nearer vertex is distinct from the root and from the farther vertex and is mandatory on every shortest path from the farther vertex to the root. Distance additivity makes its root distance strictly smaller."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("inward-replacement"),
                DeclarationHandle.Create(Prefix + "inward_replacement"),
                H("Inward replacement of a visible common-neighbor triple"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let the host be connected, let u strictly dominate v towards w, let y be adjacent to both u and v, and let p be adjacent to u with root distance one less than u. If the original triple u,v,y is visible, then p differs from v and y. There are configurations Q with labels p,v,y and P with labels p,y, an actual-host-edge slide from the original triple to Q, and a token removal from Q to P. The root-distance sum of the terminal pair is strictly smaller than that of u,v. The proof first forces the height of y and the exact distances from p to y and v, then builds existential geodesic witnesses from the predecessor edge and the original visible triple.")))))));
}
