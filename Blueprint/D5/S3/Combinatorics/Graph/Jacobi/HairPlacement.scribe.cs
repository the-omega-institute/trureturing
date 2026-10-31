using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Jacobi;

internal sealed class HairPlacementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Jacobi/HairPlacement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary branching hair trees vanish in the actual Jacobi quotient", H("Ordinary branching hair trees vanish in the actual Jacobi quotient"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-tree-placement"),
                DeclarationHandle.Create(Prefix + "HairPlacement"), H("Geometric placement with a trivalent parent"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A HairPlacement G t is an injective embedding of the actual finite tree flags into G. It preserves the rotor, ordinary colors and every internal mate; the open root is paired to a disjoint actual trivalent parent. Restricting to a left or right subtree rotates its parent to the appropriate actual binary vertex, preserving the whole exterior graph."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal-socket-extraction"),
                DeclarationHandle.Create(Prefix + "extractCherry"), H("A placed branching tree contains an actual cherry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite ordinary red and blue binary tree t with at least two leaves, every actual HairPlacement G t yields Nonempty (Cherry G). A one-hole shape context is followed through the injective flag embedding to a terminal pair of leaves. The extracted six flags consist of the terminal binary vertex and its actual parent. Their mate and rotor equations give the literal X socket, with no change to the exterior pairing. This is the structural bridge consumed by the vanishing theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("branching-hair-vanishing"),
                DeclarationHandle.Create(Prefix + "branching_hair_tree_vanishes"), H("Vanishing for every actual graft with at least two leaves"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite flag type F, every actual cyclic flag graph G on F with arbitrary numbered exterior anchors, every a in F and every ordinary red and blue binary tree t with at least two leaves, classOf (G.graft a t.model) is zero in the actual rational AS, IHX and ordinary CL quotient. The explicit subdividing graft provides a HairPlacement; structural context descent extracts an actual cherry, and the local AS, IHX and CL proof kills the entire graph. This is the ordinary branching-tree step of Proposition 2.2 and Equation 2.2 in MARKED_TWO_COLOR_FOUR_LOOP_JACOBI_VANISHING. It does not establish the global core presentation or four-loop vanishing. The colors remain ordinary throughout, including singleton colors; they are not numbered anchors."))), DescribeRole.Theorem))));
}
