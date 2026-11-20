using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.DiscreteGravity;

internal sealed class TreeConstantRatiosDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/DiscreteGravity/TreeConstantRatios.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/mazhang2026treeratios");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive solution of the tree equations of motion on a connected tree with an edge has "
            + "constant edge lengths exactly when its vertex ratios are constant.",
        H("Constant lengths and constant vertex ratios on trees"),
        Blocks(
            Describe.Lean(DescribeId.Create("tree-constant-ratios"),
                DeclarationHandle.Create(Prefix + "constant_iff"),
                H("Constant lengths iff constant ratios"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let g be a connected locally finite tree with at least one edge and ℓ a "
                    + "positive symmetric edge-length function solving the tree equations of "
                    + "motion of A. Huang, B. Stoica, X. Xia and X. Zhong, "
                    + "(R_i² + R_j²)/ℓ_ij − R_i − R_j = 0, where R_i = c_i/d_i with c_i = Σ 1/ℓ_ij "
                    + "and d_i = Σ 1/ℓ_ij² over the neighbours j of i. Then the edge lengths are "
                    + "globally constant if and only if R_i = R for every vertex and some R > 0. "
                    + "If every edge has length c, then c > 0, every vertex has a neighbour since "
                    + "the tree is connected and has an edge, and c_i = deg(i)/c, d_i = deg(i)/c² "
                    + "give R_i = c. If R_i = R > 0 everywhere, the edge equation reads "
                    + "2R²/ℓ_ij − 2R = 0, so ℓ_ij = R. This is Corollary 5 of H. Ma and "
                    + "W. Zhang."))),
                DescribeRole.Theorem))));
}
