using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hamming.ConstantPowerCooling;

internal sealed class ShadowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hamming/ConstantPowerCooling/Shadows.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ambient deletion hypotheses imply the Appendix A edge bound on the support graph.",
        H("The nonclique bound for a class shadow"),
        Blocks(
            Describe.Lean(DescribeId.Create("ambient-deletion-bound"),
                DeclarationHandle.Create(Prefix + "nonclique_shadow_edge_lower_of_ambient_deletion"),
                H("The nonclique bound for a class shadow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Hamming/liuzhangyuzhangji2026optimalcpecc")),
                Blocks(Paragraph(Text("Let t ≥ 1, w > t + 3, and let a finite ambient vertex set have at least t points. A class consists of w-subsets, and each t-subset of the ambient vertex set is disjoint from some word in the class. If the graph on ambient points whose edges are co-occurring pairs has no clique of order w + t, it has at least B(w,t) edges. The union of word supports has at least w + t points. Its induced graph has the same edges up to endpoint inclusion, retains the deletion property, and has minimum degree at least w − 1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("distance-edge-disjointness"),
                DeclarationHandle.Create(Prefix + "shadows_edge_disjoint_of_distance"),
                H("Distance forces disjoint shadow edges"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Hamming/liuzhangyuzhangji2026optimalcpecc")),
                Blocks(Paragraph(Text("For a finite indexed family of classes on a finite ambient vertex set, suppose all word supports have size w and the symmetric difference of supports from distinct classes has size at least 2w − 3. Then the classes' shadow edge sets are pairwise disjoint. A common edge would give two common points to supports from distinct classes, violating the distance condition."))), DescribeRole.Theorem)),
        []));
}
