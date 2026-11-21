using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class ProperEdgeColorPosteriorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform proper edge coloring changes the graph posterior even with identical erased replies.",
        H("A path and a cycle with the same uncolored record"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("proper-edge-colors-change-posterior"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/ProperEdgeColorPosterior.proper_edge_colors_change_posterior"),
                H("The colored record favors the cycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Give the path 0–1–2–3 and the cycle 0–1–2–3–0 equal prior masses. " +
                        "After choosing the graph, uniformly choose one of its proper edge colorings " +
                        "with three colors and query the complete neighbor replies at vertices 1 and 2.")),
                    Paragraph(Text(
                        "Those two vertices have identical uncolored replies in both graphs. " +
                        "Prescribe color 0 on edges 01 and 23 and color 1 on edge 12. " +
                        "The path has one matching coloring among twelve, and the cycle has two " +
                        "matching colorings among eighteen. The posterior probability of the cycle " +
                        "after observing the colored record is four sevenths.")),
                    Paragraph(Text(
                        "The kernel enumerates assignments on the actual edge sets. " +
                        "The two matching cycle assignments differ in the color of edge 30, " +
                        "which only needs to avoid the common color 0 on its two adjacent edges."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("erased-replies-lose-colour-information"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/ProperEdgeColorPosterior.erasedRepliesDoNotDetermineColorLikelihood"),
                H("Erased replies do not determine the colored likelihood"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the four labeled vertices, equality of the complete uncolored replies at " +
                    "vertices 1 and 2 does not determine the likelihood of the selected colored " +
                    "record. The path and cycle realize both erased replies and have positive " +
                    "numbers of proper colorings. Their respective likelihoods are one twelfth " +
                    "and one ninth."))),
                DescribeRole.Theorem))));
}
