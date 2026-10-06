using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class CycleSpaceEulerRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binary graph boundary kernel is the first Betti space with Euler rank m-n+c.",
        H("Graph Cycle Space as First Betti Rank"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boundary-kernel-is-cycle-space"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/CycleSpaceEulerRank." +
                    "graphFirstHomology_eq_simpleCycleSpace"),
                H("Boundary-kernel identification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The graph boundary sends an edge labeling to the linear functional " +
                    "obtained by summing endpoint characters. Its kernel is exactly the " +
                    "existing span of simple-cycle edge indicators. This is the finite " +
                    "unoriented chain model over ZMod 2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cycle-space-euler-rank"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/CycleSpaceEulerRank." +
                    "graphBettiOne_eq_eulerCycleRank"),
                H("Cycle-space Euler rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite simple graph G, the binary boundary kernel has " +
                        "module finrank equal to |E(G)| + c(G) - |V(G)|. The proof projects " +
                        "the existing simple-cycle/fundamental-cycle basis theorem: a " +
                        "spanning forest supplies a chord-indexed basis, and the chord " +
                        "count is the Euler cycle rank.")),
                    Paragraph(Text(
                        "Mac Lane face bases and cycle-double-cover interfaces are staged " +
                        "follow-on nodes; the classical Cycle Double Cover statement " +
                        "is not claimed as an unresolved problem here."))),
                DescribeRole.Theorem))));
}
