using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class CycleSpaceEulerRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite binary graph cycle space has Euler rank m-n+c.",
        H("Graph Cycle Space as First Betti Rank"),
        Blocks(
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
                        "For every finite simple graph G, the binary cycle space has module " +
                        "finrank equal to |E(G)| + c(G) - |V(G)|. The proof projects the " +
                        "existing simple-cycle/fundamental-cycle basis theorem: a spanning " +
                        "forest supplies a chord-indexed basis, and the chord count is the " +
                        "Euler cycle rank.")),
                    Paragraph(Text(
                        "This is the first explicit bridge from the endpoint-differential " +
                        "cycle-space formalization to the standard first Betti invariant. " +
                        "A chain-complex interface, Mac Lane face bases, and cycle-double " +
                        "covers are staged follow-on nodes."))),
                DescribeRole.Theorem))));
}
