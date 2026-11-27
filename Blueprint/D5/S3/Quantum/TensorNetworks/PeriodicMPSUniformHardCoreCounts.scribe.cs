using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSUniformHardCoreCountsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreCounts";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Move counts on independent configurations of a cycle",
        H("Cyclic insertions, hops and deletions"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodic-hard-core-insertion-count"),
                DeclarationHandle.Create(Module + ".insertion_count_balance"),
                H("Legal insertions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On a ring of length n ≥ 7, let r be the size of an independent set, d the number of occupied starts whose forward distance-two site is occupied, and a the number of legal insertions. Then a + 3r = n + d. Each cyclic triple contributes the insertion indicator at its middle site and the three occupancy indicators. An occupied pair of endpoints gives the extra contribution."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-hard-core-directed-hop-count"),
                DeclarationHandle.Create(Module + ".directed_hop_count"),
                H("Legal directed hops"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The number h of actual ordered nearest-neighbor moves is 2r − 2d. Each occupied site offers two directions. An occupied pair at distance two blocks both moves into its middle site. Forward and backward triple windows enumerate the ordered moves, including those across the seam."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-hard-core-row-balance"),
                DeclarationHandle.Create(Module + ".move_count_row_balance"),
                H("Cancellation in the weighted row"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two triple counts give 2a + h + 4r = 2n. There are r legal deletions, so the combined weight of insertions, deletions and half-weight directed hops is a + r + h/2 = n − r."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-hard-core-deletion-connectivity"),
                DeclarationHandle.Create(Module + ".deletion_reaches_empty"),
                H("Deletion paths to the empty configuration"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any cycle length, deleting an occupied site preserves independence and decreases cardinality by one. Induction on cardinality gives a path from each independent configuration to the empty configuration."))),
                DescribeRole.Theorem))));
}
