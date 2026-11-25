using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.Permutohedra;

internal sealed class OrderedPartitionsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Geometry/Permutohedra/OrderedPartitions";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/rossi2026permutohedron");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered partitions and face order.",
        H("Ordered partitions and face order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("orderedpartitions-orderedpartition"),
                DeclarationHandle.Create(Module + ".OrderedPartition"),
                H("Ordered partitions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("An ordered partition of Fin n specifies a natural number of separators and a surjection from the labels onto the ordered block indices, whose count is one plus the number of separators."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orderedpartitions-orderedpartition-cut"),
                DeclarationHandle.Create(Module + ".cut"),
                H("A cumulative cut"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At a zero-based separator index i, take all labels whose block index is at most i."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orderedpartitions-orderedpartition-tocuts"),
                DeclarationHandle.Create(Module + ".toCuts"),
                H("The chain of cumulative cuts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take the cumulative cut at every separator. Surjectivity makes each cut proper and nonempty, and the cuts are nested in separator order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orderedpartitions-orderedpartition-rank-tocuts"),
                DeclarationHandle.Create(Module + ".rank_toCuts"),
                H("Rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("An ordered partition with b blocks has exactly b minus one proper cumulative cuts. Its face rank is n minus b."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orderedpartitions-cutchain-topartition"),
                DeclarationHandle.Create(Module + ".toPartition"),
                H("The partition of a chain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("On a nonempty label set, order the cuts by increasing size. Use the cuts as separators, and send each label to the block indexed by the number of cuts that omit it. The successive differences and the complement of the largest cut give the nonempty blocks. An empty chain gives a single block."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orderedpartitions-orderedpartitionsequiv"),
                DeclarationHandle.Create(Module + ".orderedPartitionsEquiv"),
                H("The face dictionary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Taking cumulative cuts and reconstructing the ordered blocks are inverse maps when the label set is nonempty."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orderedpartitions-mergesadjacent"),
                DeclarationHandle.Create(Module + ".MergesAdjacent"),
                H("Merging adjacent blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A partition p merges to q when a monotone surjection from the block indices of p to those of q sends the block of each label in p to its block in q."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orderedpartitions-mergesadjacent-iff"),
                DeclarationHandle.Create(Module + ".mergesAdjacent_iff"),
                H("Adjacent block merges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("One partition is obtained from another by merging adjacent blocks exactly when its family of cumulative cuts is contained in the other's family. The merging map on block labels is monotone and surjective."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orderedpartitions-permutationatomsequiv"),
                DeclarationHandle.Create(Module + ".permutationAtomsEquiv"),
                H("Singleton-block partitions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Permutation flags recover each entry by the difference between successive prefixes, including the final label. Consequently permutations correspond bijectively to atoms."))),
                DescribeRole.Definition))));
}
