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
                DescribeId.Create("orderedpartitions-orderedpartition-rank-tocuts"),
                DeclarationHandle.Create(Module + ".rank_toCuts"),
                H("Rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("An ordered partition with b blocks has exactly b minus one proper cumulative cuts. Its face rank is n minus b."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orderedpartitions-orderedpartitionsequiv"),
                DeclarationHandle.Create(Module + ".orderedPartitionsEquiv"),
                H("The face dictionary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("An ordered partition is a surjective map from the labels to a nonempty finite linear order of blocks. Taking all proper cumulative cuts gives a cut chain. Conversely, a chain gives an ordered partition whose blocks are the successive differences, including the complement of the largest cut. These maps are inverse when the label set is nonempty."))),
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
