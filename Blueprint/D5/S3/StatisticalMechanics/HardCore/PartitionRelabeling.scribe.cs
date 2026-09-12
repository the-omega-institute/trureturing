using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class PartitionRelabelingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact correspondence between grid geometry and actual independent-set messages.",
        H("PartitionRelabeling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hc-partitionrelabeling-independent-image-iff"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.independent_image_iff"),
                H("Exact independent configurations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Adjacency preservation and reflection transport independence in both directions. The source and target use the existing actual independent-set predicate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-partitionrelabeling-configurations-relabel"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.configurations_relabel"),
                H("A bijection of the complete configuration families"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse image under the vertex equivalence supplies surjectivity. Equality is at the configuration-set level, before counting or weighting."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-partitionrelabeling-partition-relabel"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.partition_relabel"),
                H("Transport every vertex weight"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Summing the transported configuration weights gives an exact commutative-semiring identity, including polynomial and complex activities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-partitionrelabeling-image-erase-equiv"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/PartitionRelabeling.image_erase_equiv"),
                H("Transport a marked deletion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same relabeling carries the marked numerator domain and the full denominator domain. No cancellation or nonzero assumption occurs."))),
                DescribeRole.Theorem))));
}
