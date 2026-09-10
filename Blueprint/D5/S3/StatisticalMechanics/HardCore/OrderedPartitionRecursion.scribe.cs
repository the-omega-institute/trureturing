using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class OrderedPartitionRecursionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered elimination is derived from actual independent-set partitions, retaining all intermediate domains.",
        H("Ordered partition recursion"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-after-erases"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.afterErases"),
                H("Successive actual vertex deletions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each listed vertex is erased from the current finite domain before continuing."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-deletion-numerator-product"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.numeratorProduct"),
                H("Vacant numerator factors"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each factor is the independent-set partition after the next vertex deletion."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-deletion-denominator-product"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.denominatorProduct"),
                H("Pre-deletion denominator factors"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each factor is the independent-set partition before the next deletion. These are actual proper domains when elimination begins after removing the root."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-vacancy-product"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.vacancyProduct"),
                H("Ordered product of actual vacancy ratios"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product retains the successive intermediate subgraphs. Later ratio identities explicitly discharge the nonzero denominator obligations."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-after-erases-set"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.afterErases_eq_sdiff"),
                H("Final-domain set identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The final domain equals the original domain minus the listed vertex set, including lists with repeated entries."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-telescoping-cross"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.telescoping_cross"),
                H("Telescoping without division"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The starting partition times the numerator product equals the ending partition times the denominator product. The semiring identity remains valid when any factor vanishes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-after-erases-neighbors"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.afterErases_neighbors"),
                H("Actual closed-neighborhood domain"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When the list represents exactly the root neighbors in the original domain, erasing that list after the root gives the closed-complement domain."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-ordered-partition-cross"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.ordered_partition_cross"),
                H("The polynomial recurrence at every activity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combine the actual configuration deletion identity with denominator-free telescoping. No nonvanishing assumption is used, so complex zeros do not invalidate the identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-partition-ordered-recursion"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.partition_ordered_recursion"),
                H("Derived ratio recursion on proper domains"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonzero partitions are required only for subsets of the domain after root deletion. The root partition is excluded from the premises. Exact factor cancellation then identifies the familiar hard-core recurrence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-local-denominator-nonvanishing"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.partition_nonzero_of_local_denominator"),
                H("Noncircular nonvanishing propagation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Smaller-domain nonvanishing and a nonzero local recursion denominator imply that the original independent-set partition is nonzero. A later complex message-domain theorem must establish the local denominator condition."))), DescribeRole.Theorem),
            Paragraph(Text("These are classical elimination identities on the source-owned independent-set sum. The proof scripts are logically reviewed candidates, with no executed Lean or Scribe compilation claimed.")))));
}
