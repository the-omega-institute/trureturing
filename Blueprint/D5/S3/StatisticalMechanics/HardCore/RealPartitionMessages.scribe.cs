using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class RealPartitionMessagesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real messages and their invariant interval are derived from actual finite-graph partitions.",
        H("Actual real partition messages"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-partition-domain-monotonicity"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.partition_mono"),
                H("Nonnegative domain monotonicity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every independent set in a smaller domain remains independent in the larger domain. Nonnegative configuration weights give the corresponding partition inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-actual-vacancy-ratio"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.vacancyRatio"),
                H("Vacancy as an actual ratio"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Divide the partition after root erasure by the partition of the original finite domain."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-actual-vacancy-bounds"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.vacancy_bounds"),
                H("Derived invariant real interval"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonnegative activities and an upper budget on the root activity imply the interval from one divided by one plus the budget to one. Partition positivity is derived from the empty configuration. An absent root has ratio one and is included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-actual-real-ordered-vacancy"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.real_ordered_vacancy"),
                H("The actual reciprocal recursion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The vacancy ratio equals the reciprocal of one plus the root activity times the ordered product of actual child vacancy ratios. Nonzero intermediate partitions follow from nonnegative activities, rather than being supplied as message hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-actual-real-255-message-box"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.real_255_message_box"),
                H("The exact box at activity 2.55"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite graph domain and every activity between zero and 51/20, every actual vacancy ratio lies in [20/71,1]. This is the input box of the existing affine-message certificate. Its geometric type assignment and complex extension remain separate obligations."))), DescribeRole.Theorem),
            Paragraph(Text("Real positivity alone is not a complex zero-free theorem. The source scripts have undergone mathematical review and finite exact regressions; Lean elaboration and Scribe emission have not been executed here.")))));
}
