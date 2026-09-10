using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class SquareGridMessagesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact correspondence between grid geometry and actual independent-set messages.",
        H("SquareGridMessages"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hc-squaregridmessages-grid-vacancy-product-telescopes"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridMessages.grid_vacancy_product_telescopes"),
                H("Exact ordered vacancy quotient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Only smaller-domain partitions are required nonzero before telescoping. The same statement serves both the three-child internal node and the four-child unconditioned root."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridmessages-neighbororder"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridMessages.neighborOrder"),
                H("The six existing geometric orders"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The list representation is checked against every entry of the existing position and deleted tables."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hc-squaregridmessages-childvacancy"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridMessages.childVacancy"),
                H("Actual recentered child partitions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each child is evaluated on the existing advance domain, with its marked vertex at the origin."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hc-squaregridmessages-child-vacancy-before"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridMessages.child_vacancy_before"),
                H("Identify the successive unrotated child"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact grid relabeling transports the actual child ratio before any growth or analytic estimate is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridmessages-ordered-product-children"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridMessages.ordered_product_children"),
                H("Preserve the whole ordered product"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All intermediate domains, direction multiplicities and actual field ratios are retained. This algebraic identity itself remains valid with total division at zeros."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridmessages-grid-partition-recursion"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridMessages.grid_partition_recursion"),
                H("Noncircular field recursion on actual grid domains"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonzero hypotheses are confined to subsets after removing the root. The target partition is not assumed nonzero. All three factors are the actual recentered child ratios."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridmessages-grid-real-recursion"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridMessages.grid_real_recursion"),
                H("Actual real parent recursion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonnegative independent-set weights derive every denominator condition from the empty configuration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridmessages-child-vacancy-absent"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridMessages.child_vacancy_absent"),
                H("Absent vertices give neutral messages"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Identical positive numerator and denominator give one for a missing actual neighbor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridmessages-availabledirections"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridMessages.availableDirections"),
                H("Actual finite-domain pruning"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Availability is determined by vertex membership in the actual domain, not by an arbitrary finite-table label."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hc-squaregridmessages-typed-child-context"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridMessages.typed_child_context"),
                H("Discharge the actual child type assignment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing complete geometric certificate supplies a successor type for each present child. Its actual domain contains the new root, is compatible with its blockers, and has fewer vertices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridmessages-actual-grid-affine-contraction"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridMessages.actual_grid_affine_contraction"),
                H("Consume the affine certificate on actual graph ratios"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proof derives the reciprocal recursion, child interval bounds and neutral values for absent children. It then invokes the existing all-pruning certificate on the actual graph parent and child ratios."))),
                DescribeRole.Theorem))));
}
