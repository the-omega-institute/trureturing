using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class SquareGridRootMessagesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact correspondence between grid geometry and actual independent-set messages.",
        H("SquareGridRootMessages"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hc-squaregridrootmessages-rootframe"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.rootFrame"),
                H("The exact existing root frame"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This equivalence realizes the coordinate map already inside rootDomain. Its agreement with the original domain is proved, without accessing private names."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hc-squaregridrootmessages-root-frame-adj-iff"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_frame_adj_iff"),
                H("All four frames preserve grid edges"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Adjacency is preserved and reflected by every root coordinate map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridrootmessages-rootearlier"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.rootEarlier"),
                H("The ordered root prefix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This lists exactly those neighbors that precede the selected first child."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hc-squaregridrootmessages-root-child-vacancy"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_child_vacancy"),
                H("The actual first-child factor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The marked vacancy on the original rootDomain equals its successive unrotated neighbor ratio."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridrootmessages-root-partition-recursion"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_partition_recursion"),
                H("The genuine four-child root formula"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This uses proper-domain nonvanishing, without assuming the root partition is nonzero or applying a three-child contraction bound to the root."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridrootmessages-root-child-context"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridRootMessages.root_child_context"),
                H("Initialize the certified geometric type"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every present first child contains its new root, is compatible with the existing type-zero mask, and has fewer vertices than the original graph domain."))),
                DescribeRole.Theorem))));
}
