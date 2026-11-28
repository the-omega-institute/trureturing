using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.AllSupport;

internal sealed class RobinFourfoldBlockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An eventual lower bound on a finite Robin block characterizes RH.",
        H("Fourfold intervals for the weighted Robin tail"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("robin-fourfold-block-abel"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/AllSupport/RobinFourfoldBlock.finite_robin_block_identity"),
                H("Abel summation on a fourfold interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The drop in the weighted Chebyshev theta tail between x and 4x "
                    + "equals the prime reciprocal sum over the right-closed interval "
                    + "with two Chebyshev boundary terms and an explicit smooth correction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("robin-fourfold-block-rh"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/AllSupport/RobinFourfoldBlock.rh_iff_eventual_integer_fourfold_robin_block"),
                H("RH and a finite prime-reciprocal inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "RH implies that the normalized block is eventually at least minus "
                    + "eleven tenths. Conversely, summing the block lower bound along the "
                    + "scales n, 4n, 16n and onward controls the full weighted tail. "
                    + "A unit-interval estimate transfers this control from integer endpoints "
                    + "to real endpoints for the weighted-tail converse."))),
                DescribeRole.Theorem))));
}
