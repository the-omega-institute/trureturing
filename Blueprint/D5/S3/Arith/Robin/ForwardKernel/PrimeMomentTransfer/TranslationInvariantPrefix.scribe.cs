using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class TranslationInvariantPrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TranslationInvariantPrefix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prefix rectangles of a symmetric translation-invariant kernel are determined by three square sums.",
        H("Translation-invariant prefix identity"),
        Blocks(
            Describe.Lean(DescribeId.Create("kernel-rect-sum"), DeclarationHandle.Create(Prefix + "kernelRectSum"), H("Rectangle prefix sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Sum the kernel over the integer prefixes from one to m and from one to n."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kernel-square-sum"), DeclarationHandle.Create(Prefix + "kernelSquareSum"), H("Square prefix sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Sum the kernel over the square of the integer prefix from one to m."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prefix-identity"), DeclarationHandle.Create(Prefix + "prefix_identity"), H("Rectangle prefix identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For a symmetric translation-invariant kernel, the rectangle prefix sum equals one half of the sum of the two corresponding square prefix sums minus the square prefix sum at the distance between their lengths."))), DescribeRole.Theorem))));
}
