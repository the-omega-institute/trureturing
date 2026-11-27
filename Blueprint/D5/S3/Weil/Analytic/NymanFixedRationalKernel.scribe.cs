using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class NymanFixedRationalKernelDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Analytic/NymanFixedRationalKernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit rational cubic kernel",
        H("The explicit rational cubic kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("b-rat"),
                DeclarationHandle.Create(Owner + ".bRat"),
                H("Exact rational evaluation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a = 7/6, take the five coefficients of (1 − z)(1 − az)(1 − a²z)(1 − a³z) in increasing degree order. The rational kernel is one sixth of the sum of each coefficient times the cube of max(u/aʲ − 1, 0) for j from zero to four."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("b-rat-cast"),
                DeclarationHandle.Create(Owner + ".bRat_cast"),
                H("Agreement with the real kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Casting the rational evaluation to the reals gives the real cubic kernel at the same rational input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("b-zero-off"),
                DeclarationHandle.Create(Owner + ".b_zero_off"),
                H("Support inside the first shell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All positive parts vanish at or below 1. At or above a⁴ the untruncated cubic terms cancel, and a⁴ < 2. Thus the kernel vanishes outside the open interval (1, 2)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coefficient-product"),
                DeclarationHandle.Create(Owner + ".coefficient_product"),
                H("The four difference factors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient polynomial factors into the four linear factors of the dilation difference."))),
                DescribeRole.Theorem))));
}
