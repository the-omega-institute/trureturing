using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.AllSupport;

internal sealed class RobinLargeHeightMarginDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-support Robin estimate gives a uniform quantitative margin under RH.",
        H("A quantitative Robin margin at large logarithmic height"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("robin-large-height-margin"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/AllSupport/RobinLargeHeightMargin.normalized_robinLogMargin_large_gt"),
                H("Uniform normalized Robin margin above height 74500"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under RH, let H = log n be at least 74500. The log Robin margin "
                    + "times sqrt(H) log(H) strictly exceeds 17/500. The weighted prime "
                    + "cost contributes at least 2264003/1000000, and the adverse "
                    + "signed theta tail costs strictly less than 223/100. "
                    + "The remaining terms in the all-support identity are nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("robin-all-support-forward"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/AllSupport/RobinLargeHeightMargin.original_robin_of_rh_all_support"),
                H("The original Robin inequality under RH"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite certificates cover n greater than 5040 through log "
                    + "height 74500. The quantitative margin covers every larger height."))),
                DescribeRole.Theorem))));
}
