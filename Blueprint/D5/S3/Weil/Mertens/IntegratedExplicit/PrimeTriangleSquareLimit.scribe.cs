using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PrimeTriangleSquareLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete prime-power correction has an explicit square-root coefficient.",
        H("The prime-power correction of the prime triangle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-triangle-correction-limit"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleSquareLimit.normalized_mangoldtHinge_sub_primeTriangle_tendsto"),
                H("Square-root coefficient of the prime-power contribution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Mangoldt triangle minus the ordinary prime triangle, divided "
                    + "by the square root of its scale, tends to six times the square root "
                    + "of two minus eight. Exact prime-power decomposition isolates the "
                    + "squares. Abel summation and the prime number theorem give their "
                    + "limit. The contribution of higher powers vanishes at this scale."))),
                DescribeRole.Theorem))));
}
