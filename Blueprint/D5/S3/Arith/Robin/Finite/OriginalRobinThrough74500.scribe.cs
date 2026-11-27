using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Finite;

internal sealed class OriginalRobinThrough74500Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Robin inequality through logarithmic height 74500.",
        H("Robin inequality through log height 74500"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("robin-through-74500"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/Finite/OriginalRobinThrough74500.original_robin_through_74500"),
                H("Unconditional finite Robin inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural n greater than 5040 with log n at most 74500, "
                    + "sigma(n) is strictly below exp(gamma) times n times log(log(n)). "
                    + "Exact rational checks certify the original row prices, prime-power "
                    + "products and both ends of each interval. The adjacent certified "
                    + "intervals cover the full range."))),
                DescribeRole.Theorem))));
}
