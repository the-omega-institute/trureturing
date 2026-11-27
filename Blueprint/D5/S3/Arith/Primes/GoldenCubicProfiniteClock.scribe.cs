using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicProfiniteClockDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/Primes/GoldenCubicProfiniteClock";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native cubic Lucas trajectory realizes every compatible absolute-time clock.",
        H("The profinite cubic Lucas clock"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-profinite-clock"),
                DeclarationHandle.Create(Module + ".nativeClock"),
                H("All compatible eventual states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact native periods are cofinal among all positive time moduli. "
                    + "The resulting clock labels the entire eventual inverse-limit family."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-cubic-profinite-native-step"),
                DeclarationHandle.Create(Module + ".nativeClock_next"),
                H("The cubic update advances time by one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Addition by one agrees at every observation modulus with the original cubic polynomial."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-profinite-isolated-finite-block"),
                DeclarationHandle.Create(Module + ".finite_block_not_eventual"),
                H("Finite blocks are not eventual clock points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each finite block has a three-adic observation separating it from every compatible eventual family."))),
                DescribeRole.Theorem))));
}
