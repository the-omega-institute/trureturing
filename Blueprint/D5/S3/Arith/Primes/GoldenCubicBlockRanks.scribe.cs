using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicBlockRanksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime factors of the two Lucas cubic blocks have exact first-zero ranks and original depths.",
        H("Golden Cubic Block Ranks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-c-block-rank"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicBlockRanks.cubic_block_c_prime_rank"),
                H("The Fibonacci block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For j at least one, put x = L_(3^j) and C = x^2 + 1. "
                    + "Every prime p dividing C first divides a Fibonacci number "
                    + "at index 3^(j+1), and its valuation in C equals its "
                    + "valuation at that first Fibonacci zero. The identity "
                    + "F_(3^(j+1)) = F_(3^j) C supplies the zero; the Lucas "
                    + "discriminant excludes an earlier zero at 3^j."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-b-block-rank"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicBlockRanks.cubic_block_b_prime_rank"),
                H("The Lucas block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For j at least one, put x = L_(3^j) and B = x^2 + 3. "
                    + "Every prime p dividing B first divides a Fibonacci number "
                    + "at index 2 times 3^(j+1). Five is a quadratic residue "
                    + "modulo p, and the valuation of p in B is its original "
                    + "Fibonacci entry valuation. The Lucas discriminant "
                    + "excludes earlier zeros; F_(2r) = F_r L_r at "
                    + "r = 3^(j+1) identifies the valuation."))),
                DescribeRole.Theorem))));
}
