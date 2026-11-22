using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicMarkedFibonacciDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single marked root of a later golden Lucas cubic reads the earlier native Fibonacci prime-power depth.",
        H("Marked golden cubic roots and Fibonacci depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-marked-residue"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicMarkedFibonacciDepth.fibonacci_marked_residue"),
                H("Every marked residue reads the Fibonacci entry depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let p be a prime greater than three dividing the block L_(3^i)^2 + 3, with i positive, and use the actual Lucas parameter x = L_(3^j) for any j greater than i. Modulo every positive power of p, the cubic T^3 - 3(x^2 + 3)T + 2(x^2 + 3)x has exactly one root above each marked seed 0, 3, and -3 modulo p.")),
                    Paragraph(Text("The marked root equals its seed modulo that entire power of p if and only if the same power divides F_(6 times 3^i). The proof uses classical finite simple-root Hensel lifting, unit divided differences, the existing golden cubic recurrence, and the Fibonacci doubling and tripling identities. The result is the link from marked cubic residues to the native Fibonacci depth, not a new Hensel theorem or Fibonacci rank law. The earlier block and Fibonacci entry valuation equality is already present in GoldenCubicBlockRanks.cubic_block_b_prime_rank.")),
                    Paragraph(Text("The theorem is uniform in finite precision and retains the earlier same-prime divisor hypothesis. It does not assert an identification with F_(p-1), rule out depth two, settle Wall-Sun-Sun, or invoke GRH."))),
                DescribeRole.Theorem))));
}
