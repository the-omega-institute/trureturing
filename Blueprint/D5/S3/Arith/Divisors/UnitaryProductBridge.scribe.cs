using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class UnitaryProductBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/UnitaryProductBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-power choices connect actual divisor sums with reciprocal prime products.",
        H("Unitary divisors and mandatory prime support"),
        Blocks(
            Paragraph(Text(
                "For a positive integer N, let U(N) sum its positive unitary divisors "
                + "and let S(N) sum its positive squarefree divisors. Both sums include one. "
                + "Write rad(N) for the product of distinct prime divisors and m=N/rad(N). "
                + "All quotients below have positive denominators and are exact rationals.")),
            Node("prime_power_product_unitary", "Unitary products of complete prime powers",
                "For every nonzero natural N and every finite subset F of its prime "
                + "support, the product of p^v_p(N) over p in F is a divisor of N "
                + "coprime to its complementary quotient. Thus complete prime-power "
                + "selection yields an actual unitary divisor; if N is squarefree, "
                + "the selected product is simply the product of the primes in F."),
            Node("unitarySum_eq_product", "Complete prime-power choices",
                "For every nonzero natural N, U(N) is the product of p^v_p(N)+1 over "
                + "the distinct prime divisors p of N. A subset of prime support chooses "
                + "the complete prime power p^v_p(N) for each included prime. Its product "
                + "divides N and is coprime to the complementary product. Its prime support "
                + "is exactly the chosen subset, so distinct subsets yield distinct unitary "
                + "divisors. Expanding the product supplies the lower bound, while the "
                + "existing unitarySum_le_product supplies the upper bound."),
            Node("mandatory_support_lower", "The joint support bound",
                "Assume every prime p at most m divides N. Let A be the product of "
                + "1+1/p over primes p at most m which do not divide m, and let P be "
                + "the product over all primes at most m. Then A+P/m is at most "
                + "U(N)/N+S(N)/N. Any prime in N but absent from m occurs to exponent "
                + "one in N. Such primes therefore contribute their full reciprocal "
                + "factor to U(N)/N; every omitted factor is at least one. The exact "
                + "squarefree divisor identity gives S(N)/N as the reciprocal product "
                + "over all prime divisors, divided by m. Keeping only the mandatory "
                + "support gives the second lower bound."),
            Node("mandatory_product_lower", "Keeping repeated-prime contributions",
                "Under the same mandatory-support hypothesis, replace A by the product "
                + "of 1+1/p^(v_p(m)+1) over all primes p at most m. The resulting sum "
                + "with P/m is still at most U(N)/N+S(N)/N. For every prime divisor of N, "
                + "its exponent in N is exactly one more than its exponent in m. "
                + "This preserves the extra contribution of repeated primes, which "
                + "the coarser support-only bound discards."),
            Node("unitary_squarefree_ge_twice_of_support", "The joint divisor-sum inequality",
                "For every positive integer N, if every prime at most m=N/rad(N) "
                + "divides N, then U(N)+S(N) is at least 2N. For m at least one "
                + "thousand, the support-only product is at least two. For the "
                + "remaining positive m, the product retaining repeated-prime "
                + "contributions plus P/m is at least two by exact rational "
                + "calculation in ten consumed private kernel certificates covering "
                + "one through 999. These two ranges cover every positive m."))));

    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(
            DescribeId.Create("unitary-product-bridge-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
