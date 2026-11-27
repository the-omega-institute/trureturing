using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class CompactFactorialGcdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/CompactFactorialGcd.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-sided divisibility bound for the gcd of a one-parameter factorial family.",
        H("The compact factorial gcd"),
        Blocks(
            Paragraph(Text(
                "An Alpoge-inspired rank-one window calculation motivates the comparison. "
                + "The proof uses a GPT Pro derivation and an independent derivation of the "
                + "integer bound with budget (2r^2)!.")),
            Describe.Lean(
                DescribeId.Create("selberg-factorial"),
                DeclarationHandle.Create(Prefix + "selbergFactorial"),
                H("Factorial product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural r, s and b with rb at most s, take the product over "
                    + "j=1,...,r of (jb)! divided by b!, times (s-(r-j)b)!. "
                    + "Each division by b! is exact."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("selberg-gcd"),
                DeclarationHandle.Create(Prefix + "selbergGcd"),
                H("Gcd of the factorial products"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The gcd of the factorial products over 0<=b<=floor(s/r). "
                    + "The parameter zero supplies the product (s!)^r."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("compact-factorial-gcd"),
                DeclarationHandle.Create(Prefix + "compact_factorial_gcd"),
                H("Exact two-sided divisibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every pair of natural numbers r and s with r>=2 and s<r^2, "
                        + "tailLCM(rs+r-1,r-1) divides selbergGcd(r,s), and selbergGcd(r,s) "
                        + "divides tailLCM(rs+r-1,r-1) times (2r^2)!. The tail product "
                        + "multiplies the prefix LCM at floor((rs+r-1)/k) over "
                        + "r-1<k<=rs+r-1.")),
                    Paragraph(Text(
                        "At each prime power, a count of marked residues in consecutive blocks "
                        + "bounds the paired factorial floors below by the corresponding tail "
                        + "count. Summing via Legendre's formula proves the lower divisibility "
                        + "for every b. For a prime p<=r the parameter b=0 bounds the excess "
                        + "by (r-1) times the number of positive powers of p at most s. "
                        + "For r<p<=s the parameter b=floor(p/r) bounds the excess using "
                        + "only the first power of p. In both cases the bound is at most "
                        + "floor(2r^2/p). Primes above s contribute zero to the gcd.")),
                    Paragraph(Text(
                        "At s=0 both the tail and gcd equal one. When r=3 and s=8, "
                        + "the tail product is 41803776000 and the gcd is 83607552000, "
                        + "so the quotient equals two."))),
                DescribeRole.Theorem))));
}
