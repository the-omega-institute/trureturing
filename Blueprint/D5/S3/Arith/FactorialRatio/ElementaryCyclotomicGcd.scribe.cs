using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class ElementaryCyclotomicGcdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact prime-power carry factorization of a product of prefix least common multiples.",
        H("Cyclotomic carry products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("row-carry-product"),
                DeclarationHandle.Create(Prefix + "QStar"),
                H("Carry product for one row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiply p once for each positive prime power r = p^t up to 4(N-j)+1 "
                    + "for which the integer quotient floor(4j/r) is odd."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("carry-product"),
                DeclarationHandle.Create(Prefix + "HStar"),
                H("Accumulated carry product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiply the individual carry products over j from zero through N."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exceptional-factor"),
                DeclarationHandle.Create(Prefix + "EStar"),
                H("Exceptional factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The level two contributes 2^N. For each odd prime power r = p^t "
                    + "up to 4N+1, count the nonnegative indices j below N+1-floor((r+2)/4) where r divides "
                    + "j when r is 1 modulo 4, or r divides 4j+1 when r is 3 modulo 4. "
                    + "Each such index contributes a factor p."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("accumulated-lcm-identity"),
                DeclarationHandle.Create(Prefix + "lcmProduct_eq"),
                H("Exact accumulated LCM identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The product of the prefix least common multiples through 4i+1 for "
                        + "i from zero through N equals the product of the central binomial "
                        + "coefficients binom(4i,2i) times the accumulated carry product "
                        + "and the exceptional factor.")),
                    Paragraph(Text(
                        "At level r, shift the binomial index by floor((r+2)/4) to match "
                        + "the range of the truncated carry. The two carries add to one at "
                        + "each odd level outside its exceptional residues and to zero "
                        + "on those residues. The sum is always one at powers of two from "
                        + "four onward. At level two the carries vanish and the prefix least "
                        + "common multiples contribute N occurrences."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exceptional-factor-divisibility"),
                DeclarationHandle.Create(Prefix + "EStar_dvd"),
                H("Divisibility bound for the exceptional factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exceptional factor divides 2^N times the least common multiple "
                    + "through 4N+1 times the product of j(4j+1) over j from one through N. "
                    + "The index zero contributes at most one copy of each prime-power level "
                    + "in the least common multiple. Each positive index contributes only "
                    + "levels dividing j or 4j+1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sampled-chebyshev-comparison"),
                DeclarationHandle.Create(Prefix + "log_HStar_sub_sampled_chebyshev_le"),
                H("Explicit sampled Chebyshev comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The absolute difference between log HStar and the sum of psi(4i+1) "
                    + "over i from zero through N, after subtracting 2 log(2) N(N+1) "
                    + "from the sum, is at most 14 N log(N+2). Take logarithms of the "
                    + "exact identity using the prefix LCM formula for psi. Bounds on the "
                    + "central binomial coefficients and on the divisibility budget bound "
                    + "the two errors."))),
                DescribeRole.Theorem))));
}
