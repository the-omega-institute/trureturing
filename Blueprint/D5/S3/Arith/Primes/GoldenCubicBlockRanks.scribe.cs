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
                    + "r = 3^(j+1) identifies the valuation.")),
                Paragraph(
                    Text("The following depth and reciprocity consequences use "),
                    Ref("D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_block_interlevel"),
                    Text(", "),
                    Ref("D5/S3/Arith/Primes/GoldenCubicBlockNativePowerPeriods.cubic_block_native_power_periods"),
                    Text(", "),
                    Ref("D5/S3/Arith/GoldenApparition.fibonacci_apparition_entry_point"),
                    Text(", and "),
                    Ref("D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation.fibonacci_original_rank_valuation"),
                    Text(" together with the exact Lucas-block rank.")),
                Paragraph(Text("Let B_n = L_(3^n)^2 + 3 for n >= 1, where L is the golden Lucas sequence. These blocks are positive, so their natural absolute values are the same positive integers. For every prime p in an actual block support, put N_p = p - (5/p), with the Legendre symbol's prime denominator p, and h_p = v_p(F_(N_p)). These depths are fixed by the original Fibonacci index before either support is chosen.")),
                Paragraph(Text("The Lucas-block rank theorem gives rho(p) = 2 times 3^(n+1), (5/p) = 1, and v_p(B_n) = v_p(F_(rho(p))). The block residues exclude p = 2, 3 and 5. The apparition theorem gives p dividing F_(p-1), so rho(p) divides p-1 and p is one modulo three. Since p does not divide p-1, the original-rank valuation theorem identifies v_p(F_(p-1)) with v_p(F_(rho(p))). Consequently N_p = p-1 and v_p(B_n) = h_p on every actual support, and the exact factorization is B_n = product over p dividing B_n of p^(h_p). This argument applies to both blocks in each pair.")),
                Paragraph(Text("Fix arbitrary 1 <= i < j. The native-power-period result supplies coprimality of B_i and B_j, and the interlevel congruence gives B_j = 3 modulo B_i. Each block is three modulo four and one modulo three. Jacobi reciprocity with three therefore gives (3/B_i) = -1, because (B_i/3) = 1. Reducing the numerator modulo B_i yields (B_j/B_i) = -1. Reciprocity between the two blocks, both three modulo four, gives the opposite directed value (B_i/B_j) = +1.")),
                Paragraph(Text("For every individual prime p dividing B_i, reduction modulo p gives (B_j/p) = (3/p). As p is one modulo three, reciprocity with three gives (3/p) = (-1)^((p-1)/2). Expanding the actual factorization of B_j therefore proves product over q dividing B_j of (q/p)^(h_q) = (3/p) = (-1)^((p-1)/2). Reciprocity between p and the whole odd block B_j contributes the same sign (-1)^((p-1)/2), since B_j is three modulo four. It cancels the preceding value, giving (p/B_j) = 1. Expanding the denominator factorization gives product over q dividing B_j of (p/q)^(h_q) = 1 for every such p.")),
                Paragraph(Text("For p dividing B_i and q dividing B_j, coprimality makes the primes distinct and the Legendre symbols nonzero. Let epsilon(q,p) be zero when (q/p) = +1 and one when (q/p) = -1. Thus (q/p) = (-1)^(epsilon(q,p)). Expanding (B_j/B_i) through both actual factorizations gives (-1) raised to the sum over p dividing B_i and q dividing B_j of h_p h_q epsilon(q,p). Its value is -1, so that exact double sum is odd.")),
                Paragraph(Text("These are consequences of the block congruences, exact ranks, original valuations, coprimality and classical Jacobi laws. A Jacobi value +1 with composite denominator does not assert that the numerator is a square. The identities constrain depth parity and do not force an initial depth to equal one."))),
                DescribeRole.Theorem))));
}
