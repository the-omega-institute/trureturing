using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class PrimeReciprocalProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/PrimeReciprocalProduct.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform reciprocal estimates for finite prime supports",
        H("Harmonic sums and reciprocal prime products"),
        Blocks(
            Paragraph(Text(
                "Write P(m) for the product of 1+1/p over all primes p at most m, "
                + "and H(m) for the sum of 1/k over integers k from one to m. "
                + "The bounds below are symbolic and uniform. They use exact rational "
                + "arithmetic; no floating-point approximation or bounded search is involved.")),
            Node("harmonic_lt_twice_prime_product", "Harmonic lower bound for the product",
                "For every positive natural number m, H(m)<2P(m). Mathlib's "
                + "exists_sq_mul_squarefree writes k=a^2 b with b squarefree. "
                + "This gives an injection from the integers one through m into pairs "
                + "consisting of a between one and m and a divisor b of the primorial of m. "
                + "The rectangular reciprocal sum factors into the finite inverse-square "
                + "sum and P(m). The reciprocal divisor identity follows from Mathlib's "
                + "sum_divisors_filter_squarefree and prod_add_one. Mathlib's "
                + "sum_Ioc_inv_sq_le_sub bounds the inverse-square sum by 2-1/m, "
                + "which is strictly below two."),
            Node("prime_support_product_sq_le", "Support-size upper bound",
                "For every nonempty finite set F of primes, the square of the product "
                + "of 1+1/p over F is at most (9/4) times the cardinality of F. "
                + "For a set of r distinct odd integers at least three, induction on the "
                + "largest element q bounds the product squared by r+1. The map p to "
                + "p/2 injects all preceding odd elements into an interval, giving "
                + "q at least 2r+3 for the induction step. The prime two contributes "
                + "a factor whose square is 9/4; if two is absent, nonemptiness "
                + "absorbs the extra additive one in the odd-support estimate."),
            Paragraph(Text(
                "These estimates supply analytic ingredients for comparing divisor sums "
                + "when n divided by its radical is below the least missing prime. "
                + "They alone do not establish that divisor-sum implication: the formulas "
                + "for the actual unitary and squarefree divisor sums, the mandatory "
                + "prime-support reduction, the remaining growth estimate and the "
                + "finite residual certificate must also be connected in Lean.")))));

    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(
            DescribeId.Create("prime-reciprocal-product-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
