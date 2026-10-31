using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class PrimeValuation5040BridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PrimeValuation5040Bridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The 5040 block is the exact simultaneous valuation fibre at the four active primes.",
        H("The 5040 Prime-Valuation Fibre"),
        Blocks(
            Paragraph(Text(
                "This finite arithmetic bridge extracts the canonical prime-power block "
                + "from a nonzero natural number. The residual factor is coprime to the "
                + "external unit modulus and to 210=2*3*5*7, so the four valuations are "
                + "exactly the profile (4,2,1,1). The proof uses the repository's finite "
                + "prime-power product and the existing 5040 support; it makes no analytic "
                + "claim about RH.")),
            Describe.Lean(
                DescribeId.Create("prime-valuation-5040-joint-fibre"),
                DeclarationHandle.Create(Prefix + "jointFiber5040_mul_iff"),
                H("Exact residual characterization of the 5040 fibre"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every external modulus W coprime to 2,3,5,7 and every natural n, "
                        + "the simultaneous factorization fibre of 5040*n is equivalent to "
                        + "n being nonzero and coprime to W*210.")),
                    Paragraph(Text(
                        "The forward direction extracts nonzeroness and the four zero residual "
                        + "valuations. The reverse direction uses multiplicativity of natural "
                        + "factorization, the imported prime-power product, and coprimality "
                        + "to the active support. This is the finite bridge consumed by Robin "
                        + "records; analytic inequalities and the RH implication remain outside "
                        + "this declaration.")),
                    Paragraph(Text(
                        "For a finite set S of primes and an exponent map a, write P for the "
                        + "prime-power product over S. If jointFiber S a W n holds, then n is "
                        + "nonzero, coprime to W, and has factorization a(p) at every p in S. "
                        + "The existing primeBlock_pos and primeBlock_factorization results "
                        + "give P > 0 and factorization(P)(p) = a(p) on S, zero off S. "
                        + "Thus factorization(P)(p) <= factorization(n)(p) for every prime p: "
                        + "use the fibre equality on S and nonnegativity off S. Applying "
                        + "Nat.factorization_le_iff_dvd gives P dividing n.")),
                    Paragraph(Text(
                        "Specialize S to primes5040 = {2,3,5,7} and a to profile5040, whose "
                        + "exponents are (4,2,1,1). The existing primePowerProduct_5040 identity "
                        + "identifies P with 5040, so jointFiber primes5040 profile5040 W n "
                        + "implies 5040 divides n. These divisibility applications require no "
                        + "additional coprimality between W and the primes in S; that hypothesis "
                        + "belongs to the multiplicative residual characterization above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-valuation-5040-factorization-profile"),
                DeclarationHandle.Create(Prefix + "profile5040_eq_factorization"),
                H("The profile is the factorization of 5040"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The imported target exponent profile agrees pointwise with the natural "
                    + "factorization of 5040, giving exponents 4,2,1,1 on 2,3,5,7 and zero "
                    + "elsewhere."))),
                DescribeRole.Lemma))));
}
