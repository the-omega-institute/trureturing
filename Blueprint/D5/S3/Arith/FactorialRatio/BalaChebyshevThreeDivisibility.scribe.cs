using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class BalaChebyshevThreeDivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala's 3n+1 integrality clause reduces to positive local defects with two exceptional primes.",
        H("Chebyshev Factorial Ratio Divisibility by 3n+1"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bala-a211417-three-integrality"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FactorialRatio/BalaChebyshevThreeDivisibility.bala_three_integrality"),
                H("An unbounded factorial divisibility statement"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A(n)=(30n)!n!/((15n)!(10n)!(6n)!). The source proves that "
                        + "(3n+1)(15n)!(10n)!(6n)! divides (30n)!n! for every natural n, "
                        + "including zero. This is precisely the A(n)/(3n+1) integrality "
                        + "clause posed by Peter Bala on OEIS A211417 on 28 August 2025, "
                        + "not the separately settled (30n-1) clause.")),
                    Paragraph(Text(
                        "Legendre's formula writes each factorial valuation difference as "
                        + "a sum of nonnegative floor defects. If a modulus q divides 3n+1 "
                        + "and q is 7 or at least 10, its defect is exactly one. This covers "
                        + "all relevant prime powers except powers of 2 and 5; the prime 3 "
                        + "never divides 3n+1. At 2 the full defect sum is the valuation of "
                        + "binomial(8n,3n), and at 5 it is that of binomial(5n,3n). "
                        + "The identity (3n+1)binomial(mn,3n+1)=(m-3)n binomial(mn,3n), "
                        + "with m=8 or 5, supplies the missing valuation in both cases. "
                        + "All required factorial and binomial factors are nonzero.")),
                    Paragraph(Text(
                        "The inspected OEIS mirror version 94 still listed this clause as "
                        + "a conjecture; the linked AlphaProof file proves a different "
                        + "denominator. The proof is new to this submission, but exhaustive "
                        + "literature priority and Lean kernel acceptance are not asserted. "
                        + "The known E8 Weyl monodromy of this factorial ratio is motivation, "
                        + "not a Monster action assumed or proved by this theorem."))),
                DescribeRole.Theorem))));
}
