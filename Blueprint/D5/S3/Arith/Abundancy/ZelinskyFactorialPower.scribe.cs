using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class ZelinskyFactorialPowerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/ZelinskyFactorialPower.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/zelinsky2023nondeficient");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Euler product over the prime factors of a factorial power plus one tends to one.",
        H("Zelinsky Conjecture 36"),
        Blocks(
            Describe.Lean(DescribeId.Create("h"),
                DeclarationHandle.Create(Prefix + "H"),
                H("The distinct-prime Euler product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a natural number m, H(m) is the product of "
                    + "p/(p-1) over all distinct prime factors p of m. The empty product "
                    + "is one. This is precisely the function on page three of the source."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The factorial-power limit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("As the natural number n tends to infinity, "
                        + "H((n!)^n+1) tends to one. Every prime factor p of this integer "
                        + "exceeds n. The multiplicative order of n! modulo p is positive "
                        + "and divides both 2n and p-1.")),
                    Paragraph(Text("For any positive e, separate primes using the "
                        + "thresholds n^(1+3e), n^3, and the order threshold n^e. "
                        + "Mertens' reciprocal-prime estimate bounds the first range by "
                        + "log(1+3e) plus a term tending to zero. Small orders place "
                        + "the primes among divisors of (n!)^d-1. The logarithmic budget "
                        + "for distinct prime factors bounds this contribution. Large "
                        + "orders place primes in progressions 1+kd; the harmonic sum "
                        + "bound and the divisor subpower estimate control their total. "
                        + "The final range is controlled by the logarithm of (n!)^n+1. "
                        + "All three remaining bounds tend to zero.")),
                    Paragraph(Text("Letting e approach zero makes the complete "
                        + "reciprocal-prime sum tend to zero. The logarithm of each "
                        + "Euler factor lies between zero and 2/p, so exponentiation "
                        + "gives the stated limit. This proves exactly Conjecture 36. "
                        + "Limits for other exponents or the minus sign are not "
                        + "additional conclusions of this theorem."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zelinsky-2023-conjecture-36"),
                    ResolutionKind.Proved)))));
}
