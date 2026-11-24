using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot;

internal sealed class PrimitiveRootSieveThresholdExactDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PrimitiveRoot/SieveThresholdExact.";
    private static readonly LibraryNoteRef McGown =
        LibraryNoteRef.Create("D5/L/ArithUnits/mcgown2016grosswald");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact arithmetic threshold for the coarse character sieve",
        H("The exact arithmetic threshold for the coarse character sieve"), Blocks(
            Describe.Lean(DescribeId.Create("feasible-ne-exceptions"),
                DeclarationHandle.Create(
                    Prefix + "feasible_ne_exceptions"),
                H("Unconditional necessary exclusions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every natural x, feasibility implies x≠3483481 and x≠3573571. "
                    + "No lower threshold or primality assumption is required. At either "
                    + "exception the full support and the covering condition force a coefficient "
                    + "greater than 42 times the positive density, contradicting the strict "
                    + "margin."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primitive-root-sieve-threshold-exact"),
                DeclarationHandle.Create(Prefix + "feasible_iff"),
                H("Exact feasibility and the two exceptions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "For every integer x at least 3483481, Feasible(x) holds if and only if " +
                    "x differs from both 3483481 and 3573571. Feasibility uses precisely " +
                    "the signed coefficient K, the bound (3/2)sqrt(x)log(x), and the " +
                    "main term x/2-sqrt(x). There is no primality or GRH assumption.")),
                Paragraph(Text(
                    "An ordered prime-support split covers the unbounded tail. Below it, " +
                    "seven-prime supports with large reciprocal mass have ten possible " +
                    "radicals. Divisibility leaves eight integers, including one exception; " +
                    "the other seven satisfy exact rational margin certificates. " +
                    "For each exception, the cover forces the sieve set to be the " +
                    "difference of the full prime support and the gcd support. " +
                    "Every subset of that seven-element support has K greater than " +
                    "42 times its positive margin, which contradicts the signed estimate.")),
                Paragraph(Text(
                    "This is an arithmetic classification of the sieve criterion. The " +
                    "analytic character-sum estimates remain hypotheses of its application " +
                    "to primitive roots."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("threshold-prime-primitive-root"),
                DeclarationHandle.Create(Prefix + "exists_prime_primitiveRoot"),
                H("From coarse analytic estimates to a prime primitive root"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "Let p be prime and at least 3483482. Assume the real part of the " +
                    "principal smoothed character sum is at least p/2-sqrt(p). For each " +
                    "nonprincipal character whose order divides the product of the distinct " +
                    "prime factors of p-1, assume the absolute real part is at most " +
                    "(3/2)sqrt(p)log(p). Then there is a prime q less than p with " +
                    "order p-1 modulo p.")),
                Paragraph(Text(
                    "The exact feasibility theorem supplies sieve parameters. Replacing e " +
                    "by gcd(e,p-1) preserves the sieve primes and restricts every character " +
                    "order used by the signed sieve to a divisor of the radical of p-1. " +
                    "The signed error coefficient is nonnegative and the density margin " +
                    "is positive, so the coarse bounds replace both sides in the required " +
                    "directions. No unconditional character-sum estimate is asserted."))),
                DescribeRole.Theorem))));
}
