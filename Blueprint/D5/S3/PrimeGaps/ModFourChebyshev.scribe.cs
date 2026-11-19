using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeGaps;

internal sealed class ModFourChebyshevDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/PrimeGaps/ModFourChebyshev.";
    private static readonly LibraryNoteRef Apostol =
        LibraryNoteRef.Create("D5/L/apostol1976introduction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primes congruent to one modulo four supply the Euler-form denominator.",
        H("A classical Chebyshev lower bound in one residue class"),
        Blocks(
            Describe.Lean(DescribeId.Create("prime-count"),
                DeclarationHandle.Create(Prefix + "primeCount"),
                H("Counting primes in the residue class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The count includes the primes p with "
                    + "1 <= p <= floor(x) and p congruent to one modulo four."))),
                DescribeRole.Definition),
            Describe.Remark(DescribeId.Create("classical-weighted-mertens"),
                DeclarationHandle.Create(Prefix + "prime_count_lower"),
                H("The classical weighted Mertens estimate"),
                AssessedProvenance.FromLiterature(Apostol),
                Blocks(Paragraph(Text("Apostol, Introduction to Analytic Number Theory, "
                    + "Chapter 7, Theorem 7.3 (p. 148), states that for k > 0 and "
                    + "gcd(h,k) = 1, the sum of log(p)/p over primes p <= x with "
                    + "p congruent to h modulo k is log(x)/phi(k) + O(1). "
                    + "The case k = 4, h = 1 gives half log(x) + O(1). "
                    + "This attribution concerns the classical statement; the constant "
                    + "twelve and the prime-count lower bound below are repo-derived.")))),
            Describe.Lean(DescribeId.Create("prime-count-lower"),
                DeclarationHandle.Create(Prefix + "prime_count_lower"),
                H("A lower bound for every sufficiently large threshold"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Apostol),
                Blocks(
                    Paragraph(Text("The ordinary weighted Mertens estimate and the bounded "
                        + "character-weighted Mangoldt sum give a modulus-four weighted "
                        + "prime sum within twelve of half log(x). The prime-power "
                        + "correction is bounded by the existing convergent correction "
                        + "series. The explicit error constant twelve is a "
                        + "repo-derived quantitative form of the classical estimate.")),
                    Paragraph(Text("Apply the weighted estimate at x and at x/exp(50). "
                        + "For x at least exp(50), their difference is at least one. "
                        + "Every prime in the resulting fixed-ratio window is greater "
                        + "than x/exp(50), and log(p) is at most log(x). Hence the count "
                        + "is at least exp(-50)*x/log(x) for every such x. The threshold "
                        + "exp(50) and this fixed-ratio window deduction are "
                        + "repo-derived explicit quantitative choices."))),
                DescribeRole.Theorem))));
}
