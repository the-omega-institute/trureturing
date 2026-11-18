using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class RobinExceptionCountDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef KappaSource =
        LibraryNoteRef.Create("D5/L/ArithSums/fankobayashimolnar2025family");
    private static readonly LibraryNoteRef RobinSource =
        LibraryNoteRef.Create("D5/L/Analytic/lucapomerancesole2025robin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary Robin exceptions and the real-power Robin exceptions uniformly above a fixed positive parameter gap have upper count exp((C0+epsilon)*log(x)/log(log(x))).",
        H("Sharp upper counts for Robin exceptions"),
        Blocks(
            Describe.Lean(DescribeId.Create("kappa-source"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.sigmaKappa"),
                H("The real-power divisor transform"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(KappaSource),
                Blocks(Paragraph(Text("The transform sigmaKappa(kappa,n) is the divisor sum of mu(n/d)*sigma(d)^kappa. The real-power Robin inequality uses the real part of zeta(kappa) times this transform and compares it with (exp(gamma)*n*log(log(n)))^kappa. Fan, Kobayashi and Molnar suggest considering real-power analogues of the Robin exception-count results in Section 8."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("counting-source"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTailUpper.tailCount"),
                H("The large distinct-prime tail"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(RobinSource),
                Blocks(Paragraph(Text("The function tailCount(lambda,x) counts positive integers up to x whose number of distinct prime factors exceeds log(x)/log(log(x))+lambda*log(x)/(log(log(x)))^2. The cited correction connects Robin exceptions with the distinct-prime tail at lambda=0 and supplies the necessary-condition motivation for this statistic. The second-order threshold, optimized constant C0 and sharp tail rate are repository-derived results, reused in the two conclusions below."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kappa-count"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/RobinExceptionCount.kappa_exception_count"),
                H("Uniform real-power Robin exception bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every delta>0 and epsilon>0, the number of natural n with 2162160<n<=x for which some real kappa>=1+delta satisfies zeta(kappa)*sigmaKappa(kappa,n)>=(exp(gamma)*n*log(log(n)))^kappa is eventually at most exp((C0+epsilon)*log(x)/log(log(x))). The quantifier over kappa is inside the exceptional predicate, so one common eventual bound covers the entire unbounded parameter range. Prime-power factor bounds and ordered prime-factor replacement compare the normalized transform with the initial prime product and a uniformly controlled convergent Euler tail. A quantitative Mertens remainder and a second-order prime-counting estimate leave a strict inverse-logarithmic gap below the Robin threshold. The resulting local distinct-prime exclusion transfers to the global count through a finite initial segment and dyadic intervals. This is an unconditional upper bound; it asserts neither existence nor an asymptotic lower count of exceptions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robin-count"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/RobinExceptionCount.robin_exception_count"),
                H("Ordinary Robin exception bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every epsilon>0, the number of natural n with 5040<n<=x and sigma(n)>=exp(gamma)*n*log(log(n)) is eventually at most exp((C0+epsilon)*log(x)/log(log(x))). The ordinary divisor ratio is bounded by the inverse Euler product over its distinct prime factors, and replacing those primes by the first primes gives the same strict Mertens gap used in the real-power argument. The proved local exclusion and the existing sharp distinct-prime tail upper bound supply the global count. Equality belongs to the exceptional set. The theorem does not assert the Robin inequality for every n>5040."))), DescribeRole.Theorem))));
}
