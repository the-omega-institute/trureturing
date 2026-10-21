using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.LocalDold;

internal sealed class TribonacciFourBonacciDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/LocalDold/TribonacciFourBonacci.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Scale/chuysurichay2026fibdold");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The printed Tribonacci and four-Bonacci sequences have empty local-Dold good-prime sets, "
            + "with prime-index violations above every natural bound.",
        H("Tribonacci and four-Bonacci local Dold obstruction"),
        Blocks(
            Paragraph(
                Text("Section 4 of "), Ref("D5/L/Scale/chuysurichay2026fibdold"),
                Text(" observes computationally that the classical tribonacci prefix "
                    + "(1,1,2,4,...) and the printed four-Bonacci prefix (1,1,1,2,5,...) "
                    + "have empty good-prime sets. We interpret these positive-index "
                    + "sequences by summing the preceding three and four terms respectively.")),
            Describe.Lean(
                DescribeId.Create("local-dold-congruence"),
                DeclarationHandle.Create(Prefix + "dold"),
                H("Local Dold divisibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural p and sequence a from the naturals to the naturals, "
                        + "dold(p,a) means: for every positive natural n, the integer n divides "
                        + "the sum over positive divisors d of n of mu(n/d) times "
                        + "p raised to valuation_p(a(d)). The theorem uses prime p and "
                        + "a(d)>0 for every positive d."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-dold-good-primes"),
                DeclarationHandle.Create(Prefix + "goodPrimes"),
                H("Good primes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural sequence a, goodPrimes(a) is the set of natural p "
                        + "such that p is prime and dold(p,a) holds. This is the source's G_D(a)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("literal-four-bonacci"),
                DeclarationHandle.Create(Prefix + "fourBonacci"),
                H("The printed four-Bonacci sequence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "fourBonacci(0)=0 is an unused natural placeholder. The positive initial "
                        + "values are B1=B2=B3=1 and B4=2. For every n>=1, "
                        + "B(n+4)=B(n+3)+B(n+2)+B(n+1)+B(n). Thus the positive sequence is "
                        + "(1,1,1,2,5,9,17,33,...). It is strictly positive at every positive index. "
                        + "The integer companion model uses B0=-1 solely to encode the "
                        + "positive-index recurrence; it does not assert equality to the "
                        + "natural placeholder at zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tribonacci-four-bonacci-local-dold-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Empty good-prime sets and unbounded prime-index violations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every natural sequence a equal to the native tribonacci or "
                            + "fourBonacci, goodPrimes(a) is empty. Moreover, for every prime p "
                            + "and every natural H, there exists a prime q>H such that the "
                            + "integer Mobius sum S over d dividing q of mu(q/d) pPart(p,a(d)) "
                            + "satisfies 0<S<q and q does not divide S. Both p=2 and H=0 "
                            + "are included. Because a(1)=1 and q is prime, S=pPart(p,a(q))-1.")),
                    Paragraph(Text(
                        "The native tribonacci has T0=0, T1=T2=1 and "
                            + "T(n+3)=T(n+2)+T(n+1)+T(n), giving the positive prefix "
                            + "(1,1,2,4,...). Its positivity follows from the native "
                            + "tribonacci_level_pos theorem. FiniteCompanionCyclicModule.time "
                            + "at u=1 acts on reversed states. T uses (1,1,0) and inverse "
                            + "(1,0,0), observing coordinate 2; B uses (1,1,1,-1) and inverse "
                            + "(1,1,-1,0), observing coordinate 3. The inverse observations "
                            + "are both zero, so the unimodular-coordinate obstruction applies.")),
                    Paragraph(Text(
                        "A finite mod-p period T and polynomial congruence lifting give "
                            + "the weak integral period at every valuation depth. For r=pT-1, "
                            + "positivity makes e=valuation_p(a(r)) finite and at least one. "
                            + "The reduced progression r modulo T*p^e preserves valuation e "
                            + "using modulus p^(e+1). Dirichlet supplies a prime above H "
                            + "and p^e-1; its sum is exactly p^e-1. The argument includes "
                            + "p dividing T and imposes no condition at the unused natural "
                            + "index zero."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chuysurichay-2026-tribonacci-four-bonacci-local-dold"),
                    ResolutionKind.Proved)))));
}
