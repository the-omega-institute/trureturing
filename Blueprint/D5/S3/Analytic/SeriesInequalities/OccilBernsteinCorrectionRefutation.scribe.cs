using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class OccilBernsteinCorrectionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Analytic/occil2026bernreq");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The convex symmetric quadratic x² − x + 1/2 refutes both original Bernstein correction prescriptions at n = 2: their shared degree-4 normalized coefficient vector has middle entry −1/48.",
        H("A convex quadratic refutes both Bernstein corrections"),
        Blocks(
            Entry("f", "The counterexample function", "On [0,1], f(x) = (x − 1/2)² + 1/4 lies in (0,1], is convex, and is symmetric about 1/2. These interval-wide hypotheses are proved internally; no continuity hypothesis is needed."),
            Entry("B", "The original Bernstein sample operator", "For real u and natural n, B(n,u) sums u(j/n) times binom(n,j) X^j (1−X)^(n−j) over j = 0,...,n. Samples and polynomial scalars are real. All uses in the claim have n >= 2."),
            Entry("admissible", "Range and convexity on the closed interval", "The range is strictly positive and at most one for every x in [0,1]. Convexity is the inequality u(tx+(1−t)y) <= t u(x)+(1−t)u(y) for all x,y,t in [0,1]. Values of the real function outside this interval have no role."),
            Entry("maxError", "An actual attained absolute maximum", "Both clauses are required: every x in [0,1] has |B(n,u)(x)−u(x)| <= M, and some x in [0,1] attains equality. No continuity or supremum replaces this predicate."),
            Entry("midpointError", "The actual midpoint absolute error", "This is |B(n,u)(1/2)−u(1/2)|, with no maximum premise."),
            Entry("coeff", "The normalized degree-4 coefficient vector", "The vector is [1/16,0,−1/48,0,1/16]. The normalization includes binom(4,j), as in the source; it is not a monomial coefficient vector."),
            Entry("realization", "A normalized representation at the specified degree", "The sum uses j in Fin(d+1), so it contains exactly j = 0,...,d. Each term is a(j) binom(d,j) X^j (1−X)^(d−j). Representation degree d does not assert that the ordinary polynomial degree equals d."),
            Entry("nonnegativeCoefficients", "Nonnegative coefficients in that basis", "A polynomial has this property when it has a representation of the specified degree with all real coefficients nonnegative. The proof identifies every competing real representation uniquely by mapping it to the existing complex Bernstein-independent family and using the injective real embedding."),
            Entry("maximumBranch", "The full universal attained-maximum coefficient assertion", "For every admissible real function, every integer k >= 1 and every pair of actual attained maxima M,N at n = 2^k and 2n, the unmodified increment (B(2n,u)−N)−(B(n,u)−M) must have nonnegative normalized coefficients at representation degree exactly 2n."),
            Entry("midpointBranch", "The full universal symmetric midpoint coefficient assertion", "For every admissible real function symmetric on [0,1], and every integer k >= 1, subtract the actual midpoint absolute errors from B at n = 2^k and 2n. The increment must have nonnegative normalized coefficients at representation degree exactly 2n. There is no maximum premise."),
            Entry("claim", "The unchanged registered coefficient conjunction", "Occil's first item after the final Prove or disprove in Other Questions asks for both correction prescriptions to converge from below with nonnegative Bernstein increment coefficients. The preregistered claim is precisely the conjunction of their universal coefficient requirements. Each is a necessary clause of the corresponding original branch, independently of the unspecified convergence topology. A positive coefficient result alone would not prove convergence."),
            Entry("result", "Both original prescriptions fail at n = 2", "For f(x) = x²−x+1/2, B₂f = (X²−X)/2+1/2 and B₄f = 3(X²−X)/4+1/2. The errors are x(1−x)/2 and x(1−x)/4 on the entire interval, with actual maxima 1/8 and 1/16 attained at 1/2; these also equal the midpoint errors. Both increments are 1/16−X(1−X)/4 = (X−1/2)²/4. The exact degree-4 normalized coefficients are [1/16,0,−1/48,0,1/16]. Uniqueness excludes any nonnegative representation. The private branch_refutations proves each universal branch false, and result is literally Not claim. This refutes both full original conjunctions through their coefficient clauses without a claim against convergence itself. Existing complex Bernstein independence is reused; this external-problem resolution does not assert a new escape witness.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("occil-convex-bernstein-corrections"), ResolutionKind.Refuted)))));

    private static DocumentBlock Entry(string name, string title, string prose,
        DescribeRole role = DescribeRole.Definition, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("occil-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            name is "B" or "admissible" or "maxError" or "midpointError" or "maximumBranch" or "midpointBranch" or "claim"
                ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
