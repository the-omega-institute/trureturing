using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class ZelinskyZhangKLPrimitiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/ZelinskyZhangKLPrimitive.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/zelinskyzhang2025klprimitive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "There are infinitely many positive deficient KL-primitive integers.",
        H("Zelinsky and Zhang's Conjecture 15"),
        Blocks(
            Describe.Lean(DescribeId.Create("kl"), DeclarationHandle.Create(Prefix + "KL"),
                H("The logarithmic divisor sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Equation (6) defines KL(n) as the sum over positive "
                    + "divisors d of n of d log(d/(2 phi(d))). Quotients and logarithms "
                    + "are real. The value at one is minus log 2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primitive"),
                DeclarationHandle.Create(Prefix + "KLPrimitive"),
                H("KL primitivity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Definition 1 on page twelve requires KL(n) "
                    + "to be nonnegative and KL(d) to be strictly negative for every "
                    + "positive proper divisor d of n."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("deficient"),
                DeclarationHandle.Create(Prefix + "Deficient"),
                H("Deficiency"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("An integer n is deficient when its sum of "
                    + "positive divisors is strictly smaller than 2n."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prime-increment-bounds"),
                DeclarationHandle.Create(Prefix + "f_bounds"),
                H("Bounds for the logarithmic prime increment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural p at least two, "
                    + "f(p)=p/(p+1)*log(p/(p-1)) satisfies "
                    + "2/(3p)<=f(p)<=2/p and 0<f(p)<log(2). "
                    + "These estimates compare finite prime-tail sums with "
                    + "reciprocal-prime sums."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-prime-tail-mass"),
                DeclarationHandle.Create(Prefix + "tail_mass"),
                H("Arbitrarily large finite prime-tail mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every pair of natural numbers Q and k, "
                    + "there is a finite set of primes exceeding Q whose f sum "
                    + "is at least k/3. In particular the increment upper bound "
                    + "converts the choice k=6 into reciprocal mass at least one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("divisor-deficiency"),
                DeclarationHandle.Create(Prefix + "deficient_of_dvd"),
                H("Positive divisors preserve deficiency"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If d and n are positive natural numbers, "
                    + "d divides n, and n is deficient, then d is deficient. "
                    + "This follows from monotonicity of sigma(n)/n under "
                    + "divisibility and transfers the bounds on products "
                    + "with one prime removed to all proper divisors."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rough-deficient-core"),
                DeclarationHandle.Create(Prefix + "rough_deficient_core"),
                H("Exponential threshold control at quadratic logarithmic cost"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Fix any natural cutoff B. There are constants K>0 "
                        + "and T such that for every real t at least T there is a "
                        + "finite set S of primes exceeding B. Put "
                        + "h=product over p in S of (1+1/p) and a=h/(2-h). Then "
                        + "h<2, exp(t)<=a<=3*exp(t), every p in S is less than 2a, "
                        + "and the sum of log(p) over S is at most K*t^2. "
                        + "Distinctness of the prime factors makes their product "
                        + "squarefree, and its abundancy ratio is h.")),
                    Paragraph(Text("Divergence of the reciprocal-prime sum supplies "
                        + "a finite prime product with h at least 2. A minimal "
                        + "crossing set, with its largest prime removed, gives "
                        + "a deficient starting core whose threshold parameter "
                        + "exceeds its prime factors.")),
                    Paragraph(Text("For a large current parameter a, choose a "
                        + "prime p in (2a,3a]. Adjoining p "
                        + "keeps the core deficient and replaces a by "
                        + "a*(p+1)/(p-a), which lies between 3a/2 and 3a. "
                        + "All old and new prime factors remain below twice the "
                        + "new parameter. The first iteration to reach exp(t) "
                        + "therefore has parameter at most 3*exp(t). The number "
                        + "of iterations is linear in t, and each added prime "
                        + "has logarithm bounded linearly in that iteration's "
                        + "index, giving the quadratic total cost.")),
                    Paragraph(Text("These deficient cores supply the initial factors "
                        + "for the lower bound on primitive non-deficient integers."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Infinitely many deficient KL-primitive integers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every natural bound B there is a positive "
                        + "integer n greater than B that is deficient and KL-primitive. "
                        + "This is the infinitude assertion of Conjecture 15.")),
                    Paragraph(Text("On a product of distinct primes, KL(n)/sigma(n) "
                        + "plus log 2 is the sum of f(p) = p/(p+1) log(p/(p-1)). "
                        + "The logarithm of sigma(n)/n is the sum of g(p) = log(1+1/p). "
                        + "StrictGibbs.kl_divergence_pos_of_ne applied to the distinct "
                        + "two-point distributions P = (1/(p+1), p/(p+1)) and "
                        + "Q = (1/p, (p-1)/p) gives g(p) < f(p), since their "
                        + "KL divergence is f(p)-g(p). The Euler logarithm upper "
                        + "bound is FibonacciRankEulerTail.euler_log_bounds. "
                        + "The bounds 2/(3p) <= f(p) <= 2/p give arbitrarily small "
                        + "positive increments with unbounded finite tail sums.")),
                    Paragraph(Text("Choose one prime beyond B and two, retaining "
                        + "half its positive difference f(p)-g(p). Add distant primes "
                        + "until the f sum first reaches log 2, with each increment "
                        + "smaller than this reserve. The resulting product has "
                        + "nonnegative KL and is deficient. Its smallest positive "
                        + "divisor with nonnegative KL is KL-primitive. Deficiency "
                        + "passes to divisors by GA2ForcedPrimeSource.abundancy_mono. "
                        + "All prime factors still exceed B, and the chosen divisor "
                        + "cannot be one, so it exceeds B.")),
                    Paragraph(Text("The odd squarefree strengthening follows from "
                        + "the same construction on paper. The present conclusion "
                        + "does not require that strengthening and does not settle "
                        + "the question about primitive non-deficient integers."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zelinsky-zhang-2025-conjecture-15"),
                    ResolutionKind.Proved)))));
}
