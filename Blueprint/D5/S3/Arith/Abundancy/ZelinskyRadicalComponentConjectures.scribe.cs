using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class ZelinskyRadicalComponentConjecturesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/zelinsky2026smallcomponent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primitive non-deficient integers have relative density zero in B.",
        H("Zelinsky's Conjectures 10, 12 and 14"),
        Blocks(
            Describe.Lean(DescribeId.Create("primitive-count"),
                DeclarationHandle.Create(Prefix + "primitiveCount"),
                H("The primitive non-deficient counting function"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The count uses the existing predicate "
                    + "PrimitiveNonDeficient and the inclusive interval [1,X]. "
                    + "A positive integer is primitive non-deficient when its divisor "
                    + "sum is at least twice itself and every positive proper divisor "
                    + "has divisor sum strictly less than twice itself."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primitive-density-zero"),
                DeclarationHandle.Create(Prefix + "primitive_density_zero"),
                H("Primitive non-deficient integers have density zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Write h(n)=sigma(n)/n. For n primitive "
                        + "non-deficient and a prime power p^a exactly dividing n, "
                        + "the prime-step formula and h(n/p)<2 give "
                        + "2<=h(n)<2+2/p^a. If all full prime powers of n are at "
                        + "most T, their prime valuations show that n divides T!. "
                        + "Consequently every primitive non-deficient n>T! "
                        + "satisfies 2<=h(n)<2+2/T.")),
                    Paragraph(Text("Fix 2<=K<=L and take T=2L^2. If a primitive "
                        + "non-deficient n>T! has a prime divisor p in [K,L] "
                        + "which occurs exactly once, write n=mp. Then "
                        + "h(n)=h(m)(1+1/p). The cofactor m determines p uniquely "
                        + "among such integers. Indeed, distinct primes p<q<=L "
                        + "give a difference h(m)(1/p-1/q)>=1/L^2, since "
                        + "h(m)>=1. Two values in [2,2+1/L^2) cannot have "
                        + "that separation. There are at most X/K possible "
                        + "cofactors for n<=X.")),
                    Paragraph(Text("The remaining integers either have no prime "
                        + "divisor in [K,L] or are divisible by p^2 for some "
                        + "p>=K. Put Q equal to the product of the primes in "
                        + "[K,L]. Quotient and remainder modulo Q bound the "
                        + "first count by X*phi(Q)/Q+phi(Q). Euler's totient "
                        + "formula identifies phi(Q)/Q with the product of "
                        + "1-1/p on that interval. The square-divisor count is "
                        + "at most 2X/K. Altogether C(X) is at most "
                        + "(2L^2)!+phi(Q)+X*product(1-1/p)+3X/K.")),
                    Paragraph(Text("For fixed K, Mertens' product theorem makes "
                        + "the interval product tend to zero as L tends to "
                        + "infinity. Choose L so that it is less than 1/K. "
                        + "After division by X, the two constant terms vanish, "
                        + "and the remaining upper bound is 4/K. Letting K "
                        + "increase proves C(X)/X tends to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("conjectures"),
                DeclarationHandle.Create(Prefix + "conjectures"),
                H("The three relative counting limits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For B defined by the threshold lam=2, "
                    + "the limits (B intersect C)(X)/B(X), "
                    + "(B intersect C_O)(X)/B(X), and "
                    + "(B intersect C_M)(X)/B(X) are all zero. Here C_O is the "
                    + "set of odd primitive non-deficient integers, and M "
                    + "ranges over all nonempty finite sets of primes; C_M "
                    + "consists of primitive non-deficient integers divisible "
                    + "by no element of M. Each numerator is bounded by C(X), "
                    + "whereas B(X)/X tends to the positive constant "
                    + "1-log(2). The quotient limit therefore follows. "
                    + "The argument applies to every subset of C and every "
                    + "positive radical threshold. It does not settle the "
                    + "different ratios whose denominator is C(X)."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zelinsky-2026-radical-component-density"),
                    ResolutionKind.Proved)),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The source's zero-density assertion for B"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source states that B has natural "
                    + "density zero. This claim uses the original threshold "
                    + "lam=2 and the inclusive positive counting function. "
                    + "Including or excluding the integer one leaves the "
                    + "density unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("B does not have density zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact asymptotic B(X)/X -> 1-log(2) "
                    + "contradicts the zero-density claim, because log(2)<1. "
                    + "Uniqueness of limits gives its formal negation. "
                    + "This correction is compatible with the three "
                    + "conjectures: their numerators have density zero "
                    + "and their common denominator has positive density."))),
                DescribeRole.Theorem)))));
}
