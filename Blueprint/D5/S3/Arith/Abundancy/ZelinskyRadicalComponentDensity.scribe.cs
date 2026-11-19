using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class ZelinskyRadicalComponentDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/ZelinskyRadicalComponentDensity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/zelinsky2026smallcomponent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Radical component inequalities have natural density 1-log(2).",
        H("The density of bounded radical components"),
        Blocks(
            Describe.Lean(DescribeId.Create("radical-component-set"),
                DeclarationHandle.Create(Prefix + "radicalComponentSet"),
                H("A threshold for every prime-power component"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a real parameter lam, the set consists of "
                    + "natural numbers n at least two for which every prime divisor p "
                    + "satisfies p^(v_p(n)+1) < lam*rad(n). Here rad(n) is the product "
                    + "of the distinct prime factors of n. At lam=2 this is the set B "
                    + "of the source, apart from its immaterial convention at n=1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("count"),
                DeclarationHandle.Create(Prefix + "count"),
                H("Inclusive positive counting functions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a set S of natural numbers, count(S,X) is "
                    + "the number of its elements in the inclusive interval from 1 "
                    + "to X. Both endpoints are natural numbers."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("radical-component-count"),
                DeclarationHandle.Create(Prefix + "radicalComponentCount"),
                H("The counting function of the component set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The function radicalComponentCount(lam,X) "
                    + "counts the members of radicalComponentSet(lam) up to X, "
                    + "using the same inclusive positive counting convention."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The asymptotic density is independent of the positive threshold"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every positive real lam, the quotient "
                        + "radicalComponentCount(lam,X)/X tends to 1-log(2) as the "
                        + "natural threshold X tends to infinity. Thus the source's "
                        + "set B has positive natural density, and its assertion "
                        + "that B has natural density zero is false.")),
                    Paragraph(Text("Write P(n) for the largest prime factor of n "
                        + "and F_c={n>=2 : P(n)^2<c*n}. The complement of F_1 has "
                        + "a unique representation n=p*m with p prime and 1<=m<=p. "
                        + "Its exact counting function is the sum of p over primes "
                        + "p<=sqrt(X), plus the sum of floor(X/p) over primes "
                        + "sqrt(X)<p<=X. The first sum is at most "
                        + "sqrt(X)*pi(sqrt(X))=o(X). Replacing floor(X/p) by X/p "
                        + "in the second sum has error at most pi(X)=o(X).")),
                    Paragraph(Text("Mertens' reciprocal-prime estimate writes the "
                        + "sum of 1/p up to x as log(log(x))+M+o(1). Subtracting "
                        + "the value at sqrt(x) gives log(2)+o(1). Consequently "
                        + "F_1 has natural density 1-log(2).")),
                    Paragraph(Text("For fixed c>0, put a=min(1,c) and b=max(1,c). "
                        + "If membership in F_c and F_1 differs, then "
                        + "a*n<=P(n)^2<=b*n. Writing n=p*m bounds p by sqrt(b*X) "
                        + "and m by p/a. The number of such pairs is at most "
                        + "pi(Y)*Y/a, where Y=floor(sqrt(b*X)). Since Y^2<=b*X "
                        + "and pi(Y)/Y tends to zero, this bound is o(X). Every "
                        + "F_c therefore has the same density as F_1.")),
                    Paragraph(Text("To control repeated prime factors, write "
                        + "n=s^2*u with u squarefree. The number of integers "
                        + "n<=X divisible by some s^2 with s>T is at most "
                        + "2*X/(T+1). Outside this set the square factor can be "
                        + "chosen with s<=T. Since u divides rad(n), one has "
                        + "n<=T^2*rad(n). If v_p(n)>=2, squarefreeness of u gives "
                        + "v_p(n)=2*v_p(s)+v_p(u) with v_p(u)<=1, hence "
                        + "p^(v_p(n)+1)<=s^4<=T^4.")),
                    Paragraph(Text("For n>T^6/lam, repeated prime factors thus "
                        + "satisfy the required strict component inequality. "
                        + "A prime factor of exponent one satisfies it whenever "
                        + "P(n)^2<(lam/T^2)*n. Apart from the finite initial "
                        + "interval and the exceptional large square divisors, "
                        + "F_(lam/T^2) is contained in radicalComponentSet(lam). "
                        + "Conversely radicalComponentSet(lam) is contained "
                        + "in F_lam, because rad(n)<=n and the largest prime "
                        + "factor has positive exponent. The common density "
                        + "of the two critical sets and the error 2/(T+1), "
                        + "which tends to zero as T increases, give the result."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zelinsky-2026-radical-component-density"),
                    ResolutionKind.Proved)))));
}
