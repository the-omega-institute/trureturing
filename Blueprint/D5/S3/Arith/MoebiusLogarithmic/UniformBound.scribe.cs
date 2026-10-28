using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.MoebiusLogarithmic;

internal sealed class UniformBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/MoebiusLogarithmic/UniformBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite logarithmic Moebius sums have an unconditional bound uniform in the modulus and cutoff.",
        H("Uniform coprime logarithmic sums"),
        Blocks(
            Describe.Lean(DescribeId.Create("coprime-logarithmic-sum"),
                DeclarationHandle.Create(Prefix + "coprimeLogSum"),
                H("The exact logarithmic coefficients"), StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural q and real x, S(q,x) is the finite "
                    + "sum over positive integers n at most the natural floor of x "
                    + "and coprime to q. It uses the actual integer Moebius function "
                    + "cast to the reals and the real natural logarithm. For x<1 the "
                    + "sum is empty. A term n=x, when present, has zero logarithm."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("base-logarithmic-bound"),
                DeclarationHandle.Create(Prefix + "logarithmic_base_bound"),
                H("The elementary base estimate"), StatementSource.FromAuthor(BaseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For x at least one, the unrestricted logarithmic "
                    + "sum lies between zero and 2(1-1/x). Let F(t) be the integral "
                    + "of (u-floor(u))/u^2 from one to t. This primitive is increasing "
                    + "and lies between zero and 1-1/t. Abel summation gives "
                    + "F(t)=log(t)-H(floor(t))+floor(t)/t, where H is the harmonic sum. "
                    + "Finite Moebius cancellation with harmonic weights then expresses "
                    + "S(1,x) as 1-1/x plus the sum of mu(n)F(x/n)/n. The bound "
                    + "on every reciprocal Moebius prefix and finite summation by "
                    + "parts control the absolute value of this last sum by F(x)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-coprime-bound"),
                DeclarationHandle.Create(Prefix + "coprime_log_uniform_bound"),
                H("All moduli and positive real cutoffs"), StatementSource.FromAuthor(UniformFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive natural q and positive real x, "
                    + "the coprime logarithmic sum is nonnegative and at most "
                    + "2q/phi(q), where phi is Euler's actual totient. The finite "
                    + "coefficient convolution gives S(q,x)=sum S(1,x/d)/d over "
                    + "positive d at most x whose prime divisors divide q. All prime "
                    + "powers in this support remain present. The reciprocal mass "
                    + "of that finite set is at most the finite-prime Euler product "
                    + "product (1-1/p)^(-1)=q/phi(q). Applying the base estimate "
                    + "term by term proves both inequalities.")),
                    Paragraph(Text("No relation between q and x is required. The cases "
                        + "q=1, x<1, and x=1 are included. Repeated prime factors of q "
                        + "do not change the supported primes. These finite coefficient "
                        + "estimates do not establish the Riemann hypothesis or the "
                        + "strict Robin inequality for all integers above 5040."))),
                DescribeRole.Theorem))));

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula S(Formula q, Formula x) => Call("S", q, x);

    private static Formula DefinitionFormula()
    {
        var q = F.Id("q"); var x = F.Id("x"); var n = F.Id("n");
        return Disp(Seq(Forall, Sp, q, InMacro, Naturals, Comma,
            x, InMacro, Reals, Comma,
            Equal(S(q, x), Seq(new Formula.Subscript(Sum,
                Seq(D(1), Le, Sp, n, Le, Sp, Call("floor", x), Comma,
                    Equal(Call("gcd", n, q), D(1)))),
                new Formula.Fraction(Call("mu", n), n), Cdot, Sp,
                Call("log", new Formula.Fraction(x, n))))));
    }

    private static Formula BaseFormula()
    {
        var x = F.Id("x");
        return Disp(Seq(Forall, Sp, x, InMacro, Reals, Comma, D(1), Le, Sp, x, Rightarrow,
            D(0), Le, Sp, S(D(1), x), Land, Sp, S(D(1), x), Le,
            D(2), Cdot, Open, D(1), Minus, new Formula.Fraction(D(1), x), Close));
    }

    private static Formula UniformFormula()
    {
        var q = F.Id("q"); var x = F.Id("x");
        return Disp(Seq(Forall, Sp, q, InMacro, Naturals, Comma,
            x, InMacro, Reals, Comma, D(1), Le, Sp, q, Land, D(0), Lt, x, Rightarrow,
            D(0), Le, Sp, S(q, x), Land, Sp, S(q, x), Le,
            new Formula.Fraction(Seq(D(2), Cdot, Sp, q), Call("phi", q))));
    }
}
