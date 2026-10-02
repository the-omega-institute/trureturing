using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class UniformDivisorWeightTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/UniformDivisorWeightTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorial congruences preserve relative normalized divisor weights uniformly on exponential height bounds.",
        H("Uniform Divisor Weight Transfer"),
        Blocks(
            Node("high-prime-divisor-weight", "High-prime divisor weight", "highWeight", HighFormula(),
                "For positive n, H(m,n) is the product of reciprocal geometric sums z(p,v)=sum(i=0..v) p^(-i) "
                + "over prime divisors p of n greater than m. The exponent v(p,n) is the natural "
                + "prime factorization exponent. The value H(m,0) is one.", DescribeRole.Definition),
            Node("complete-prime-product", "Complete Euler product", "primeProduct", ProductFormula(),
                "P(x) is the product of (1-1/p)^(-1) over positive primes p at most the natural "
                + "floor of the real cutoff x. The natural floor is zero when x is negative.",
                DescribeRole.Definition),
            Node("normalized-divisor-weight", "Normalized divisor weight", "normalizedWeight", WeightFormula(),
                "For a positive natural n, Z(n) is the sum of positive divisors of n divided by n. "
                + "The value at zero is zero, following real division by zero in the formal definition.",
                DescribeRole.Definition),
            Node("uniform-relative-error", "Uniform relative error", "uniformError", ErrorFormula(),
                "U(C,m) is the supremum of the absolute relative errors over positive integers "
                + "a,b bounded by exp(C*m*log(m)) and congruent modulo m!. "
                + "The real supremum of an empty admissible set is defined as zero.", DescribeRole.Definition),
            Node("uniform-factorial-divisor-transfer", "Cutoff envelope and uniform congruence transfer", "result",
                ResultFormula(),
                "For every natural m >= 2 and positive natural n, every real cutoff X >= m "
                + "gives the first bound. Write Z(n)=sigma(n)/n, where sigma is the sum of positive "
                + "divisors. For every fixed positive real C, every positive epsilon admits a "
                + "natural threshold M. All m >= M and positive a,b bounded by exp(C*m*log(m)) "
                + "and congruent modulo m! then satisfy the second bound. This is the epsilon "
                + "form of the third conclusion: U(C,m) tends to zero as m tends to infinity.",
                DescribeRole.Theorem),
            Paragraph(Text("Split the actual prime divisors above m at X. Complete the product "
                + "on m < p <= X to P(X)/P(m). Above X, each logarithmic Euler factor is at most "
                + "1/(X-1), and the number of distinct prime divisors is at most log(n)/log(X). "
                + "The divisor-sum product splits into its small and high prime factors. Set "
                + "X=m*(log(m))^2. Mertens' product estimate and log(X)/log(m) tending to one "
                + "make the complete interval product tend to one. The height bound makes the "
                + "remaining exponential factor tend to one uniformly. The factorial congruence "
                + "squeeze controls the small factors; applying the same bounds to a and b "
                + "in both orders gives the absolute relative error bound.")))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(Formula f, Formula t, Formula body) =>
        Seq(Forall, Sp, f, InMacro, Sp, t, Comma, Sp, body);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula HighFormula()
    {
        var m = F.Id("m"); var n = F.Id("n"); var p = F.Id("p");
        return Disp(Seq(All(Seq(m, Comma, n), N, Seq(D(0), Lt, n, Rightarrow, Sp,
            Equal(Call("H", m, n), Seq(new Formula.Subscript(Prod,
                Seq(p, Mid, Sp, n, Comma, Call("Prime", p), Comma, m, Lt, p)),
                Call("z", p, Call("v", p, n)))))), Land, Sp,
            All(m, N, Equal(Call("H", m, D(0)), D(1)))));
    }
    private static Formula ProductFormula()
    {
        var x = F.Id("x"); var p = F.Id("p");
        return Disp(All(x, R, Equal(Call("P", x), Seq(new Formula.Subscript(Prod,
            Seq(D(0), Lt, p, Le, Sp, new Formula.Floor(Seq(Sp, x)), Comma, Call("Prime", p))),
            Pow(Par(Sub(D(1), new Formula.Fraction(D(1), p))), Seq(Minus, D(1)))))));
    }
    private static Formula WeightFormula()
    {
        var n = F.Id("n");
        return Disp(Seq(All(n, N, Seq(D(0), Lt, n, Rightarrow, Sp,
            Equal(Call("Z", n), new Formula.Fraction(Call("sigma", n), n)))),
            Land, Sp, Equal(Call("Z", D(0)), D(0))));
    }
    private static Formula ErrorFormula()
    {
        var c = F.Id("C"); var m = F.Id("m"); var a = F.Id("a"); var b = F.Id("b");
        return Disp(All(c, R, All(m, N, Equal(Call("U", c, m), Seq(
            new Formula.Subscript(Seq(Operatorname, Grp(F.Id("sup"))), Seq(a, Comma, b, InMacro, Sp, N, Comma,
                D(0), Lt, a, Comma, D(0), Lt, b, Comma,
                a, Comma, b, Le, Sp, Call("exp", Seq(c, m, Call("log", m))), Comma,
                a, Equiv, Sp, b, Pmod, Grp(Seq(m, Bang)))),
            new Formula.Absolute(Sub(new Formula.Fraction(Call("Z", a), Call("Z", b)), D(1))))))));
    }
    private static Formula ResultFormula()
    {
        var m = F.Id("m"); var n = F.Id("n"); var x = F.Id("X");
        var a = F.Id("a"); var b = F.Id("b"); var c = F.Id("C");
        var e = F.Id("epsilon"); var threshold = F.Id("M");
        var first = All(Seq(m, Comma, n), N, Seq(m, Ge, Sp, D(2), Land, Sp, D(0), Lt, n,
            Rightarrow, Sp, All(x, R, Seq(m, Le, Sp, x, Rightarrow, Sp,
                D(1), Le, Sp, Call("H", m, n), Le,
                new Formula.Fraction(Call("P", x), Call("P", m)),
                Call("exp", new Formula.Fraction(Call("log", n),
                    Seq(Par(Sub(x, D(1))), Call("log", x))))))));
        var second = All(c, R, Seq(D(0), Lt, c, Rightarrow, Sp,
            All(e, R, Seq(D(0), Lt, e, Rightarrow, Sp,
                Exists, Sp, threshold, InMacro, Sp, N, Comma, Sp,
                All(m, N, Seq(threshold, Le, Sp, m, Rightarrow, Sp,
                    All(Seq(a, Comma, b), N, Seq(D(0), Lt, a, Comma, D(0), Lt, b,
                        Comma, a, Le, Sp, Call("exp", Seq(c, m, Call("log", m))),
                        Comma, b, Le, Sp, Call("exp", Seq(c, m, Call("log", m))),
                        Comma, a, Equiv, Sp, b, Pmod, Grp(Seq(m, Bang)),
                        Rightarrow, Sp, new Formula.Absolute(Sub(
                            new Formula.Fraction(Call("Z", a), Call("Z", b)), D(1))), Lt, e))))))));
        var third = All(c, R, Seq(D(0), Lt, c, Rightarrow, Sp,
            Equal(Seq(new Formula.Subscript(Lim, Seq(m, To, Infty)), Call("U", c, m)), D(0))));
        return Disp(Seq(Par(first), Land, Sp, Par(second), Land, Sp, Par(third)));
    }
}
