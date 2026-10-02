using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class EulerValuationMomentComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit logarithmic comparison of full valuation and prime-support Euler moments.",
        H("Euler Valuation Moment Comparison"),
        Blocks(
            Paragraph(Text("For a prime p and a natural exponent a, Z_p(a) is the sum "
                + "of p^(-j) for 0 <= j <= a. Define U_p(s) as (1-1/p) times the "
                + "sum over a >= 0 of Z_p(a)^s p^(-a), and define W_p(s) as "
                + "1-1/p+(1/p)(1-1/p)^(-s). Real powers are used. U(s) and W(s) "
                + "are the products of these local factors over every prime.")),
            Describe.Lean(
                DescribeId.Create("euler-valuation-moment-comparison"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/EulerValuationMomentComparison.result"),
                H("Convergence and logarithmic comparison"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The real moment order s is at least four. Every local "
                        + "valuation series converges, the local factors lie between one "
                        + "and W_p(s), and both full prime products converge to strictly "
                        + "positive real numbers. Multipliable denotes convergence of "
                        + "the net of finite products.")),
                    Paragraph(Text("A single term near the critical exponent log(s)/log(p) "
                        + "controls the logarithmic loss for p <= sqrt(s). For larger "
                        + "primes the local loss is at most s/(p squared minus one), "
                        + "and the integer tail telescopes. Combining the two ranges "
                        + "gives the displayed bound.")),
                    Paragraph(Text("The definition and large-moment asymptotic of W(s) "
                        + "are given in Andreas Weingartner, The distribution functions "
                        + "of sigma(n)/n and n/phi(n), II, arXiv:1011.4262v1, equation (5) "
                        + "and Lemma 5. The explicit comparison here is the derivation "
                        + "in the Fibonacci atomic relation volume; no originality "
                        + "claim is made."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula a = F.Id("a");
        Formula up = new Formula.Apply(Seq(F.Id("U"), Underscore, Grp(p)), [s]);
        Formula wp = new Formula.Apply(Seq(F.Id("W"), Underscore, Grp(p)), [s]);
        Formula u = new Formula.Apply(F.Id("U"), [s]);
        Formula w = new Formula.Apply(F.Id("W"), [s]);
        Formula z = new Formula.Apply(Seq(F.Id("Z"), Underscore, Grp(p)), [a]);
        Formula term = Seq(new Formula.Power(z, s), Sp, new Formula.Power(p, Seq(Minus, a)));
        Formula gap = Seq(new Formula.Apply(Log, [w]), Minus, new Formula.Apply(Log, [u]));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, s, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma,
                Sp, D(4), Sp, Le, Sp, s, Sp, Rightarrow),
            Seq(Forall, Sp, p, Sp, F.Id("prime"), Comma, Sp,
                new Formula.Apply(F.Id("Summable"), [Seq(a, Sp, Mapsto, Sp, term)]),
                Comma, Sp, D(1), Sp, Le, Sp, up, Sp, Le, Sp, wp),
            Seq(new Formula.Apply(F.Id("Multipliable"), [Seq(p, Sp, Mapsto, Sp, up)]),
                Comma, Sp, new Formula.Apply(F.Id("Multipliable"), [Seq(p, Sp, Mapsto, Sp, wp)])),
            Seq(D(0), Sp, Lt, Sp, u, Comma, Sp, D(0), Sp, Lt, Sp, w),
            Seq(D(0), Sp, Le, Sp, gap, Sp, Le, Sp,
                Seq(Sqrt, Grp(s)), Open, new Formula.Apply(Log, [s]), Plus, D(5), Close)
        ]));
    }
}
