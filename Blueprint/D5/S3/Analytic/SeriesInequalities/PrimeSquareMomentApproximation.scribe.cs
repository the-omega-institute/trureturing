using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class PrimeSquareMomentApproximationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/AnalyticClosure/unkown2026primesquaremoment");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact infinite local moment has a uniform prime-square approximation for every sufficiently large real moment parameter.",
        H("Uniform prime-square local moments"), Blocks(
            Paragraph(Text("All local Lean names belong to D5.S3.Analytic.SeriesInequalities.PrimeSquareMomentApproximation. "
                + "The exponent a is natural, including zero; p and s in the definitions are real. Powers with real exponent s are positive-base real powers on the stated domain. "
                + "The infinite sum is Lean's unconditional real tsum; its summability is proved for every p>1 and s≥0.")),
            Definition("factor", "The original rational local factor", FactorFormula(),
                "For a=0 the factor is one. For every integer a≥1 it is exactly (p+3a(p−1))/(2(p+a(p−1))). "
                + "For p>1 all these factors are positive, and for p≥1 they are at most 3/2.", true),
            Definition("localMoment", "The full infinite real-power moment", MomentFormula(),
                "This is the source series with every natural exponent present. Its prefactor is 1−1/p. "
                + "Comparison with (3/2)^s times the geometric series with ratio 1/p proves summability for p>1 and s≥0. "
                + "The a=0 summand is one, so the local moment is strictly positive for p>1 and s>0.", true),
            Definition("c", "The prime-square scale", Equal(Local("c"), Divide(Log(Divide(D(7), D(6))), D(2))),
                "The source writes P=exp(cs). Thus P²=exp(2cs), and P^(1−δ)=exp((1−δ)cs).", true),
            Definition("c3", "A sufficient slope for every higher exponent", Equal(Local("c3"), Divide(Log(Divide(D(5), D(4))), D(3))),
                "For g(a)=(3a+1)/(2(a+1)), induction gives g(a)^3≤(5/4)^a for every a≥3. "
                + "Taking logarithms yields log g(a)≤c3 a. This explicit c3 supplies the source's proposed smaller slope.", false),
            Describe.Lean(DescribeId.Create("prime-square-gap"), DeclarationHandle.Create(Prefix + "c3_lt_c"),
                H("A strict gap between the two scales"), StatementSource.FromAuthor(Disp(Less(Local("c3"), Local("c")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "The rational inequality (5/4)^2<(7/6)^3 gives 2 log(5/4)<3 log(7/6). "
                    + "Together with log(5/4)>0, this gives 0<c3<c."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prime-square-positive-scale"), DeclarationHandle.Create(Prefix + "c_pos"),
                H("A positive exponential scale"), StatementSource.FromAuthor(Disp(Less(D(0), Local("c")))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "Positivity follows from 0<c3<c. In particular 1−c3/c is positive, so the admissible interval "
                    + "0<δ<1−c3/c is nonempty; its midpoint is one explicit choice."))), DescribeRole.Theorem),
            Definition("originalClaim", "The complete uniform statement", IffF(Local("originalClaim"), ClaimFormula()),
                "For each fixed admissible δ and fixed B>2, one real threshold works for every real s beyond it and every prime "
                + "in the original congruence class and window. The lower endpoint is strict and the upper endpoint is closed. "
                + "The explicit interval for δ is a sufficient interpretation of the source's sufficiently-small condition.", false),
            Describe.Lean(DescribeId.Create("prime-square-uniform-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Uniform logarithmic approximation"), StatementSource.FromAuthor(Disp(Local("originalClaim"))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Put X=exp(2cs)/p² and q=exp(c3 s)/p. The sum of all a≥3 terms is at most q³/(1−q) when q<1. "
                        + "The a=1 term is at most 1/p. The exact a=2 factor is (7/6)(1−4/(21p−14)), so for p≥2 "
                        + "its logarithm lies between 2c−2/p and 2c. Consequently, if A=1+X and A0=1+e_p(2)^s/p², "
                        + "then A exp(−2s/p)≤A0≤A. This controls the relative perturbation even when X grows.")),
                    Paragraph(Text("Writing T for the full tail and U=e_p(1)^s/p+T, the exact identity is "
                        + "m_p(s)=(1−1/p)(A0+U). The inequalities −2x≤log(1−x) for 0≤x≤1/2 and log(1+y)≤y "
                        + "give |log m_p(s)−log A|≤2/p+2s/p+q³/(1−q). Every logarithm used in this comparison has a positive argument.")),
                    Paragraph(Text("Let α=(1−δ)c and κ=α−c3>0. Whenever p>exp(αs), one has 1/p≤exp(−αs) and q≤exp(−κs). "
                        + "Eventually q≤1/2, so q³/(1−q)≤2q. The common error bound is "
                        + "2exp(−αs)+2s exp(−αs)+2exp(−κs), which tends to zero as the real variable s tends to infinity. "
                        + "Choose one threshold for this bound to be below ε, for q≤1/2 and for s≥1. It is independent of p.")),
                    Paragraph(Text("The estimate holds for all real p≥2 above the lower exponential cutoff. Specializing it to natural primes "
                        + "preserves p≡1 mod 4 and p≤B exp(cs), although these additional restrictions are unnecessary for the bound. "
                        + "The conclusion concerns a single local factor. It asserts no global Euler-product approximation, sum over primes, or optimal endpoint for δ."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathoverflow-516091-prime-square-local-moment"), ResolutionKind.Proved))
        )));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose, bool literature) =>
        Describe.Lean(DescribeId.Create("prime-square-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula FactorFormula() => All("p", R(), All("a", N(), And(
        ImpliesF(Equal(X("a"), D(0)), Equal(LocalCall("factor", X("p"), X("a")), D(1))),
        ImpliesF(LE(D(1), X("a")), Equal(LocalCall("factor", X("p"), X("a")),
            Divide(Add(X("p"), Mul(Mul(D(3), Typed(X("a"), R())), Sub(X("p"), D(1)))),
                Mul(D(2), Add(X("p"), Mul(Typed(X("a"), R()), Sub(X("p"), D(1)))))))))));

    private static Formula MomentFormula() => All("p", R(), All("s", R(),
        Equal(LocalCall("localMoment", X("p"), X("s")), Mul(Sub(D(1), Divide(D(1), X("p"))),
            Seq(new Formula.Subscript(Sum, Seq(X("a"), InMacro, N())), Sp,
                Divide(Pow(LocalCall("factor", X("p"), X("a")), X("s")), Pow(X("p"), X("a"))))))));

    private static Formula ClaimFormula()
    {
        var p = Typed(X("p"), R());
        var error = Abs(Sub(Log(LocalCall("localMoment", p, X("s"))),
            Log(Add(D(1), Divide(Exp(Mul(Mul(D(2), Local("c")), X("s"))), Pow(p, D(2)))))));
        var primes = All("p", N(), ImpliesF(Call("Nat", "Prime", X("p")),
            ImpliesF(Equal(Call("Nat", "mod", X("p"), D(4)), D(1)),
                ImpliesF(Less(Exp(Mul(Mul(Sub(D(1), X("delta")), Local("c")), X("s"))), p),
                    ImpliesF(LE(p, Mul(X("B"), Exp(Mul(Local("c"), X("s"))))), Less(error, X("epsilon")))))));
        var threshold = Ex("S", R(), All("s", R(), ImpliesF(LE(X("S"), X("s")), primes)));
        var accuracy = All("epsilon", R(), ImpliesF(Less(D(0), X("epsilon")), threshold));
        var window = All("B", R(), ImpliesF(Less(D(2), X("B")), accuracy));
        return All("delta", R(), ImpliesF(Less(D(0), X("delta")),
            ImpliesF(Less(X("delta"), Sub(D(1), Divide(Local("c3"), Local("c")))), window)));
    }

    private static Formula X(string s) => F.Id(s);
    private static Formula Local(string s) => Q("PrimeSquareMomentApproximation", s);
    private static Formula LocalCall(string s, params Formula[] a) => App(Local(s), a);
    private static Formula Q(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Call(string name, params Formula[] a) => App(Q(name), a);
    private static Formula Call(string owner, string name, params Formula[] a) => App(Q(owner, name), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula N() => Seq(Mathbb, Grp(X("N")));
    private static Formula R() => Seq(Mathbb, Grp(X("R")));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, Typed(X(n), t), Comma, Sp, Parenthesized(b));
    private static Formula Ex(string n, Formula t, Formula b) => Seq(Exists, Sp, Typed(X(n), t), Comma, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Divide(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Exp(Formula a) => Call("Real", "exp", a);
    private static Formula Log(Formula a) => Call("Real", "log", a);
    private static Formula Abs(Formula a) => Call("abs", a);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula ImpliesF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
