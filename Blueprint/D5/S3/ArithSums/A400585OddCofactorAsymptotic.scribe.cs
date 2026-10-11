using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class A400585OddCofactorAsymptoticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/A400585OddCofactorAsymptotic.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/oeis2026a400585");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd-cofactor binomial divisor sum has the cubic asymptotic proposed in A400585.",
        H("A400585: the odd-cofactor summatory asymptotic"),
        Blocks(
            Node("a", "The divisor sum", AFormula(),
                "a(n) = Sum_{d|n, n/d odd} binomial(d, 2). "
                + "This is the NAME of OEIS A400585. In the formula, divisors(n) is "
                + "the finset of positive divisors for n>0, and divisors(0) is empty. "
                + "natDiv(n,d) means natural-number division, or floor(n/d); on "
                + "these positive divisors it is the exact integer cofactor. "
                + "ite(P,x,y) is x when P holds and y otherwise. binomial(d,2) "
                + "is the natural binomial coefficient. The source offset is one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("S", "The positive-prefix sum", SFormula(),
                "S(N) is real-valued. Ioc(0,N) contains exactly the natural "
                + "indices 1 through N. Each natural value a(n) is cast to the "
                + "reals before summation; at N=0 the sum is empty.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("Z3", "The real cubic reciprocal series", ZFormula(),
                "Z3 is the real series defining zeta(3). The natural index q+1 "
                + "enumerates each positive denominator once. The displayed "
                + "division is real division. The proof establishes summability "
                + "and strict positivity of this series.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The full natural ratio limit", ResultFormula(),
                "Conjecture: Sum_{k=1..n} a(k) ~ 7*zeta(3)*n^3/48. - _Vaclav Kotesovec_, Oct 01 2026 "
                + "This is the FORMULA conjecture of OEIS A400585, revision 22. "
                + "Tendsto is convergence of the displayed real-valued function "
                + "along the natural atTop filter to the real neighbourhood filter "
                + "at one. All natural indices are retained, with no hypotheses. "
                + "The value at zero has no effect on the limit. "
                + "Reindexing by the odd cofactor q expresses S(N) as the sum "
                + "of binomial(natDiv(N,q)+1,3) over odd q from one through N. "
                + "The binomial equals (m^3-m)/6 for m=natDiv(N,q). Its normalized "
                + "pointwise limit is 1/(6q^3), dominated by the summable cubic "
                + "reciprocal series. Dominated-series convergence and the even/odd "
                + "split give the constant 7*Z3/48. Its positivity permits the "
                + "final ratio normalization.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a400585-odd-cofactor-asymptotic"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("a400585-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula AFormula()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        return Universal("n", Equal(Call("a", n), SumOver(d, Call("divisors", n),
            Call("ite", Call("Odd", Call("natDiv", n, d)), Call("binomial", d, D(2)), D(0)))));
    }

    private static Formula SFormula()
    {
        var n = F.Id("n");
        var N = F.Id("N");
        return Universal("N", Equal(Call("S", N),
            SumOver(n, Call("Ioc", D(0), N), Cast(Call("a", n), Reals()))));
    }

    private static Formula ZFormula()
    {
        var q = F.Id("q");
        var successor = new Formula.Binary(q, FormulaBinaryOperator.Add, D(1));
        return Disp(Equal(ZetaThree(), SumOver(q, Naturals(), new Formula.Fraction(
            D(1), new Formula.Power(Cast(Cast(successor, Naturals()), Reals()), D(3))))));
    }

    private static Formula ResultFormula()
    {
        var N = F.Id("N");
        var coefficient = new Formula.Fraction(new Formula.Binary(D(7),
            FormulaBinaryOperator.Multiply, ZetaThree()), D(4, 8));
        var denominator = new Formula.Binary(Parenthesized(coefficient),
            FormulaBinaryOperator.Multiply, new Formula.Power(Cast(N, Reals()), D(3)));
        var ratio = new Formula.Fraction(Call("S", N), denominator);
        var function = Parenthesized(Seq(Parenthesized(Seq(N, Colon, Sp, Naturals())),
            Sp, Mapsto, Sp, ratio));
        return Disp(Call("Tendsto", function, F.Id("atTop"), Call("nhds", Cast(D(1), Reals()))));
    }

    private static Formula Universal(string name, Formula body) => Disp(new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Naturals(), body));
    private static Formula SumOver(Formula index, Formula range, Formula body) =>
        Seq(new Formula.Subscript(Sum, new Formula.Relation(index,
            FormulaRelationOperator.MemberOf, range)), Sp, Parenthesized(body));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ZetaThree() => Seq(Operatorname, Grp(F.Id("Z"), D(3)));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
