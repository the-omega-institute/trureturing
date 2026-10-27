using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class BalaA193237ModFiveSevenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/BalaA193237ModFiveSeven.";
    private const string Note = "D5/L/RecurrenceComposition/bala2021triangularcuberoots";
    private static AssessedProvenance Source() =>
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bala's unbounded modulo-five and modulo-seven coefficient congruences.",
        H("OEIS A193237: congruences modulo five and seven"),
        Blocks(
            Paragraph(Text("All indices are natural numbers. Nat.div is natural-number division. "
                + "The finite coefficient sum expresses the infinite triangular series: "
                + "j*(j+1)/2=m implies j≤m. PowerSeries coefficients are rational unless stated otherwise.")),
            Node("F", "The source series", Equal(F.Id("F"), SourceSeries()), Source(),
                "Expansion of g.f.:  ( Sum_{n>=0} (2*n+1)*3^n*(-x)^(n*(n+1)/2) )^(-1/3). OEIS A193237, NAME line (unnumbered web entry; no page number). "
                + "The coefficient at degree m sums exactly the terms of triangular degree m.",
                DescribeRole.Definition),
            Node("IsGF", "The normalized reciprocal cube root",
                All("A", Series(Rat()), Equal(Call("IsGF", F.Id("A")), Norm(F.Id("A"), F.Id("F")))),
                Source(), "The source's constant-one expansion means constantCoeff(A)=1 and A^3*F=1.",
                DescribeRole.Definition),
            Node("claim", "Bala's two conjectures", Equal(F.Id("claim"), ClaimBody(F.Id("F"), true)), Source(),
                "Conjectures: a(5*n+4) == 0 (mod 5) and a(7*n+5) == 0 (mod 7) "
                + "(both checked up to n = 200). - _Peter Bala_, Feb 26 2021 "
                + "OEIS A193237, FORMULA line (unnumbered web entry; no page number). "
                + "The statement asserts existence and covers every normalized rational solution, "
                + "an integer coefficient sequence, both primes, and every natural index.", DescribeRole.Definition),
            Node("triangular", "Weighted triangular series", TriangularFormula(),
                AssessedProvenance.FromRepo(), "For any semiring R and weight function w, the coefficient "
                + "at degree m is the sum of (2*j+1)*w(j) over the triangular indices of degree m.",
                DescribeRole.Definition),
            Node("resolve", "Weighted triangular reciprocal cube roots", ResolveFormula(),
                AssessedProvenance.FromRepo(), "Weights with w(0)=1 and nine dividing every positive "
                + "triangular coefficient give an integral normalized reciprocal cube root. "
                + "Its coefficients satisfy both congruences, independently of the remaining weights.",
                DescribeRole.Theorem),
            Node("result", "Both unbounded congruences", ClaimBody(F.Id("F")),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                "The positive-degree coefficients of F are multiples of nine. Coefficient contraction "
                + "constructs an integral cube root of F, whose inverse is integral. "
                + "Modulo five the triangular series is supported in residues 0 and 1, "
                + "so its cube misses residue 4. Modulo seven it is supported in residues 0, 1 and 3, "
                + "so its square misses residue 5. Frobenius transfers these missing residues "
                + "to the reciprocal cube root. Uniqueness identifies every normalized rational solution.",
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction"))]));

    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series(Formula r) => Call("PowerSeries", r);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Cast(Formula x, Formula r) => Parenthesized(Seq(x, Colon, Sp, r));
    private static Formula Pow(Formula x, Formula n) => new Formula.Power(Parenthesized(x), n);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Arr(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula Norm(Formula a, Formula f) =>
        And(Equal(Call("constantCoeff", a), D(1)), Equal(Multiply(Pow(a, D(3)), f), D(1)));
    private static Formula ClaimBody(Formula f, bool useIsGF = false)
    {
        var a = F.Id("A"); var c = F.Id("a"); var m = F.Id("m"); var n = F.Id("n");
        var normalized = useIsGF ? Call("IsGF", a) : Norm(a, f);
        return And(Ex("A", Series(Rat()), normalized),
            All("A", Series(Rat()), Imp(normalized, Ex("a", Arr(Nat(), Ints()),
                And(All("m", Nat(), Equal(Call("coeff", m, a), Cast(App(c, m), Rat()))),
                    All("n", Nat(), And(
                        Seq(Cast(D(5), Ints()), Sp, Mid, Sp, App(c, Add(Multiply(D(5), n), D(4)))),
                        Seq(Cast(D(7), Ints()), Sp, Mid, Sp, App(c, Add(Multiply(D(7), n), D(5)))))))))));
    }
    private static Formula Triangle(Formula j) => App(Qualified("Nat", "div"), Multiply(j, Add(j, D(1))), D(2));
    private static Formula FiniteSum(Formula m, Formula term) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id("j"), Sp, InMacro, Sp,
            App(Qualified("Finset", "range"), Add(m, D(1))))), Sp, term);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Seq(Operatorname, Grp(F.Id("if")), Sp, condition, Sp,
            Operatorname, Grp(F.Id("then")), Sp, yes, Sp,
            Operatorname, Grp(F.Id("else")), Sp, no);
    private static Formula SourceSeries()
    {
        var j = F.Id("j"); var m = F.Id("m");
        var weight = Multiply(Multiply(Cast(Add(Multiply(D(2), j), D(1)), Rat()), Pow(D(3), j)), Pow(Seq(Minus, D(1)), Triangle(j)));
        return App(Qualified("PowerSeries", "mk"), Fun("m", Nat(),
            FiniteSum(m, If(Equal(Triangle(j), m), weight, D(0)))));
    }
    private static Formula TriangularFormula()
    {
        var r = F.Id("R"); var w = F.Id("w"); var j = F.Id("j"); var m = F.Id("m");
        return Seq(Forall, Sp, Parenthesized(Seq(r, Colon, Sp, F.Id("Type"))), Sp,
            OpenBracket, Call("Semiring", r), CloseBracket, Comma, Sp,
            All("w", Arr(Nat(), r), Equal(Call("triangular", w),
                App(Qualified("PowerSeries", "mk"), Fun("m", Nat(), FiniteSum(m,
                    If(Equal(Triangle(j), m),
                        Multiply(Cast(Add(Multiply(D(2), j), D(1)), r), App(w, j)), D(0))))))));
    }
    private static Formula ResolveFormula()
    {
        var f = F.Id("F"); var w = F.Id("w"); var j = F.Id("j");
        return All("F", Series(Rat()), All("w", Arr(Nat(), Ints()),
            Imp(Equal(App(w, D(0)), D(1)),
                Imp(All("j", Nat(), Imp(Seq(D(0), Sp, Lt, Sp, j),
                    Seq(Cast(D(9), Ints()), Sp, Mid, Sp,
                        Multiply(Cast(Add(Multiply(D(2), j), D(1)), Ints()), App(w, j))))),
                    Imp(Equal(f, App(Qualified("PowerSeries", "map"),
                        App(Qualified("Int", "castRingHom"), Rat()), Call("triangular", w))),
                        ClaimBody(f))))));
    }
}
