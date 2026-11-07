using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.MatharA379464;

internal sealed class MatharA379464ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/MatharA379464/Result.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/mathar2025a379464");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal OEIS A379464 path count satisfies the eight-term recurrence.", H("The A379464 recurrence"),
        Blocks(
            Paragraph(Text("The source states: “Conjecture D-finite with recurrence +3*(n+4)*(3*n+4)*(3*n+8)*a(n) +3*(-63*n^3-297*n^2-349*n-60)*a(n-1) +3*(189*n^3+270*n^2-229*n-140)*a(n-2) +15*(-63*n^3+117*n^2+44*n-64)*a(n-3) +(689*n^3-5372*n^2+6946*n-1288)*a(n-4) +(n-4)*(201*n^2+2767*n-3011)*a(n-5) -(n-5)*(579*n+257)*(n-4)*a(n-6) +229*(n-5)*(n-6)*(n-4)*a(n-7)=0.” OEIS A379464, revision 20, unnumbered FORMULA line. The displayed proposition keeps integer polynomial arithmetic and natural sequence subtraction.")),
            Node("E", "The Euler operator", EFormula(), AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("L", "The differential operator", LFormula(), AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("recurrence", "The rational coefficient recurrence", RecurrenceFormula(), AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("geom", "The geometric series", GeomFormula(), AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("param", "The substitution parameter", ParamFormula(), AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("transform", "The binomial transform", TransformFormula(), AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("b", "The factorial sequence", BFormula(), AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("coeff_L", "Coefficient extraction", CoeffLFormula(), AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("forcing_zero", "Vanishing of the forcing term", ForcingZeroFormula(), AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("transform_coefficients", "The transform coefficients", TransformCoefficientsFormula(), AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Node("explicit_series_certificate", "The explicit series certificate", CertificateFormula(), AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mathar379464-result-claim"), DeclarationHandle.Create(Prefix + "claim"), H("The source recurrence claim"), StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every natural n at least 7, the eight displayed coefficient terms sum to zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mathar379464-result-result"), DeclarationHandle.Create(Prefix + "result"), H("The recurrence is proved"), StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The path count is converted to a binomial transform of the factorial series. The formal differential certificate has zero coefficients in degrees at least 7, so coefficient extraction gives the displayed recurrence for every such n."))), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("mathar379464"), ResolutionKind.Proved)))));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula A(Formula n) => Call("a", n);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Cast(Formula x) => Parenthesized(Seq(x, Colon, Z()));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        Formula z = Cast(n);
        Formula term0 = Mul(Mul(Mul(D(3), Add(z, D(4))), Add(Mul(D(3), z), D(4))), Add(Mul(D(3), z), D(8)));
        Formula body = Mul(term0, A(n));
        body = Add(body, Mul(Mul(D(3), Sub(Sub(Sub(Mul(new Formula.Negate(Num(63)), Pow(z, D(3))), Mul(Num(297), Pow(z, D(2)))), Mul(Num(349), z)), Num(60))), A(Sub(n, D(1)))));
        body = Add(body, Mul(Mul(D(3), Sub(Sub(Add(Mul(Num(189), Pow(z, D(3))), Mul(Num(270), Pow(z, D(2)))), Mul(Num(229), z)), Num(140))), A(Sub(n, D(2)))));
        body = Add(body, Mul(Mul(Num(15), Sub(Add(Add(Mul(new Formula.Negate(Num(63)), Pow(z, D(3))), Mul(Num(117), Pow(z, D(2)))), Mul(Num(44), z)), Num(64))), A(Sub(n, D(3)))));
        body = Add(body, Mul(Sub(Add(Sub(Mul(Num(689), Pow(z, D(3))), Mul(Num(5372), Pow(z, D(2)))), Mul(Num(6946), z)), Num(1288)), A(Sub(n, D(4)))));
        body = Add(body, Mul(Mul(Sub(z, D(4)), Sub(Add(Mul(Num(201), Pow(z, D(2))), Mul(Num(2767), z)), Num(3011))), A(Sub(n, D(5)))));
        body = Sub(body, Mul(Mul(Mul(Sub(z, D(5)), Add(Mul(Num(579), z), Num(257))), Sub(z, D(4))), A(Sub(n, D(6)))));
        body = Add(body, Mul(Mul(Mul(Num(229), Sub(z, D(5))), Sub(z, D(6))), Mul(Sub(z, D(4)), A(Sub(n, D(7))))));
        return Disp(All("n", N(), Imp(Le(D(7), n), Eq(body, D(0)))));
    }
    private static DocumentBlock Node(string name, string title, Formula formula, AssessedProvenance provenance, DescribeRole role) => Describe.Lean(
        DescribeId.Create("mathar379464-operator-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text("The formal-series expression uses rational coefficients and the displayed differential operators."))), role);

    private static Formula Q() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula PS() => Call("PowerSeries", Q());
    private static Formula X() => Qualified("PowerSeries", "X");
    private static Formula C(Formula x) => Qualified("PowerSeries", "C", x);
    private static Formula Coeff(Formula n, Formula f) => Qualified("PowerSeries", "coeff", n, f);


    private static Formula CastQ(Formula x) => Parenthesized(Seq(x, Colon, Q()));

    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula V(Formula v, int k) => Call("v", Sub(v, Num(k)));
    private static Formula E(Formula f) => Call("E", f);

    private static Formula EBody(Formula f) =>
        Sub(Mul(Mul(X(), Sub(D(1), X())), Call("derivative", f)), Mul(X(), f));

    private static Formula EFormula() => All("f", PS(), Eq(Call("E", F.Id("f")), EBody(F.Id("f"))));

    private static Formula LBody(Formula f)
    {
        Formula left = Mul(Pow(Sub(D(1), X()), D(4)),
            Add(Add(Mul(C(Num(27)), E(E(E(f)))), Mul(C(Num(216)), E(E(f)))),
                Add(Mul(C(Num(528)), E(f)), Mul(C(Num(384)), f))));
        Formula right = Mul(C(Num(256)), Mul(Pow(X(), D(4)),
            Add(Add(E(E(E(f))), Mul(C(Num(14)), E(E(f)))),
                Add(Mul(C(Num(63)), E(f)), Mul(C(Num(90)), f)))));
        return Sub(left, right);
    }

    private static Formula LFormula() => All("f", PS(), Eq(Call("L", F.Id("f")), LBody(F.Id("f"))));

    private static Formula RecurrenceBody(Formula v, Formula n)
    {
        Formula z = CastQ(n);
        Formula result = Mul(Mul(Mul(D(3), Add(z, D(4))), Add(Mul(D(3), z), D(4))), Add(Mul(D(3), z), D(8)));
        result = Mul(result, Call("v", n));
        result = Add(result, Mul(Mul(D(3), Sub(Sub(Sub(Mul(new Formula.Negate(Num(63)), Pow(z, D(3))), Mul(Num(297), Pow(z, D(2)))), Mul(Num(349), z)), Num(60))), V(n, 1)));
        result = Add(result, Mul(Mul(D(3), Sub(Sub(Add(Mul(Num(189), Pow(z, D(3))), Mul(Num(270), Pow(z, D(2)))), Mul(Num(229), z)), Num(140))), V(n, 2)));
        result = Add(result, Mul(Mul(Num(15), Sub(Add(Add(Mul(new Formula.Negate(Num(63)), Pow(z, D(3))), Mul(Num(117), Pow(z, D(2)))), Mul(Num(44), z)), Num(64))), V(n, 3)));
        result = Add(result, Mul(Sub(Add(Sub(Mul(Num(689), Pow(z, D(3))), Mul(Num(5372), Pow(z, D(2)))), Mul(Num(6946), z)), Num(1288)), V(n, 4)));
        result = Add(result, Mul(Mul(Sub(z, D(4)), Sub(Add(Mul(Num(201), Pow(z, D(2))), Mul(Num(2767), z)), Num(3011))), V(n, 5)));
        result = Sub(result, Mul(Mul(Mul(Sub(z, D(5)), Add(Mul(Num(579), z), Num(257))), Sub(z, D(4))), V(n, 6)));
        result = Add(result, Mul(Mul(Mul(Num(229), Sub(z, D(5))), Sub(z, D(6))), Mul(Sub(z, D(4)), V(n, 7))));
        return result;
    }

    private static Formula RecurrenceFormula() =>
        All("v", new Formula.TypeArrow(N(), Q()), All("n", N(), Eq(Call("recurrence", F.Id("v"), F.Id("n")), RecurrenceBody(F.Id("v"), F.Id("n")))));

    private static Formula GeomFormula() =>
        Eq(Call("geom"), Qualified("PowerSeries", "mk", Parenthesized(Seq(D(1), Colon, new Formula.TypeArrow(N(), Q())))));

    private static Formula ParamFormula() => Eq(Call("param"), Pow(Mul(X(), Call("geom")), D(4)));


    private static Formula TransformFormula() => All("f", PS(), Eq(Call("transform", F.Id("f")), Mul(Call("geom"), Qualified("PowerSeries", "subst", Call("param"), F.Id("f")))));



    private static Formula BFormula()
    {
        Formula k = F.Id("k");
        Formula numerator = Mul(D(3), CastQ(Qualified("Nat", "factorial", Add(Mul(D(4), k), D(2)))));
        Formula denominator = Mul(CastQ(Qualified("Nat", "factorial", k)), CastQ(Qualified("Nat", "factorial", Add(Mul(D(3), k), D(3)))));
        return All("k", N(), Eq(Call("b", k), new Formula.Fraction(numerator, denominator)));
    }

    private static Formula CoeffLFormula()
    {
        Formula f = F.Id("f"); var n = F.Id("n");
        Formula function = Lambda("i", N(), Coeff(F.Id("i"), f));
        return All("f", PS(), All("n", N(), Imp(Le(D(7), n), Eq(Coeff(n, Call("L", f)), Call("recurrence", function, n)))));
    }

    private static Formula ForcingZeroFormula()
    {
        Formula n = F.Id("n");
        return All("n", N(), Imp(Le(D(7), n), Eq(Coeff(n, Mul(C(Num(384)), Pow(Sub(D(1), X()), D(3)))), D(0))));
    }

    private static Formula TransformCoefficientsFormula()
    {
        Formula f = F.Id("f"); var n = F.Id("n"); var k = F.Id("k");
        Formula summand = Mul(CastQ(Qualified("Nat", "choose", n, Mul(D(4), k))), Coeff(k, f));
        Formula sum = Seq(new Formula.Subscript(F.Sum, Seq(k, Sp, InMacro, Sp, Qualified("Finset", "range", Add(n, D(1))))), Sp, summand);
        return All("f", PS(), All("n", N(), Eq(Coeff(n, Call("transform", f)), sum)));
    }

    private static Formula CertificateFormula() =>
        Eq(Call("L", Call("transform", Qualified("PowerSeries", "mk", Call("b")))),
            Mul(C(Num(384)), Pow(Sub(D(1), X()), D(3))));
}
