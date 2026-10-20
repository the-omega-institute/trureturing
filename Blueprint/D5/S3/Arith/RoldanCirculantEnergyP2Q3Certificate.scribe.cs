using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class RoldanCirculantEnergyP2Q3CertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/RoldanCirculantEnergyP2Q3Certificate.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact integer coefficient comparison gives a uniform energy deficit for every mask below 2048 other than 1445 on the nonnegative quadrant.",
        H("The polynomial coefficient certificate for integral circulant energy"), Blocks(
            Node("A", "A: prime-power coefficient data", Disp(Eqn(Parenthesized(Seq(Named("A"), Sp, Colon, Sp, new Formula.TypeArrow(Fin(3), new Formula.TypeArrow(Fin(3), new Formula.TypeArrow(Fin(3), Field("Z")))))), Vec(Vec(Vec(D(0), D(0), D(0)), Vec(new Formula.Negate(D(1)), D(0), D(0)), Vec(D(1), D(0), D(0))), Vec(Vec(new Formula.Negate(D(3)), new Formula.Negate(D(1)), D(0)), Vec(D(2), D(1), D(0)), Vec(D(1), D(0), D(0))), Vec(Vec(D(6), D(5), D(1)), Vec(D(2), D(1), D(0)), Vec(D(1), D(0), D(0)))))),
                "The entries are integer coefficient vectors in increasing exponent order. Rows index the gcd exponent and columns index the divisor exponent.", DescribeRole.Definition),
            Node("B", "B: prime-power coefficient data", Disp(Eqn(Parenthesized(Seq(Named("B"), Sp, Colon, Sp, new Formula.TypeArrow(Fin(4), new Formula.TypeArrow(Fin(4), new Formula.TypeArrow(Fin(4), Field("Z")))))), Vec(Vec(Vec(D(0), D(0), D(0), D(0)), Vec(D(0), D(0), D(0), D(0)), Vec(new Formula.Negate(D(1)), D(0), D(0), D(0)), Vec(D(1), D(0), D(0), D(0))), Vec(Vec(D(0), D(0), D(0), D(0)), Vec(new Formula.Negate(D(3)), new Formula.Negate(D(1)), D(0), D(0)), Vec(D(2), D(1), D(0), D(0)), Vec(D(1), D(0), D(0), D(0))), Vec(Vec(new Formula.Negate(D(9)), new Formula.Negate(D(6)), new Formula.Negate(D(1)), D(0)), Vec(D(6), D(5), D(1), D(0)), Vec(D(2), D(1), D(0), D(0)), Vec(D(1), D(0), D(0), D(0))), Vec(Vec(D(1, 8), D(2, 1), D(8), D(1)), Vec(D(6), D(5), D(1), D(0)), Vec(D(2), D(1), D(0), D(0)), Vec(D(1), D(0), D(0), D(0)))))),
                "The entries are integer coefficient vectors in increasing exponent order. Rows index the gcd exponent and columns index the divisor exponent.", DescribeRole.Definition),
            Node("wA", "wA: prime-power coefficient data", Disp(Eqn(Parenthesized(Seq(Named("wA"), Sp, Colon, Sp, new Formula.TypeArrow(Fin(3), new Formula.TypeArrow(Fin(3), Field("Z"))))), Vec(Vec(D(6), D(5), D(1)), Vec(D(2), D(1), D(0)), Vec(D(1), D(0), D(0))))),
                "The entries are integer coefficient vectors in increasing exponent order. Rows index the gcd exponent; columns give coefficients in increasing exponent order.", DescribeRole.Definition),
            Node("wB", "wB: prime-power coefficient data", Disp(Eqn(Parenthesized(Seq(Named("wB"), Sp, Colon, Sp, new Formula.TypeArrow(Fin(4), new Formula.TypeArrow(Fin(4), Field("Z"))))), Vec(Vec(D(1, 8), D(2, 1), D(8), D(1)), Vec(D(6), D(5), D(1), D(0)), Vec(D(2), D(1), D(0), D(0)), Vec(D(1), D(0), D(0), D(0))))),
                "The entries are integer coefficient vectors in increasing exponent order. Rows index the gcd exponent; columns give coefficients in increasing exponent order.", DescribeRole.Definition),
            Node("switch", "The divisor-mask bit", SwitchFormula(),
                "The (2,3) entry is zero. Every other entry is the bit of mask at position 4c + f, interpreted as an integer.", DescribeRole.Definition),
            Node("lcoeff", "Spectral polynomial coefficients", LinearFormula(),
                "The spectral coefficient is the sum over the two divisor exponents of the product of the two prime-power table entries and the selected bit.", DescribeRole.Definition),
            Node("star", "The maximizing mask", Disp(Eqn(Named("star"), D(1,4,4,5))),
                "The eleven low bits encode the six divisors of Dstar.", DescribeRole.Definition),
            Node("eval", "Evaluation of a rectangular integer coefficient array", EvalFormula(),
                "An array is evaluated by the finite double sum of its integer coefficients cast to the reals, multiplied by the corresponding powers of u and v.", DescribeRole.Definition),
            Node("evalW", "Evaluation of a weight polynomial", WeightFormula(),
                "The weight polynomial is the finite sum of its integer coefficients cast into a ring, times successive powers of x.", DescribeRole.Definition),
            Node("modelEnergy", "The weighted absolute spectral sum", EnergyFormula(),
                "There are three exponents for p and four for q. Each spectral polynomial contributes its absolute value with the product of the two totient weight polynomials.", DescribeRole.Definition),
            Node("model_gap", "A uniform gap of at least 96", GapFormula(),
                "For every mask below 2048 other than 1445 and all nonnegative u and v, the maximizing mask exceeds that mask's weighted absolute spectral sum by at least 96. The proof compares integer coefficient arrays exactly and uses the triangle inequality for polynomial evaluation. At the maximizing mask every spectral polynomial has coefficients of one sign, so the majorant is attained.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("roldan-certificate-" + declaration.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Field(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula FinN(Formula n) => Call("Fin", n);
    private static Formula Vec(params Formula[] xs)
    {
        var items = new List<Formula> { Bang, OpenBracket };
        for (var i = 0; i < xs.Length; i++)
        {
            if (i != 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(xs[i]);
        }
        items.Add(CloseBracket);
        return Seq([.. items]);
    }
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(Sum,
        Underscore, Grp(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula IntCast(Formula x) => Parenthesized(Seq(x, Sp, Colon, Sp, Field("R")));
    private static Formula Pow(Formula x, Formula k) => new Formula.Power(Parenthesized(x), k);

    private static Formula SwitchFormula()
    {
        Formula mask = F.Id("mask"), c = F.Id("c"), f = F.Id("f");
        Formula corner = And(Eqn(Val(c), D(2)), Eqn(Val(f), D(3)));
        Formula bit = App(Seq(Named("Nat"), Dot, Named("testBit")), mask, Add(Mul(D(4), Val(c)), Val(f)));
        Formula value = Seq(Named("if"), Sp, Parenthesized(corner), Sp, Named("then"), Sp, D(0), Sp,
            Named("else"), Sp, Named("if"), Sp, bit, Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(0));
        return Disp(All("mask", Field("N"), All("c", Fin(3), All("f", Fin(4), Eqn(App(Named("switch"), mask, c, f), value)))));
    }

    private static Formula LinearFormula()
    {
        Formula mask = F.Id("mask"), a = F.Id("a"), b = F.Id("b"), i = F.Id("i"), j = F.Id("j"), c = F.Id("c"), f = F.Id("f");
        Formula summand = Mul(Mul(App(Named("A"), a, c, i), App(Named("B"), b, f, j)), App(Named("switch"), mask, c, f));
        return Disp(All("mask", Field("N"), All("a", Fin(3), All("b", Fin(4), All("i", Fin(3), All("j", Fin(4),
            Eqn(App(Named("lcoeff"), mask, a, b, i, j), SumOver("c", Fin(3), SumOver("f", Fin(4), summand)))))))));
    }

    private static Formula EvalFormula()
    {
        Formula r = F.Id("r"), s = F.Id("s"), c = F.Id("C"), u = F.Id("u"), v = F.Id("v"), i = F.Id("i"), j = F.Id("j");
        Formula type = new Formula.TypeArrow(FinN(r), new Formula.TypeArrow(FinN(s), Field("Z")));
        Formula summand = Mul(Mul(IntCast(App(c, i, j)), Pow(u, Val(i))), Pow(v, Val(j)));
        return Disp(All("r", Field("N"), All("s", Field("N"), All("C", type, All("u", Field("R"), All("v", Field("R"),
            Eqn(App(Named("eval"), c, u, v), SumOver("i", FinN(r), SumOver("j", FinN(s), summand)))))))));
    }

    private static Formula WeightFormula()
    {
        Formula r = F.Id("r"), c = F.Id("C"), x = F.Id("x"), i = F.Id("i"), ring = F.Id("R");
        Formula poly = App(Seq(Named("Polynomial"), Dot, Named("ofFn")), r, c);
        Formula mapped = App(Seq(Named("Polynomial"), Dot, Named("map")),
            App(Seq(Named("Int"), Dot, Named("castRingHom")), ring), poly);
        Formula body = All("r", Field("N"), All("C", new Formula.TypeArrow(FinN(r), Field("Z")), All("x", ring,
            Eqn(App(Named("evalW"), c, x), App(Seq(Named("Polynomial"), Dot, Named("eval")), x, mapped)))));
        return Disp(All("R", Named("Type"), Seq(OpenBracket, Call("Ring", ring), CloseBracket, Sp, body)));
    }

    private static Formula EnergyFormula()
    {
        Formula mask = F.Id("mask"), u = F.Id("u"), v = F.Id("v"), a = F.Id("a"), b = F.Id("b");
        Formula weights = Mul(App(Named("evalW"), App(Named("wA"), a), u), App(Named("evalW"), App(Named("wB"), b), v));
        Formula eigenvalue = App(Named("eval"), App(Named("lcoeff"), mask, a, b), u, v);
        return Disp(All("mask", Field("N"), All("u", Field("R"), All("v", Field("R"), Eqn(App(Named("modelEnergy"), mask, u, v),
            SumOver("a", Fin(3), SumOver("b", Fin(4), Mul(weights, new Formula.Absolute(eigenvalue)))))))));
    }

    private static Formula GapFormula()
    {
        Formula mask = F.Id("mask"), u = F.Id("u"), v = F.Id("v"), star = Named("star");
        Formula gap = Sub(App(Named("modelEnergy"), star, u, v), App(Named("modelEnergy"), Val(mask), u, v));
        return Disp(All("mask", Call("Fin", D(2,0,4,8)), Imp(new Formula.Not(Parenthesized(Eqn(Val(mask), star))),
            All("u", Field("R"), All("v", Field("R"), Imp(Le(D(0), u), Imp(Le(D(0), v), Le(D(9,6), gap))))))));
    }
}
