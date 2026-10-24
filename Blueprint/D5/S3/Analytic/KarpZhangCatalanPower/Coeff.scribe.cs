using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangCatalanPower;

internal sealed class CoeffDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rising-factorial coefficients of Catalan powers and their degree-parameter ordering.",
        H("Catalan power coefficients"), Blocks(
            Node("a", "The coefficient in formula (15)", DescribeRole.Definition,
                All("n", Nat(), All("t", Real(), Eq(A(X("n"), X("t")),
                    Div(Poch(Mul(D(2), X("n")), X("t")),
                        Mul(Poch(X("n"), Add(X("t"), D(1))), Fact(X("n"))))))),
                "The coefficient is the literal quotient (t) at rising order 2n divided by (t+1) at rising order n and n factorial. Real division is total. Its polynomial continuation agrees with this quotient whenever t is greater than minus one, including every nonnegative parameter."),
            Node("coeffPoly", "The polynomial continuation", DescribeRole.Definition,
                Seq(Eq(Call("coeffPoly", D(0)), D(1)), Comma, Quad,
                    All("n", Nat(), Eq(Call("coeffPoly", Add(X("n"), D(1))),
                        Seq(Call("C", new Formula.Power(Fact(Add(X("n"), D(1))), Seq(Minus, D(1)))),
                            Sp, Times, Sp, X("X"), Sp, Times, Sp,
                            App(Q("Polynomial", "comp"), Call("ascPochhammer", Real(), X("n")),
                                Par(Add(X("X"), Call("C", Add(X("n"), D(2)))))))))),
                "The degree-zero polynomial is one. At degree n+1 the polynomial is X times the rising Pochhammer polynomial of order n evaluated at X+n+2, divided by (n+1) factorial."),
            Node("coeffPoly_succ_eval", "Evaluation of the continuation", DescribeRole.Theorem,
                All("n", Nat(), All("t", Real(), Eq(Eval(Call("coeffPoly", Add(X("n"), D(1))), X("t")),
                    Div(Mul(X("t"), Poch(X("n"), Add(Add(X("t"), X("n")), D(2)))),
                        Fact(Add(X("n"), D(1))))))),
                "Polynomial evaluation gives the product t times the rising factorial at t+n+2. This form is used to cancel the denominator of the original quotient."),
            Node("a_eq_polynomial", "Cancellation away from the poles", DescribeRole.Theorem,
                All("n", Nat(), All("t", Real(), Imp(Lt(Seq(Minus, D(1)), X("t")),
                    Eq(A(X("n"), X("t")), Eval(Call("coeffPoly", X("n")), X("t")))))),
                "For t greater than minus one, all factors of (t+1) at rising order n are positive. Pochhammer multiplication splits off these factors and cancels them, including t=0."),
            Node("a_product", "The finite product", DescribeRole.Theorem,
                All("n", Nat(), All("t", Real(), Imp(Le(D(1), X("n")),
                    Imp(Lt(Seq(Minus, D(1)), X("t")),
                        Eq(A(X("n"), X("t")), Mul(Div(X("t"), Fact(X("n"))),
                            Seq(F.Prod, Underscore, Grp(Seq(X("r"), InMacro,
                                App(Q("Finset", "Ico"), Add(X("n"), D(1)), Mul(D(2), X("n"))))),
                                Sp, Par(Add(X("t"), X("r")))))))))),
                "For n at least one the remaining product runs from n+1 through 2n-1. Finset.Ico excludes its upper endpoint. This representation proves positivity."),
            Node("a_pos", "Positivity", DescribeRole.Theorem,
                All("n", Nat(), All("t", Real(), Imp(Lt(D(0), X("t")), Lt(D(0), A(X("n"), X("t")))))),
                "Every coefficient is positive at a positive parameter. Degree zero is one; in positive degree each factor in the finite product is positive."),
            Node("a_zero_parameter", "The zero parameter", DescribeRole.Theorem,
                All("n", Nat(), Imp(Lt(D(0), X("n")), Eq(A(X("n"), D(0)), D(0)))),
                "At parameter zero every positive-degree coefficient vanishes. This supplies the boundary case of the interval tail inequality."),
            Node("a_nonneg", "Nonnegative parameters", DescribeRole.Theorem,
                All("n", Nat(), All("t", Real(), Imp(Le(D(0), X("t")), Le(D(0), A(X("n"), X("t")))))),
                "The positive-parameter result and the value at zero show nonnegativity on the entire closed nonnegative half-line."),
            Node("adjacent_ratio", "Adjacent coefficient ratios", DescribeRole.Theorem,
                All("n", Nat(), All("t", Real(), Imp(Lt(D(0), X("t")),
                    Eq(A(Add(X("n"), D(1)), X("t")), Mul(A(X("n"), X("t")),
                        Div(Mul(Add(X("t"), Mul(D(2), X("n"))),
                                Add(Add(X("t"), Mul(D(2), X("n"))), D(1))),
                            Mul(Add(Add(X("t"), X("n")), D(1)), Add(X("n"), D(1))))))))),
                "The ratio a(n+1,t)/a(n,t), multiplied by n+1, is (t+2n)(t+2n+1)/(t+n+1), including n=0. Cross multiplication at two positive parameters shows that this ratio strictly increases with the parameter."),
            Node("tp2", "Strict total positivity of order two", DescribeRole.Theorem,
                TP2(false),
                "If i is less than l and 0<u<v, the cross product a(i,u)a(l,v) exceeds a(l,u)a(i,v). The adjacent ratio comparison propagates by induction through every degree gap. The interval derivative uses this strict sign after reflection."),
            Node("tp2_le", "The weak cross-product order", DescribeRole.Theorem,
                TP2(true),
                "For 0<u≤v the same determinant is nonnegative. At equal parameters it is zero; otherwise strict total positivity applies."),
            IndexSection.Create())));

    private static DocumentBlock Node(string name, string title, DescribeRole role, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("kz42-coeff-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangCatalanPower/Coeff." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula X(string name) => F.Id(name);
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(Seq(X(owner), Dot, X(name))));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Par(Seq(X(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Fact(Formula n) => Seq(Par(n), Bang);
    private static Formula Eval(Formula p, Formula t) => App(Q("Polynomial", "eval"), t, p);
    private static Formula Poch(Formula n, Formula t) => Eval(Call("ascPochhammer", Real(), n), t);
    private static Formula A(Formula n, Formula t) => Call("a", n, t);
    private static Formula TP2(bool weak) => All("u", Real(), All("v", Real(),
        All("i", Nat(), All("l", Nat(), Imp(Lt(D(0), X("u")),
            Imp(weak ? Le(X("u"), X("v")) : Lt(X("u"), X("v")),
                Imp(Lt(X("i"), X("l")), weak
                    ? Le(Mul(A(X("l"), X("u")), A(X("i"), X("v"))), Mul(A(X("i"), X("u")), A(X("l"), X("v"))))
                    : Lt(Mul(A(X("l"), X("u")), A(X("i"), X("v"))), Mul(A(X("i"), X("u")), A(X("l"), X("v")))))))))));
}

internal static class IndexSection
{
    private const string Prefix = "D5/S3/Analytic/KarpZhangCatalanPower/Coeff.";

    public static DocumentBlock Create() => new DocumentBlock.Section(H("Convolution and differentiation of Catalan-power coefficients"), Blocks(
            Paragraph(Text("Polynomial.eval t (coeffPoly n) evaluates the coefficient polynomial at t. The coefficient a(n,t) is the literal rising-factorial quotient in formula (15). The two agree for t greater than minus one. The generator b(j) is the derivative of a(j,t) at t=0. All sums are finite; natural subtraction occurs only with the subtracted index bounded by the degree.")),
            Node("index_polynomial", "The polynomial convolution law", DescribeRole.Theorem,
                All("s", Real(), All("t", Real(), All("m", Nat(),
                    Eq(SumRange("k", Add(X("m"), D(1)), Mul(Eval(X("k"), X("s")),
                            Eval(Sub(X("m"), X("k")), X("t")))),
                        Eval(X("m"), Add(X("s"), X("t"))))))),
                "The identity holds for arbitrary real s and t, including the roots of denominator factors in the original quotient. The existing Catalan Lagrange coefficient transform identifies evaluation of coeffPoly n at a natural t with the coefficient of C to the natural power t. Multiplication of natural powers supplies convolution on the natural grid. Polynomial uniqueness extends first in s and then in t. The supplied Lagrange transform is reused directly; no real formal power is assumed."),
            Node("index_law", "The index law for the original coefficients", DescribeRole.Theorem,
                All("s", Real(), All("t", Real(), All("m", Nat(),
                    Imp(Le(D(0), X("s")), Imp(Le(D(0), X("t")),
                        Eq(SumRange("k", Add(X("m"), D(1)), Mul(A(X("k"), X("s")),
                                A(Sub(X("m"), X("k")), X("t")))),
                            A(X("m"), Add(X("s"), X("t"))))))))),
                "For nonnegative s and t, every denominator factor in formula (15) is positive. Substitution of the polynomial form into the all-real polynomial convolution proves the index law. Both zero parameters are included. The literal totalized quotient is not asserted to satisfy the law at negative poles."),
            Node("b", "The infinitesimal generator", DescribeRole.Definition,
                All("j", Nat(), Eq(Call("b", X("j")),
                    Call("deriv", Call("a", X("j")), D(0)))),
                "The generator coefficient is the derivative at zero of the original coefficient function. Its polynomial representation is valid on a neighborhood of zero."),
            Node("b_eq_centralBinom", "The generator in closed form", DescribeRole.Theorem,
                All("j", Nat(), Imp(Le(D(1), X("j")),
                    Eq(Call("b", X("j")), Div(App(Q("Nat", "choose"),
                        Par(Mul(D(2), X("j"))), X("j")), Mul(D(2), X("j")))))),
                "For every positive natural j, differentiation at zero leaves the product from j+1 through 2j-1 divided by j factorial. Rising-factorial and binomial identities convert it to Nat.choose (2j) j divided by 2j. The division is real division and 2j is positive."),
            Node("b_pos", "Every positive-degree generator coefficient is positive", DescribeRole.Theorem,
                All("j", Nat(), Imp(Le(D(1), X("j")), Lt(D(0), Call("b", X("j"))))),
                "The central binomial coefficient and the denominator 2j are positive. This positivity weights each reflected determinant in the interval-slice derivative."),
            Node("hasDerivAt_a", "Differentiation is convolution with the generator", DescribeRole.Theorem,
                All("n", Nat(), All("t", Real(), Imp(Le(D(0), X("t")),
                    Call("HasDerivAt", Call("a", X("n")),
                        SumIcc("j", D(1), X("n"), Mul(Call("b", X("j")),
                            A(Sub(X("n"), X("j")), X("t")))), X("t"))))),
                "At every nonnegative t, the derivative of a(n,t) is the sum of b(j)a(n-j,t), with j from one through n. Differentiate the polynomial index law in its first parameter at zero. The derivative of the degree-zero polynomial is zero, so that summand drops out. Equality with the literal quotient on the open interval t greater than minus one supplies a two-sided derivative, also at t=0. The degree-zero sum is empty.")));

    private static DocumentBlock Node(string name, string title, DescribeRole role, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("kz42-index-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
    private static Formula X(string name) => F.Id(name);
    private static Formula Real() => Seq(Mathbb, Grp(X("R")));
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(Seq(X(owner), Dot, X(name))));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(X(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Eval(Formula degree, Formula argument) =>
        App(Q("Polynomial", "eval"), Par(argument), Call("coeffPoly", degree));
    private static Formula A(Formula degree, Formula argument) => Call("a", degree, argument);
    private static Formula SumRange(string index, Formula upper, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(X(index), InMacro,
            App(Q("Finset", "range"), Par(upper)))), Sp, body);
    private static Formula SumIcc(string index, Formula lower, Formula upper, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(X(index), InMacro,
            App(Q("Finset", "Icc"), lower, upper))), Sp, body);
}
