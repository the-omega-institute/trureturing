using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaLegendreCentralBinomialTransformDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integer binomial-square transform and its first moment determine two coefficient residue laws.",
        H("The integer central-binomial transform"),
        Blocks(
            Node("Q", "The finite binomial-square polynomial",
                Generic(All("a", X("R"), All("n", N(), Eqn(Call("Q", X("a"), X("n")), QBody())))),
                "This polynomial has coefficient choose(n,k) squared times a to the k.", DescribeRole.Definition),
            Node("summand", "A parameterized summand",
                Generic(All("c", X("R"), All("a", X("R"), All("b", X("R"), All("n", N(), Eqn(Call("summand", X("c"), X("a"), X("b"), X("n")), Mul(Pow(Var(), X("n")), DenBody(), Call("Q", X("a"), X("n")), Call("Q", X("b"), X("n"))))))))),
                "The initial power of X makes the n-th summand vanish below degree n.", DescribeRole.Definition),
            Node("weighted", "The coefficientwise weighted series",
                Generic(All("w", Seq(N(), Sp, To, Sp, X("R")), Parameters(Eqn(Call("weighted", X("w"), X("c"), X("a"), X("b")), SeriesBody(true))))),
                "Each coefficient is a finite sum, weighted by the value w(n).", DescribeRole.Definition),
            Node("Q_coeff", "Every polynomial coefficient",
                Generic(All("a", X("R"), All("n", N(), All("k", N(), Eqn(Coeff(X("k"), Call("Q", X("a"), X("n"))), Mul(Pow(Cast(Choose(X("n"), X("k")), X("R")), D(2)), Pow(X("a"), X("k")))))))),
                "The formula also covers k greater than n, where the binomial coefficient is zero.", DescribeRole.Theorem),
            Node("Q_zero", "The zero parameter",
                Generic(All("n", N(), Eqn(Call("Q", Cast(D(0), X("R")), X("n")), D(1)))),
                "At parameter zero the binomial-square polynomial is one.", DescribeRole.Theorem),
            Node("term_low", "The lower coefficients vanish",
                Generic(Parameters(All("n", N(), All("k", N(), ImplicationBody(Seq(X("k"), Lt, X("n")), Eqn(Coeff(X("k"), Call("summand", X("c"), X("a"), X("b"), X("n"))), D(0))))))),
                "Only indices up to the desired coefficient can contribute.", DescribeRole.Theorem),
            Node("map_series", "Changing the coefficient ring",
                TwoRings(All("hom", Seq(X("R"), Sp, To, Seq(Caret, Grp(Seq(Plus, Star))), Sp, X("S")), Parameters(Eqn(Map(Call("weighted", App(Qualified("Function", "const"), N(), D(1)), X("c"), X("a"), X("b")), X("hom")), Call("weighted", App(Qualified("Function", "const"), N(), D(1)), App(X("hom"), X("c")), App(X("hom"), X("a")), App(X("hom"), X("b"))))))),
                "Here hom is a ring homomorphism R to S. Mapping the finite polynomials and the constant-one inverse commutes with every coefficient sum.", DescribeRole.Theorem),
            Node("map_weighted", "Changing a weighted coefficient ring",
                TwoRings(All("hom", Seq(X("R"), Sp, To, Seq(Caret, Grp(Seq(Plus, Star))), Sp, X("S")), All("w", Seq(N(), Sp, To, Sp, X("R")), Parameters(Eqn(Map(Call("weighted", X("w"), X("c"), X("a"), X("b")), X("hom")), Call("weighted", LambdaBody("n", N(), App(X("hom"), App(X("w"), X("n")))), App(X("hom"), X("c")), App(X("hom"), X("a")), App(X("hom"), X("b")))))))),
                "Here hom is a ring homomorphism R to S. The weights are mapped along with the series coefficients.", DescribeRole.Theorem),
            Node("rational_den", "The rational inverse",
                All("c", Rat(), All("n", N(), Eqn(DenBody(), Pow(Cast(Pow(Sub(D(1), Mul(Constant(X("c")), Var())), Add(Mul(D(2), X("n")), D(1))), PSeries(Rat())), Seq(Minus, D(1)))))),
                "Over the rationals the constant-one unit inverse equals the ordinary power-series inverse.", DescribeRole.Theorem),
            Node("square_binomial_sum", "The binomial-square transform",
                All("n", N(), All("t", N(), Eqn(SumRange("k", Add(X("n"), D(1)), Mul(Pow(Cast(Choose(X("n"), X("k")), Z()), D(2)), Cast(Choose(Sub(Add(Mul(D(2), X("n")), X("t")), X("k")), Mul(D(2), X("n"))), Z()))), Pow(Cast(Choose(Add(X("n"), X("t")), X("n")), Z()), D(2))))),
                "A denominator-free telescoping certificate gives a recurrence in t. The initial finite sum is one; induction and the choose recurrence give the squared binomial coefficient. Natural subtraction truncates at zero.", DescribeRole.Theorem),
            Node("R_coeff", "The exact alternating transform",
                All("N", N(), Eqn(Coeff(X("N"), Reduced()), If(Seq(D(2), Mid, Sp, X("N")), Mul(Pow(Seq(Minus, D(1)), DivTwo()), Cast(Choose(X("N"), DivTwo()), Z())), D(0)))),
                "Even coefficients are signed central binomial coefficients and odd coefficients vanish. Nat.div denotes natural integer division.", DescribeRole.Theorem),
            Node("T_mod_two", "The first moment modulo two",
                Eqn(Map(Call("weighted", LambdaBody("n", N(), Cast(X("n"), Z())), Seq(Minus, D(1)), Seq(Minus, D(1)), D(0)), IntHom(Zmod(2))), Cast(Var(), PSeries(Zmod(2)))),
                "The derivative of the alternating convolution computes the first moment. Its reduction modulo two is exactly X.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula X(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Pow(Formula value, Formula power) =>
        new Formula.Power(Parenthesized(value), power);
    private static Formula Mul(params Formula[] values) =>
        values.Aggregate((a, b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b));
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, X(name), Colon, type, Comma, Sp, body);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, type));
    private static Formula N() => Seq(Mathbb, Grp(X("N")));
    private static Formula Z() => Seq(Mathbb, Grp(X("Z")));
    private static Formula Rat() => Seq(Mathbb, Grp(X("Q")));
    private static Formula Choose(Formula n, Formula k) => App(Qualified("Nat", "choose"), n, k);
    private static Formula Coeff(Formula n, Formula series) => App(Qualified("PowerSeries", "coeff"), n, series);
    private static Formula Constant(Formula value) => App(Qualified("PowerSeries", "C"), value);
    private static Formula PSeries(Formula type) => Call("PowerSeries", type);
    private static Formula Var() => Qualified("PowerSeries", "X");
    private static Formula SumRange(string name, Formula bound, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(X(name), InMacro, Sp, App(Qualified("Finset", "range"), bound))), body);
    private static Formula LambdaBody(string name, Formula type, Formula body) =>
        Seq(Operatorname, Grp(X("fun")), Sp, Parenthesized(Seq(X(name), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula Mk(Formula body) => App(Qualified("PowerSeries", "mk"), body);
    private static Formula Map(Formula series, Formula hom) => App(Qualified("PowerSeries", "map"), hom, series);
    private static Formula IntHom(Formula type) => App(Qualified("Int", "castRingHom"), type);
    private static Formula Zmod(byte modulus) => Call("ZMod", D(modulus));
    private static Formula Generic(Formula body) => All("R", X("Type"),
        Seq(OpenBracket, Call("CommRing", X("R")), CloseBracket, Sp, body));
    private static Formula TwoRings(Formula body) => All("R", X("Type"), All("S", X("Type"),
        Seq(OpenBracket, Call("CommRing", X("R")), CloseBracket, Sp,
            OpenBracket, Call("CommRing", X("S")), CloseBracket, Sp, body)));
    private static Formula Parameters(Formula body) => All("c", X("R"), All("a", X("R"), All("b", X("R"), body)));
    private static Formula DenBody() => App(Qualified("PowerSeries", "invOfUnit"), Pow(Sub(D(1), Mul(Constant(X("c")), Var())), Add(Mul(D(2), X("n")), D(1))), D(1));
    private static Formula QBody() => SumRange("k", Add(X("n"), D(1)),
        Mul(Constant(Mul(Pow(Cast(Choose(X("n"), X("k")), X("R")), D(2)), Pow(X("a"), X("k")))), Pow(Var(), X("k"))));
    private static Formula SeriesBody(bool weighted) => Mk(LambdaBody("m", N(),
        Coeff(X("m"), SumRange("n", Add(X("m"), D(1)), weighted
            ? Mul(Constant(App(X("w"), X("n"))), Call("summand", X("c"), X("a"), X("b"), X("n")))
            : Call("summand", X("c"), X("a"), X("b"), X("n"))))));
    private static Formula ImplicationBody(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Seq(Operatorname, Grp(X("if")), Sp, Parenthesized(condition), Sp,
            Operatorname, Grp(X("then")), Sp, yes, Sp, Operatorname, Grp(X("else")), Sp, no);
    private static Formula Reduced() => Call("weighted", App(Qualified("Function", "const"), N(), D(1)), Cast(Seq(Minus, D(1)), Z()), Seq(Minus, D(1)), D(0));
    private static Formula DivTwo() => App(Qualified("Nat", "div"), X("N"), D(2));
}
