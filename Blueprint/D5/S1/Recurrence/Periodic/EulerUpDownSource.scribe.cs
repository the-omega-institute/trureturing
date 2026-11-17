using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class EulerUpDownSourceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/EulerUpDownSource.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "E is ordinary A000111, defined in the naturals by the source recurrence A second derivative equals A times A first derivative. It differs from the weighted Entringer diagonal. U denotes ordinarySeries, a rational formal power series; derivatives and constants below are formal. The exact signed bridges are proved using complex rescaling and Riccati uniqueness, with no assumed EGF or congruence bridge.", H("The ordinary Euler source carrier"), Blocks(
            Paragraph(Text("E is ordinary A000111, defined in the naturals by the source recurrence A second derivative equals A times A first derivative. It differs from the weighted Entringer diagonal. U denotes ordinarySeries, a rational formal power series; derivatives and constants below are formal. The exact signed bridges are proved using complex rescaling and Riccati uniqueness, with no assumed EGF or congruence bridge.")),
            Node("E", "The offset-zero ordinary recurrence", And(Eqn(E(D(0)),D(1)),And(Eqn(E(D(1)),D(1)),Q("n",Eqn(E(Add(V("n"),D(2))),Sum("i",Add(V("n"),D(1)),Mul(Mul(Call("choose",V("n"),V("i")),E(V("i"))),E(Sub(Add(V("n"),D(1)),V("i"))))))))),
                "All subtraction in indices is natural subtraction; each term uses strictly earlier values.", DescribeRole.Definition),
            Node("ordinarySeries", "The ordinary exponential series", Eqn(V("U"),InfiniteSum("n",Div(Mul(E(V("n")),Pow(V("X"),V("n"))),Call("factorial",V("n"))))),
                "U encodes the natural E coefficients in the rationals. X is the distinguished formal indeterminate.", DescribeRole.Definition),
            Node("source_equation", "The source differential equation", And(Eqn(Co(V("U")),D(1)),And(Eqn(Co(Der(V("U"))),D(1)),Eqn(Der(Der(V("U"))),Mul(V("U"),Der(V("U")))))),
                "Coefficient multiplication recovers the defining positive recurrence exactly.", DescribeRole.Theorem),
            Node("boundary_values", "All small-value boundaries", And(Eqn(E(D(0)),D(1)),And(Eqn(E(D(1)),D(1)),And(Eqn(E(D(2)),D(1)),And(Eqn(E(D(3)),D(2)),Q("k",Imp(LeN(D(4),V("k")),LtN(D(2),E(V("k"))))))))),
                "The source recurrence gives the initial values, and its zeroth summand proves monotonicity.", DescribeRole.Theorem),
            Node("ordinary_riccati", "The secant-plus-tangent equation", Eqn(Mul(D(2),Der(V("U"))),Add(Pow(V("U"),D(2)),D(1))),
                "The derivative of twice U prime minus U squared vanishes. Its constant coefficient is one.", DescribeRole.Theorem),
            Node("signed_even", "Exact even signed correspondence", Q("s",Eqn(E(Mul(D(2),V("s"))),Mul(Pow(MinusOne(),V("s")),A(D(1),Mul(D(2),V("s")))))),
                "Equality is in the integers. The source value at zero is included.", DescribeRole.Theorem),
            Node("signed_odd", "Exact odd signed correspondence", Q("s",Eqn(E(Add(Mul(D(2),V("s")),D(1))),Mul(Pow(MinusOne(),Add(V("s"),D(1))),A(D(0),Add(Mul(D(2),V("s")),D(1)))))),
                "Equality is in the integers. The sign retains the ordinary positive tangent coefficients.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, Formula f, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("eulerupdownsource-" + name.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(f)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string n) => F.Id(n);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Int() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Rat() => Seq(Mathbb, Grp(V("Q")));
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula And(Formula x, Formula y) => Seq(P(x), Sp, Land, Sp, P(y));
    private static Formula Imp(Formula x, Formula y) => Seq(P(x), Sp, Implies, Sp, P(y));
    private static Formula Dvd(Formula x, Formula y) => Seq(x, Sp, Mid, Sp, y);
    private static Formula LtN(Formula x, Formula y) => Seq(x, Sp, Lt, Sp, y);
    private static Formula LeN(Formula x, Formula y) => Seq(x, Sp, Le, Sp, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x,y);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x,y);
    private static Formula Negate(Formula x) => Seq(Minus, P(x));
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, P(body));
    private static Formula Q(string names, Formula body)
    {
        foreach (var n in names.Split(' ').Reverse()) body = All(n, Nat(), body);
        return body;
    }
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [..args]);
    private static Formula Sum(string n, Formula bound, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(V(n), Sp, InMacro, Sp, Call("range",bound))), Sp, P(body));
    private static Formula InfiniteSum(string n, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(V(n), Sp, InMacro, Sp, Nat())), Sp, P(body));
    private static Formula E(Formula n) => Call("E",n);
    private static Formula A(Formula b, Formula n) => Call("A",b,n);
    private static Formula B(Formula b) => Call("F",b);
    private static Formula Der(Formula f) => Call("derivative",f);
    private static Formula Co(Formula f) => Call("constantCoeff",f);
    private static Formula Exp() => Call("exp",Rat());
    private static Formula C(Formula x) => Call("C",x);
    private static Formula Phi(Formula n) => Call("totient",n);
    private static Formula R(Formula q, Formula x) => Call("residue",q,x);
    private static Formula MinusOne() => Negate(D(1));
    private static Formula Shift(Formula k, Formula m, Formula d) => Add(k,Mul(m,Phi(d)));


}
